/**
 * @file evaluation.cpp
 * @brief Expression evaluation implementation for the Scheme interpreter
 */

#include "value.hpp"
#include "expr.hpp"
#include "RE.hpp"
#include "syntax.hpp"
#include <cstring>
#include <vector>
#include <map>
#include <climits>
#include <cstdlib>

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

// Global environment pointer for lexical closure fallback (for mutually recursive defines)
Assoc *globalEnvPtr = nullptr;

// gcd helper
static int mygcd(int a, int b) {
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b != 0) {
        int t = b;
        b = a % b;
        a = t;
    }
    return a;
}

// Build a numeric value from numerator/denominator - Integer if denominator=1
static Value makeNumeric(int num, int den) {
    if (den == 0) throw RuntimeError("Division by zero");
    if (den < 0) { num = -num; den = -den; }
    int g = mygcd(num, den);
    if (g == 0) g = 1;
    num /= g;
    den /= g;
    if (den == 1) return IntegerV(num);
    return RationalV(num, den);
}

// Get numerator/denominator from a numeric value
static bool getNumeric(const Value &v, int &num, int &den) {
    if (v->v_type == V_INT) {
        num = dynamic_cast<Integer*>(v.get())->n;
        den = 1;
        return true;
    }
    if (v->v_type == V_RATIONAL) {
        Rational *r = dynamic_cast<Rational*>(v.get());
        num = r->numerator;
        den = r->denominator;
        return true;
    }
    return false;
}

Value Fixnum::eval(Assoc &e) { return IntegerV(n); }
Value RationalNum::eval(Assoc &e) { return makeNumeric(numerator, denominator); }
Value StringExpr::eval(Assoc &e) { return StringV(s); }
Value True::eval(Assoc &e) { return BooleanV(true); }
Value False::eval(Assoc &e) { return BooleanV(false); }
Value MakeVoid::eval(Assoc &e) { return VoidV(); }
Value Exit::eval(Assoc &e) { return TerminateV(); }

Value Unary::eval(Assoc &e) { return evalRator(rand->eval(e)); }
Value Binary::eval(Assoc &e) { return evalRator(rand1->eval(e), rand2->eval(e)); }
Value Variadic::eval(Assoc &e) {
    std::vector<Value> args;
    for (auto &r : rands) args.push_back(r->eval(e));
    return evalRator(args);
}

Value Var::eval(Assoc &e) {
    Value matched_value = find(x, e);
    // Also check global environment as a fallback for mutual recursion
    if (matched_value.get() == nullptr && globalEnvPtr != nullptr) {
        matched_value = find(x, *globalEnvPtr);
    }
    if (matched_value.get() == nullptr) {
        if (primitives.count(x)) {
            static std::map<ExprType, std::pair<Expr, std::vector<std::string>>> primitive_map = {
                {E_VOID,     {new MakeVoid(), {}}},
                {E_EXIT,     {new Exit(), {}}},
                {E_BOOLQ,    {new IsBoolean(new Var("parm")), {"parm"}}},
                {E_INTQ,     {new IsFixnum(new Var("parm")), {"parm"}}},
                {E_NULLQ,    {new IsNull(new Var("parm")), {"parm"}}},
                {E_PAIRQ,    {new IsPair(new Var("parm")), {"parm"}}},
                {E_PROCQ,    {new IsProcedure(new Var("parm")), {"parm"}}},
                {E_SYMBOLQ,  {new IsSymbol(new Var("parm")), {"parm"}}},
                {E_STRINGQ,  {new IsString(new Var("parm")), {"parm"}}},
                {E_DISPLAY,  {new Display(new Var("parm")), {"parm"}}},
                {E_PLUS,     {new PlusVar({}),  {}}},
                {E_MINUS,    {new MinusVar({}), {}}},
                {E_MUL,      {new MultVar({}),  {}}},
                {E_DIV,      {new DivVar({}),   {}}},
                {E_MODULO,   {new Modulo(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                {E_EXPT,     {new Expt(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                {E_EQQ,      {new EqualVar({}), {}}},
            };
            auto it = primitive_map.find(primitives[x]);
            if (it != primitive_map.end()) {
                Assoc env = empty();
                return ProcedureV(it->second.second, it->second.first, env);
            }
            // For other primitives (car, cdr, cons, list, set-car!, set-cdr!, not, and, or, list?),
            // build a closure on demand.
            ExprType t = primitives[x];
            Assoc env = empty();
            switch (t) {
                case E_CAR: {
                    std::vector<std::string> p = {"x"};
                    return ProcedureV(p, Expr(new Car(new Var("x"))), env);
                }
                case E_CDR: {
                    std::vector<std::string> p = {"x"};
                    return ProcedureV(p, Expr(new Cdr(new Var("x"))), env);
                }
                case E_CONS: {
                    std::vector<std::string> p = {"a","b"};
                    return ProcedureV(p, Expr(new Cons(new Var("a"), new Var("b"))), env);
                }
                case E_LIST: {
                    std::vector<std::string> p;
                    return ProcedureV(p, Expr(new ListFunc({})), env);
                }
                case E_SETCAR: {
                    std::vector<std::string> p = {"a","b"};
                    return ProcedureV(p, Expr(new SetCar(new Var("a"), new Var("b"))), env);
                }
                case E_SETCDR: {
                    std::vector<std::string> p = {"a","b"};
                    return ProcedureV(p, Expr(new SetCdr(new Var("a"), new Var("b"))), env);
                }
                case E_NOT: {
                    std::vector<std::string> p = {"x"};
                    return ProcedureV(p, Expr(new Not(new Var("x"))), env);
                }
                case E_AND: {
                    std::vector<std::string> p;
                    return ProcedureV(p, Expr(new AndVar({})), env);
                }
                case E_OR: {
                    std::vector<std::string> p;
                    return ProcedureV(p, Expr(new OrVar({})), env);
                }
                case E_LISTQ: {
                    std::vector<std::string> p = {"x"};
                    return ProcedureV(p, Expr(new IsList(new Var("x"))), env);
                }
                case E_EQ: {
                    std::vector<std::string> p;
                    return ProcedureV(p, Expr(new EqualVar({})), env);
                }
                case E_LT: {
                    std::vector<std::string> p;
                    return ProcedureV(p, Expr(new LessVar({})), env);
                }
                case E_LE: {
                    std::vector<std::string> p;
                    return ProcedureV(p, Expr(new LessEqVar({})), env);
                }
                case E_GE: {
                    std::vector<std::string> p;
                    return ProcedureV(p, Expr(new GreaterEqVar({})), env);
                }
                case E_GT: {
                    std::vector<std::string> p;
                    return ProcedureV(p, Expr(new GreaterVar({})), env);
                }
                default: break;
            }
        }
        throw RuntimeError("Variable not found: " + x);
    }
    return matched_value;
}

Value Plus::evalRator(const Value &rand1, const Value &rand2) {
    int n1, d1, n2, d2;
    if (!getNumeric(rand1, n1, d1) || !getNumeric(rand2, n2, d2))
        throw RuntimeError("+: non-numeric argument");
    // n1/d1 + n2/d2 = (n1*d2 + n2*d1) / (d1*d2)
    return makeNumeric(n1 * d2 + n2 * d1, d1 * d2);
}

Value Minus::evalRator(const Value &rand1, const Value &rand2) {
    int n1, d1, n2, d2;
    if (!getNumeric(rand1, n1, d1) || !getNumeric(rand2, n2, d2))
        throw RuntimeError("-: non-numeric argument");
    return makeNumeric(n1 * d2 - n2 * d1, d1 * d2);
}

Value Mult::evalRator(const Value &rand1, const Value &rand2) {
    int n1, d1, n2, d2;
    if (!getNumeric(rand1, n1, d1) || !getNumeric(rand2, n2, d2))
        throw RuntimeError("*: non-numeric argument");
    return makeNumeric(n1 * n2, d1 * d2);
}

Value Div::evalRator(const Value &rand1, const Value &rand2) {
    int n1, d1, n2, d2;
    if (!getNumeric(rand1, n1, d1) || !getNumeric(rand2, n2, d2))
        throw RuntimeError("/: non-numeric argument");
    if (n2 == 0) throw RuntimeError("Division by zero");
    return makeNumeric(n1 * d2, d1 * n2);
}

Value Modulo::evalRator(const Value &rand1, const Value &rand2) {
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int dividend = dynamic_cast<Integer*>(rand1.get())->n;
        int divisor = dynamic_cast<Integer*>(rand2.get())->n;
        if (divisor == 0) throw RuntimeError("Division by zero");
        return IntegerV(dividend % divisor);
    }
    throw RuntimeError("modulo is only defined for integers");
}

Value PlusVar::evalRator(const std::vector<Value> &args) {
    int num = 0, den = 1;
    for (auto &a : args) {
        int n, d;
        if (!getNumeric(a, n, d)) throw RuntimeError("+: non-numeric argument");
        num = num * d + n * den;
        den = den * d;
        int g = mygcd(num, den);
        if (g == 0) g = 1;
        num /= g; den /= g;
    }
    return makeNumeric(num, den);
}

Value MinusVar::evalRator(const std::vector<Value> &args) {
    if (args.empty()) throw RuntimeError("-: no arguments");
    int num, den;
    if (!getNumeric(args[0], num, den)) throw RuntimeError("-: non-numeric argument");
    if (args.size() == 1) {
        return makeNumeric(-num, den);
    }
    for (size_t i = 1; i < args.size(); i++) {
        int n, d;
        if (!getNumeric(args[i], n, d)) throw RuntimeError("-: non-numeric argument");
        num = num * d - n * den;
        den = den * d;
        int g = mygcd(num, den);
        if (g == 0) g = 1;
        num /= g; den /= g;
    }
    return makeNumeric(num, den);
}

Value MultVar::evalRator(const std::vector<Value> &args) {
    int num = 1, den = 1;
    for (auto &a : args) {
        int n, d;
        if (!getNumeric(a, n, d)) throw RuntimeError("*: non-numeric argument");
        num *= n;
        den *= d;
        int g = mygcd(num, den);
        if (g == 0) g = 1;
        num /= g; den /= g;
    }
    return makeNumeric(num, den);
}

Value DivVar::evalRator(const std::vector<Value> &args) {
    if (args.empty()) throw RuntimeError("/: no arguments");
    int num, den;
    if (!getNumeric(args[0], num, den)) throw RuntimeError("/: non-numeric argument");
    if (args.size() == 1) {
        if (num == 0) throw RuntimeError("Division by zero");
        return makeNumeric(den, num);
    }
    for (size_t i = 1; i < args.size(); i++) {
        int n, d;
        if (!getNumeric(args[i], n, d)) throw RuntimeError("/: non-numeric argument");
        if (n == 0) throw RuntimeError("Division by zero");
        num *= d;
        den *= n;
        int g = mygcd(num, den);
        if (g == 0) g = 1;
        num /= g; den /= g;
    }
    return makeNumeric(num, den);
}

Value Expt::evalRator(const Value &rand1, const Value &rand2) {
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int base = dynamic_cast<Integer*>(rand1.get())->n;
        int exponent = dynamic_cast<Integer*>(rand2.get())->n;
        if (exponent < 0) throw RuntimeError("Negative exponent not supported");
        if (base == 0 && exponent == 0) throw RuntimeError("0^0 is undefined");
        long long result = 1;
        long long b = base;
        int exp = exponent;
        while (exp > 0) {
            if (exp % 2 == 1) {
                result *= b;
                if (result > INT_MAX || result < INT_MIN) throw RuntimeError("Overflow");
            }
            b *= b;
            if ((b > INT_MAX || b < INT_MIN) && exp > 1) throw RuntimeError("Overflow");
            exp /= 2;
        }
        return IntegerV((int)result);
    }
    throw RuntimeError("expt: expected integers");
}

int compareNumericValues(const Value &v1, const Value &v2) {
    int n1, d1, n2, d2;
    if (!getNumeric(v1, n1, d1) || !getNumeric(v2, n2, d2))
        throw RuntimeError("compareNumericValues: non-numeric");
    long long left = (long long)n1 * d2;
    long long right = (long long)n2 * d1;
    return (left < right) ? -1 : (left > right) ? 1 : 0;
}

Value Less::evalRator(const Value &rand1, const Value &rand2) {
    return BooleanV(compareNumericValues(rand1, rand2) < 0);
}
Value LessEq::evalRator(const Value &rand1, const Value &rand2) {
    return BooleanV(compareNumericValues(rand1, rand2) <= 0);
}
Value Equal::evalRator(const Value &rand1, const Value &rand2) {
    return BooleanV(compareNumericValues(rand1, rand2) == 0);
}
Value GreaterEq::evalRator(const Value &rand1, const Value &rand2) {
    return BooleanV(compareNumericValues(rand1, rand2) >= 0);
}
Value Greater::evalRator(const Value &rand1, const Value &rand2) {
    return BooleanV(compareNumericValues(rand1, rand2) > 0);
}

static Value compareVar(const std::vector<Value> &args, int want) {
    // want: -1 for <, -2 for <=, 0 for ==, 1 for >, 2 for >=
    for (size_t i = 1; i < args.size(); i++) {
        int c = compareNumericValues(args[i-1], args[i]);
        bool ok = false;
        switch (want) {
            case -1: ok = (c < 0); break;
            case -2: ok = (c <= 0); break;
            case 0:  ok = (c == 0); break;
            case 1:  ok = (c > 0); break;
            case 2:  ok = (c >= 0); break;
        }
        if (!ok) return BooleanV(false);
    }
    return BooleanV(true);
}

Value LessVar::evalRator(const std::vector<Value> &args) { return compareVar(args, -1); }
Value LessEqVar::evalRator(const std::vector<Value> &args) { return compareVar(args, -2); }
Value EqualVar::evalRator(const std::vector<Value> &args) { return compareVar(args, 0); }
Value GreaterEqVar::evalRator(const std::vector<Value> &args) { return compareVar(args, 2); }
Value GreaterVar::evalRator(const std::vector<Value> &args) { return compareVar(args, 1); }

Value Cons::evalRator(const Value &rand1, const Value &rand2) {
    return PairV(rand1, rand2);
}

Value ListFunc::evalRator(const std::vector<Value> &args) {
    Value res = NullV();
    for (int i = (int)args.size() - 1; i >= 0; i--) {
        res = PairV(args[i], res);
    }
    return res;
}

Value IsList::evalRator(const Value &rand) {
    Value cur = rand;
    while (cur->v_type == V_PAIR) {
        Pair *p = dynamic_cast<Pair*>(cur.get());
        cur = p->cdr;
    }
    return BooleanV(cur->v_type == V_NULL);
}

Value Car::evalRator(const Value &rand) {
    if (rand->v_type != V_PAIR) throw RuntimeError("car: not a pair");
    return dynamic_cast<Pair*>(rand.get())->car;
}

Value Cdr::evalRator(const Value &rand) {
    if (rand->v_type != V_PAIR) throw RuntimeError("cdr: not a pair");
    return dynamic_cast<Pair*>(rand.get())->cdr;
}

Value SetCar::evalRator(const Value &rand1, const Value &rand2) {
    if (rand1->v_type != V_PAIR) throw RuntimeError("set-car!: not a pair");
    dynamic_cast<Pair*>(rand1.get())->car = rand2;
    return VoidV();
}

Value SetCdr::evalRator(const Value &rand1, const Value &rand2) {
    if (rand1->v_type != V_PAIR) throw RuntimeError("set-cdr!: not a pair");
    dynamic_cast<Pair*>(rand1.get())->cdr = rand2;
    return VoidV();
}

Value IsEq::evalRator(const Value &rand1, const Value &rand2) {
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        return BooleanV((dynamic_cast<Integer*>(rand1.get())->n) == (dynamic_cast<Integer*>(rand2.get())->n));
    }
    else if (rand1->v_type == V_BOOL && rand2->v_type == V_BOOL) {
        return BooleanV((dynamic_cast<Boolean*>(rand1.get())->b) == (dynamic_cast<Boolean*>(rand2.get())->b));
    }
    else if (rand1->v_type == V_SYM && rand2->v_type == V_SYM) {
        return BooleanV((dynamic_cast<Symbol*>(rand1.get())->s) == (dynamic_cast<Symbol*>(rand2.get())->s));
    }
    else if ((rand1->v_type == V_NULL && rand2->v_type == V_NULL) ||
             (rand1->v_type == V_VOID && rand2->v_type == V_VOID)) {
        return BooleanV(true);
    } else {
        return BooleanV(rand1.get() == rand2.get());
    }
}

Value IsBoolean::evalRator(const Value &rand) { return BooleanV(rand->v_type == V_BOOL); }
Value IsFixnum::evalRator(const Value &rand) { return BooleanV(rand->v_type == V_INT); }
Value IsNull::evalRator(const Value &rand) { return BooleanV(rand->v_type == V_NULL); }
Value IsPair::evalRator(const Value &rand) { return BooleanV(rand->v_type == V_PAIR); }
Value IsProcedure::evalRator(const Value &rand) { return BooleanV(rand->v_type == V_PROC); }
Value IsSymbol::evalRator(const Value &rand) { return BooleanV(rand->v_type == V_SYM); }
Value IsString::evalRator(const Value &rand) { return BooleanV(rand->v_type == V_STRING); }

Value Begin::eval(Assoc &e) {
    if (es.empty()) return VoidV();
    Value v = VoidV();
    for (auto &expr : es) v = expr->eval(e);
    return v;
}

// Convert a Syntax into a Value (for quote)
static Value syntaxToValue(Syntax &s) {
    if (Number *n = dynamic_cast<Number*>(s.get())) {
        return IntegerV(n->n);
    }
    if (RationalSyntax *r = dynamic_cast<RationalSyntax*>(s.get())) {
        return makeNumeric(r->numerator, r->denominator);
    }
    if (TrueSyntax *t = dynamic_cast<TrueSyntax*>(s.get())) {
        (void)t;
        return BooleanV(true);
    }
    if (FalseSyntax *f = dynamic_cast<FalseSyntax*>(s.get())) {
        (void)f;
        return BooleanV(false);
    }
    if (SymbolSyntax *sym = dynamic_cast<SymbolSyntax*>(s.get())) {
        return SymbolV(sym->s);
    }
    if (StringSyntax *ss = dynamic_cast<StringSyntax*>(s.get())) {
        return StringV(ss->s);
    }
    if (List *l = dynamic_cast<List*>(s.get())) {
        // Check for (A . B) form - in Scheme the dot represents a pair
        // But our parser reads dots as regular symbols. We need to handle '.' in the middle.
        // For quote, the list (a b . c) is read as a normal list but in reader .
        // Actually, looking at syntax.cpp's readItem, it treats '.' as part of a symbol token.
        // A 3-element list (1 . 2) would be read as [1, ., 2] — three tokens including symbol "."
        // If we see such a pattern, interpret as dotted pair.

        // Check if any sub-syntax is a symbol "."
        int dotIdx = -1;
        for (size_t i = 0; i < l->stxs.size(); i++) {
            SymbolSyntax *ss = dynamic_cast<SymbolSyntax*>(l->stxs[i].get());
            if (ss && ss->s == ".") {
                dotIdx = (int)i;
                break;
            }
        }

        if (dotIdx >= 0) {
            // (A ... . B) means cons A ... B
            // Must be at position size-2
            if (dotIdx != (int)l->stxs.size() - 2) {
                // malformed: just treat as normal list
            } else {
                Value tail = syntaxToValue(l->stxs[dotIdx + 1]);
                for (int i = dotIdx - 1; i >= 0; i--) {
                    Value head = syntaxToValue(l->stxs[i]);
                    tail = PairV(head, tail);
                }
                return tail;
            }
        }

        // Plain list
        Value res = NullV();
        for (int i = (int)l->stxs.size() - 1; i >= 0; i--) {
            Value head = syntaxToValue(l->stxs[i]);
            res = PairV(head, res);
        }
        return res;
    }
    throw RuntimeError("quote: unknown syntax");
}

Value Quote::eval(Assoc &e) {
    return syntaxToValue(s);
}

// Scheme truthiness: only #f is false
static bool isTruthy(const Value &v) {
    if (v->v_type == V_BOOL) return dynamic_cast<Boolean*>(v.get())->b;
    return true;
}

Value AndVar::eval(Assoc &e) {
    if (rands.empty()) return BooleanV(true);
    Value v = BooleanV(true);
    for (auto &r : rands) {
        v = r->eval(e);
        if (!isTruthy(v)) return v;
    }
    return v;
}

Value OrVar::eval(Assoc &e) {
    if (rands.empty()) return BooleanV(false);
    Value v = BooleanV(false);
    for (auto &r : rands) {
        v = r->eval(e);
        if (isTruthy(v)) return v;
    }
    return v;
}

Value Not::evalRator(const Value &rand) {
    return BooleanV(!isTruthy(rand));
}

Value If::eval(Assoc &e) {
    Value c = cond->eval(e);
    if (isTruthy(c)) return conseq->eval(e);
    else return alter->eval(e);
}

Value Cond::eval(Assoc &env) {
    for (auto &clause : clauses) {
        if (clause.empty()) continue;
        Value c = clause[0]->eval(env);
        if (isTruthy(c)) {
            if (clause.size() == 1) return c;
            Value res = VoidV();
            for (size_t i = 1; i < clause.size(); i++)
                res = clause[i]->eval(env);
            return res;
        }
    }
    return VoidV();
}

Value Lambda::eval(Assoc &env) {
    return ProcedureV(x, e, env);
}

Value Apply::eval(Assoc &e) {
    Value rv = rator->eval(e);
    if (rv->v_type != V_PROC) throw RuntimeError("Attempt to apply a non-procedure");
    Procedure* clos_ptr = dynamic_cast<Procedure*>(rv.get());

    // Evaluate args
    std::vector<Value> args;
    for (auto &r : rand) args.push_back(r->eval(e));

    // Special case: procedure created from primitive variadic (empty parameters, body is a Variadic expression)
    if (clos_ptr->parameters.empty()) {
        if (auto varNode = dynamic_cast<Variadic*>(clos_ptr->e.get())) {
            return varNode->evalRator(args);
        }
        if (auto andNode = dynamic_cast<AndVar*>(clos_ptr->e.get())) {
            // Evaluate and-semantics on already evaluated args
            if (args.empty()) return BooleanV(true);
            Value v = BooleanV(true);
            for (auto &a : args) {
                v = a;
                if (!isTruthy(v)) return v;
            }
            return v;
        }
        if (auto orNode = dynamic_cast<OrVar*>(clos_ptr->e.get())) {
            if (args.empty()) return BooleanV(false);
            Value v = BooleanV(false);
            for (auto &a : args) {
                v = a;
                if (isTruthy(v)) return v;
            }
            return v;
        }
    }

    if (args.size() != clos_ptr->parameters.size())
        throw RuntimeError("Wrong number of arguments");

    Assoc param_env = clos_ptr->env;
    for (size_t i = 0; i < args.size(); i++) {
        param_env = extend(clos_ptr->parameters[i], args[i], param_env);
    }

    return clos_ptr->e->eval(param_env);
}

Value Define::eval(Assoc &env) {
    // define is not allowed to overlap with primitives/reserved_words
    if (primitives.count(var) || reserved_words.count(var)) {
        throw RuntimeError("define: cannot redefine primitive or reserved word: " + var);
    }
    // Create placeholder for recursion, then update
    env = extend(var, NullV(), env);
    Value v = e->eval(env);
    modify(var, v, env);
    return VoidV();
}

Value Let::eval(Assoc &env) {
    // Evaluate bindings in outer env, then extend
    std::vector<Value> vals;
    for (auto &b : bind) vals.push_back(b.second->eval(env));
    Assoc newEnv = env;
    for (size_t i = 0; i < bind.size(); i++)
        newEnv = extend(bind[i].first, vals[i], newEnv);
    return body->eval(newEnv);
}

Value Letrec::eval(Assoc &env) {
    // Step 1: bind all vars to nullptr in env1
    Assoc env1 = env;
    for (auto &b : bind) env1 = extend(b.first, Value(nullptr), env1);
    // Step 2: evaluate expressions in env1
    std::vector<Value> vals;
    for (auto &b : bind) vals.push_back(b.second->eval(env1));
    // Step 3: bind to proper values in env2
    Assoc env2 = env1;
    for (size_t i = 0; i < bind.size(); i++)
        env2 = extend(bind[i].first, vals[i], env2);
    // Step 4: update env2 bindings to their values
    // (Already done via extend; for closures capturing env1, modify env1 so they see env2 values)
    for (size_t i = 0; i < bind.size(); i++)
        modify(bind[i].first, vals[i], env1);
    return body->eval(env2);
}

Value Set::eval(Assoc &env) {
    // Verify variable exists (check env first, then global fallback)
    Value existing = find(var, env);
    bool inGlobal = false;
    if (existing.get() == nullptr && globalEnvPtr != nullptr) {
        existing = find(var, *globalEnvPtr);
        if (existing.get() != nullptr) inGlobal = true;
    }
    if (existing.get() == nullptr) throw RuntimeError("set!: variable not defined: " + var);
    // Evaluate and modify
    Value v = e->eval(env);
    modify(var, v, env);
    if (inGlobal && globalEnvPtr != nullptr) {
        modify(var, v, *globalEnvPtr);
    }
    return VoidV();
}

Value Display::evalRator(const Value &rand) {
    if (rand->v_type == V_STRING) {
        String* str_ptr = dynamic_cast<String*>(rand.get());
        std::cout << str_ptr->s;
    } else {
        rand->show(std::cout);
    }
    return VoidV();
}
