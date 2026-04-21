/**
 * @file parser.cpp
 * @brief Parsing implementation for Scheme syntax tree to expression tree conversion
 */

#include "RE.hpp"
#include "Def.hpp"
#include "syntax.hpp"
#include "value.hpp"
#include "expr.hpp"
#include <map>
#include <string>
#include <iostream>

#define mp make_pair
using std::string;
using std::vector;
using std::pair;

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

Expr Syntax::parse(Assoc &env) {
    return ptr->parse(env);
}

Expr Number::parse(Assoc &env) {
    return Expr(new Fixnum(n));
}

Expr RationalSyntax::parse(Assoc &env) {
    return Expr(new RationalNum(numerator, denominator));
}

Expr SymbolSyntax::parse(Assoc &env) {
    return Expr(new Var(s));
}

Expr StringSyntax::parse(Assoc &env) {
    return Expr(new StringExpr(s));
}

Expr TrueSyntax::parse(Assoc &env) {
    return Expr(new True());
}

Expr FalseSyntax::parse(Assoc &env) {
    return Expr(new False());
}

// Helper: parse a list of expressions given the stxs starting index
static vector<Expr> parseArgs(vector<Syntax> &stxs, size_t start, Assoc &env) {
    vector<Expr> args;
    for (size_t i = start; i < stxs.size(); i++) {
        args.push_back(stxs[i]->parse(env));
    }
    return args;
}

Expr List::parse(Assoc &env) {
    if (stxs.empty()) {
        return Expr(new Quote(Syntax(new List())));
    }

    SymbolSyntax *id = dynamic_cast<SymbolSyntax*>(stxs[0].get());
    if (id == nullptr) {
        // First element is not a symbol: it's an expression to apply
        Expr rator = stxs[0]->parse(env);
        vector<Expr> rands = parseArgs(stxs, 1, env);
        return Expr(new Apply(rator, rands));
    }
    string op = id->s;

    // If op is a user-defined variable, treat as Apply
    if (find(op, env).get() != nullptr) {
        Expr rator = Expr(new Var(op));
        vector<Expr> rands = parseArgs(stxs, 1, env);
        return Expr(new Apply(rator, rands));
    }

    // Handle reserved words first
    if (reserved_words.count(op) != 0) {
        switch (reserved_words[op]) {
            case E_BEGIN: {
                vector<Expr> exprs = parseArgs(stxs, 1, env);
                return Expr(new Begin(exprs));
            }
            case E_QUOTE: {
                if (stxs.size() != 2) throw RuntimeError("quote: wrong number of args");
                return Expr(new Quote(stxs[1]));
            }
            case E_IF: {
                if (stxs.size() != 4) throw RuntimeError("if: wrong number of args");
                Expr c = stxs[1]->parse(env);
                Expr t = stxs[2]->parse(env);
                Expr e = stxs[3]->parse(env);
                return Expr(new If(c, t, e));
            }
            case E_COND: {
                vector<vector<Expr>> clauses;
                for (size_t i = 1; i < stxs.size(); i++) {
                    List *cl = dynamic_cast<List*>(stxs[i].get());
                    if (cl == nullptr) throw RuntimeError("cond: malformed clause");
                    vector<Expr> clause;
                    // Check for 'else' as first symbol
                    bool isElse = false;
                    SymbolSyntax *firstSym = cl->stxs.empty() ? nullptr : dynamic_cast<SymbolSyntax*>(cl->stxs[0].get());
                    if (firstSym && firstSym->s == "else") {
                        // else branch: mark by pushing a True as first element
                        clause.push_back(Expr(new True()));
                        for (size_t j = 1; j < cl->stxs.size(); j++) {
                            clause.push_back(cl->stxs[j]->parse(env));
                        }
                    } else {
                        for (size_t j = 0; j < cl->stxs.size(); j++) {
                            clause.push_back(cl->stxs[j]->parse(env));
                        }
                    }
                    clauses.push_back(clause);
                }
                return Expr(new Cond(clauses));
            }
            case E_LAMBDA: {
                if (stxs.size() < 3) throw RuntimeError("lambda: wrong number of args");
                List *paramList = dynamic_cast<List*>(stxs[1].get());
                if (paramList == nullptr) throw RuntimeError("lambda: param list expected");
                vector<string> params;
                Assoc newEnv = env;
                for (auto &p : paramList->stxs) {
                    SymbolSyntax *ps = dynamic_cast<SymbolSyntax*>(p.get());
                    if (ps == nullptr) throw RuntimeError("lambda: parameter must be symbol");
                    params.push_back(ps->s);
                    // Add to env as a placeholder so body references are parsed as Var (via Apply fallback)
                    newEnv = extend(ps->s, NullV(), newEnv);
                }
                // Body: if multiple expressions, wrap in begin
                Expr body(nullptr);
                if (stxs.size() == 3) {
                    body = stxs[2]->parse(newEnv);
                } else {
                    vector<Expr> exprs;
                    for (size_t i = 2; i < stxs.size(); i++)
                        exprs.push_back(stxs[i]->parse(newEnv));
                    body = Expr(new Begin(exprs));
                }
                return Expr(new Lambda(params, body));
            }
            case E_DEFINE: {
                if (stxs.size() < 3) throw RuntimeError("define: wrong number of args");
                // Two forms:
                //  (define var expr)
                //  (define (fname args...) body)
                SymbolSyntax *sym = dynamic_cast<SymbolSyntax*>(stxs[1].get());
                if (sym) {
                    // (define var expr) - if multiple exprs, use begin
                    Expr e(nullptr);
                    if (stxs.size() == 3) {
                        e = stxs[2]->parse(env);
                    } else {
                        vector<Expr> exprs;
                        for (size_t i = 2; i < stxs.size(); i++)
                            exprs.push_back(stxs[i]->parse(env));
                        e = Expr(new Begin(exprs));
                    }
                    return Expr(new Define(sym->s, e));
                }
                List *fnHead = dynamic_cast<List*>(stxs[1].get());
                if (fnHead == nullptr || fnHead->stxs.empty()) {
                    throw RuntimeError("define: malformed");
                }
                SymbolSyntax *fnName = dynamic_cast<SymbolSyntax*>(fnHead->stxs[0].get());
                if (fnName == nullptr) throw RuntimeError("define: function name must be symbol");
                vector<string> params;
                Assoc newEnv = env;
                for (size_t i = 1; i < fnHead->stxs.size(); i++) {
                    SymbolSyntax *ps = dynamic_cast<SymbolSyntax*>(fnHead->stxs[i].get());
                    if (ps == nullptr) throw RuntimeError("define: param must be symbol");
                    params.push_back(ps->s);
                    newEnv = extend(ps->s, NullV(), newEnv);
                }
                Expr body(nullptr);
                if (stxs.size() == 3) {
                    body = stxs[2]->parse(newEnv);
                } else {
                    vector<Expr> exprs;
                    for (size_t i = 2; i < stxs.size(); i++)
                        exprs.push_back(stxs[i]->parse(newEnv));
                    body = Expr(new Begin(exprs));
                }
                Expr lam = Expr(new Lambda(params, body));
                return Expr(new Define(fnName->s, lam));
            }
            case E_LET:
            case E_LETREC: {
                if (stxs.size() < 3) throw RuntimeError("let/letrec: wrong number of args");
                List *bindList = dynamic_cast<List*>(stxs[1].get());
                if (bindList == nullptr) throw RuntimeError("let/letrec: bindings expected");
                vector<pair<string, Expr>> binds;
                bool isLetrec = (reserved_words[op] == E_LETREC);

                Assoc bodyEnv = env;
                Assoc bindEnv = env;
                if (isLetrec) {
                    // For letrec, all variables available in bind expressions
                    for (auto &b : bindList->stxs) {
                        List *bp = dynamic_cast<List*>(b.get());
                        if (bp == nullptr || bp->stxs.size() != 2) throw RuntimeError("let: malformed binding");
                        SymbolSyntax *bs = dynamic_cast<SymbolSyntax*>(bp->stxs[0].get());
                        if (bs == nullptr) throw RuntimeError("let: binding name must be symbol");
                        bindEnv = extend(bs->s, NullV(), bindEnv);
                    }
                    bodyEnv = bindEnv;
                    for (auto &b : bindList->stxs) {
                        List *bp = dynamic_cast<List*>(b.get());
                        SymbolSyntax *bs = dynamic_cast<SymbolSyntax*>(bp->stxs[0].get());
                        Expr e = bp->stxs[1]->parse(bindEnv);
                        binds.push_back(std::make_pair(bs->s, e));
                    }
                } else {
                    // let: bind expressions evaluated in outer env
                    for (auto &b : bindList->stxs) {
                        List *bp = dynamic_cast<List*>(b.get());
                        if (bp == nullptr || bp->stxs.size() != 2) throw RuntimeError("let: malformed binding");
                        SymbolSyntax *bs = dynamic_cast<SymbolSyntax*>(bp->stxs[0].get());
                        if (bs == nullptr) throw RuntimeError("let: binding name must be symbol");
                        Expr e = bp->stxs[1]->parse(env);
                        binds.push_back(std::make_pair(bs->s, e));
                        bodyEnv = extend(bs->s, NullV(), bodyEnv);
                    }
                }
                Expr body(nullptr);
                if (stxs.size() == 3) {
                    body = stxs[2]->parse(bodyEnv);
                } else {
                    vector<Expr> exprs;
                    for (size_t i = 2; i < stxs.size(); i++)
                        exprs.push_back(stxs[i]->parse(bodyEnv));
                    body = Expr(new Begin(exprs));
                }
                if (isLetrec) return Expr(new Letrec(binds, body));
                else return Expr(new Let(binds, body));
            }
            case E_SET: {
                if (stxs.size() != 3) throw RuntimeError("set!: wrong number of args");
                SymbolSyntax *sym = dynamic_cast<SymbolSyntax*>(stxs[1].get());
                if (sym == nullptr) throw RuntimeError("set!: variable must be symbol");
                Expr e = stxs[2]->parse(env);
                return Expr(new Set(sym->s, e));
            }
            default:
                throw RuntimeError("Unknown reserved word: " + op);
        }
    }

    // Primitive function
    if (primitives.count(op) != 0) {
        vector<Expr> parameters = parseArgs(stxs, 1, env);
        ExprType op_type = primitives[op];
        switch (op_type) {
            case E_PLUS:
                return Expr(new PlusVar(parameters));
            case E_MINUS:
                return Expr(new MinusVar(parameters));
            case E_MUL:
                return Expr(new MultVar(parameters));
            case E_DIV:
                return Expr(new DivVar(parameters));
            case E_MODULO:
                if (parameters.size() != 2) throw RuntimeError("modulo: wrong number of args");
                return Expr(new Modulo(parameters[0], parameters[1]));
            case E_EXPT:
                if (parameters.size() != 2) throw RuntimeError("expt: wrong number of args");
                return Expr(new Expt(parameters[0], parameters[1]));
            case E_LT:
                return Expr(new LessVar(parameters));
            case E_LE:
                return Expr(new LessEqVar(parameters));
            case E_EQ:
                return Expr(new EqualVar(parameters));
            case E_GE:
                return Expr(new GreaterEqVar(parameters));
            case E_GT:
                return Expr(new GreaterVar(parameters));
            case E_CONS:
                if (parameters.size() != 2) throw RuntimeError("cons: wrong number of args");
                return Expr(new Cons(parameters[0], parameters[1]));
            case E_CAR:
                if (parameters.size() != 1) throw RuntimeError("car: wrong number of args");
                return Expr(new Car(parameters[0]));
            case E_CDR:
                if (parameters.size() != 1) throw RuntimeError("cdr: wrong number of args");
                return Expr(new Cdr(parameters[0]));
            case E_LIST:
                return Expr(new ListFunc(parameters));
            case E_SETCAR:
                if (parameters.size() != 2) throw RuntimeError("set-car!: wrong number of args");
                return Expr(new SetCar(parameters[0], parameters[1]));
            case E_SETCDR:
                if (parameters.size() != 2) throw RuntimeError("set-cdr!: wrong number of args");
                return Expr(new SetCdr(parameters[0], parameters[1]));
            case E_NOT:
                if (parameters.size() != 1) throw RuntimeError("not: wrong number of args");
                return Expr(new Not(parameters[0]));
            case E_AND:
                return Expr(new AndVar(parameters));
            case E_OR:
                return Expr(new OrVar(parameters));
            case E_EQQ:
                if (parameters.size() != 2) throw RuntimeError("eq?: wrong number of args");
                return Expr(new IsEq(parameters[0], parameters[1]));
            case E_BOOLQ:
                if (parameters.size() != 1) throw RuntimeError("boolean?: wrong number of args");
                return Expr(new IsBoolean(parameters[0]));
            case E_INTQ:
                if (parameters.size() != 1) throw RuntimeError("number?: wrong number of args");
                return Expr(new IsFixnum(parameters[0]));
            case E_NULLQ:
                if (parameters.size() != 1) throw RuntimeError("null?: wrong number of args");
                return Expr(new IsNull(parameters[0]));
            case E_PAIRQ:
                if (parameters.size() != 1) throw RuntimeError("pair?: wrong number of args");
                return Expr(new IsPair(parameters[0]));
            case E_PROCQ:
                if (parameters.size() != 1) throw RuntimeError("procedure?: wrong number of args");
                return Expr(new IsProcedure(parameters[0]));
            case E_SYMBOLQ:
                if (parameters.size() != 1) throw RuntimeError("symbol?: wrong number of args");
                return Expr(new IsSymbol(parameters[0]));
            case E_LISTQ:
                if (parameters.size() != 1) throw RuntimeError("list?: wrong number of args");
                return Expr(new IsList(parameters[0]));
            case E_STRINGQ:
                if (parameters.size() != 1) throw RuntimeError("string?: wrong number of args");
                return Expr(new IsString(parameters[0]));
            case E_DISPLAY:
                if (parameters.size() != 1) throw RuntimeError("display: wrong number of args");
                return Expr(new Display(parameters[0]));
            case E_VOID:
                if (parameters.size() != 0) throw RuntimeError("void: wrong number of args");
                return Expr(new MakeVoid());
            case E_EXIT:
                return Expr(new Exit());
            default:
                throw RuntimeError("Unknown primitive: " + op);
        }
    }

    // Default: treat as Apply of a variable
    Expr rator = Expr(new Var(op));
    vector<Expr> rands = parseArgs(stxs, 1, env);
    return Expr(new Apply(rator, rands));
}
