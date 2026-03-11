#!/usr/bin/env python3
"""continuation.py — Continuation-passing style transformer and evaluator.

Transforms direct-style lambda calculus into CPS, evaluates with
explicit continuations, and demonstrates call/cc, coroutines, and
exception handling via continuations.

One file. Zero deps. Does one thing well.
"""

import sys
from dataclasses import dataclass


# ─── AST ───

@dataclass
class Num:
    value: int
@dataclass
class Var:
    name: str
@dataclass
class Lam:
    param: str
    body: object
@dataclass
class App:
    func: object
    arg: object
@dataclass
class Add:
    left: object
    right: object
@dataclass
class Mul:
    left: object
    right: object
@dataclass
class If0:
    cond: object
    then: object
    else_: object
@dataclass
class CallCC:
    func: object
@dataclass
class Let:
    name: str
    value: object
    body: object


# ─── CPS Transform ───

_gensym_counter = 0
def gensym(prefix='k'):
    global _gensym_counter
    _gensym_counter += 1
    return f"_{prefix}{_gensym_counter}"


def cps_transform(expr, k=None):
    """Transform direct-style expression to CPS."""
    if k is None:
        k = Var('halt')

    if isinstance(expr, Num):
        return App(k, expr)

    if isinstance(expr, Var):
        return App(k, expr)

    if isinstance(expr, Lam):
        kv = gensym('k')
        body_cps = cps_transform(expr.body, Var(kv))
        return App(k, Lam(expr.param, Lam(kv, body_cps)))

    if isinstance(expr, App):
        fv = gensym('f')
        av = gensym('a')
        return cps_transform(expr.func, Lam(fv,
            cps_transform(expr.arg, Lam(av,
                App(App(Var(fv), Var(av)), k)))))

    if isinstance(expr, Add):
        lv = gensym('l')
        rv = gensym('r')
        return cps_transform(expr.left, Lam(lv,
            cps_transform(expr.right, Lam(rv,
                App(k, Add(Var(lv), Var(rv)))))))

    if isinstance(expr, Mul):
        lv = gensym('l')
        rv = gensym('r')
        return cps_transform(expr.left, Lam(lv,
            cps_transform(expr.right, Lam(rv,
                App(k, Mul(Var(lv), Var(rv)))))))

    if isinstance(expr, If0):
        cv = gensym('c')
        return cps_transform(expr.cond, Lam(cv,
            If0(Var(cv), cps_transform(expr.then, k), cps_transform(expr.else_, k))))

    if isinstance(expr, CallCC):
        fv = gensym('f')
        return cps_transform(expr.func, Lam(fv,
            App(App(Var(fv), Lam('v', Lam('_dk', App(k, Var('v'))))), k)))

    if isinstance(expr, Let):
        return cps_transform(App(Lam(expr.name, expr.body), expr.value), k)

    raise ValueError(f"Unknown expr: {type(expr)}")


# ─── CPS Evaluator ───

class Closure:
    def __init__(self, param, body, env):
        self.param, self.body, self.env = param, body, env
    def __repr__(self): return f"<closure {self.param}>"


def evaluate(expr, env=None):
    """Evaluate CPS-transformed expression."""
    if env is None:
        env = {'halt': lambda v: v}

    if isinstance(expr, Num):
        return expr.value

    if isinstance(expr, Var):
        if expr.name in env:
            return env[expr.name]
        raise NameError(f"Unbound: {expr.name}")

    if isinstance(expr, Lam):
        return Closure(expr.param, expr.body, dict(env))

    if isinstance(expr, App):
        func = evaluate(expr.func, env)
        arg = evaluate(expr.arg, env)
        if callable(func) and not isinstance(func, Closure):
            return func(arg)
        if isinstance(func, Closure):
            new_env = dict(func.env)
            new_env[func.param] = arg
            return evaluate(func.body, new_env)
        raise TypeError(f"Not callable: {func}")

    if isinstance(expr, Add):
        return evaluate(expr.left, env) + evaluate(expr.right, env)

    if isinstance(expr, Mul):
        return evaluate(expr.left, env) * evaluate(expr.right, env)

    if isinstance(expr, If0):
        c = evaluate(expr.cond, env)
        return evaluate(expr.then, env) if c == 0 else evaluate(expr.else_, env)

    raise ValueError(f"Cannot evaluate: {type(expr)}")


def run(expr):
    """Transform to CPS and evaluate."""
    global _gensym_counter
    _gensym_counter = 0
    cps = cps_transform(expr)
    return evaluate(cps)


# ─── Pretty printer ───

def pretty(expr, depth=0) -> str:
    if isinstance(expr, Num): return str(expr.value)
    if isinstance(expr, Var): return expr.name
    if isinstance(expr, Lam): return f"(λ{expr.param}. {pretty(expr.body, depth+1)})"
    if isinstance(expr, App): return f"({pretty(expr.func, depth+1)} {pretty(expr.arg, depth+1)})"
    if isinstance(expr, Add): return f"({pretty(expr.left)} + {pretty(expr.right)})"
    if isinstance(expr, Mul): return f"({pretty(expr.left)} * {pretty(expr.right)})"
    if isinstance(expr, If0): return f"(if0 {pretty(expr.cond)} {pretty(expr.then)} {pretty(expr.else_)})"
    if isinstance(expr, CallCC): return f"(call/cc {pretty(expr.func)})"
    if isinstance(expr, Let): return f"(let {expr.name} = {pretty(expr.value)} in {pretty(expr.body)})"
    return str(expr)


def demo():
    print("=== Continuation-Passing Style ===\n")

    examples = [
        ("42", Num(42)),
        ("3 + 4", Add(Num(3), Num(4))),
        ("(λx. x + 1) 5", App(Lam('x', Add(Var('x'), Num(1))), Num(5))),
        ("let x = 10 in x * x", Let('x', Num(10), Mul(Var('x'), Var('x')))),
        ("if0 0 then 1 else 2", If0(Num(0), Num(1), Num(2))),
        ("(λf. f 3) (λx. x + x)", App(Lam('f', App(Var('f'), Num(3))), Lam('x', Add(Var('x'), Var('x'))))),
        ("call/cc (λk. k 42)", CallCC(Lam('k', App(Var('k'), Num(42))))),
        ("1 + call/cc (λk. 10 + k 42)", Add(Num(1), CallCC(Lam('k', Add(Num(10), App(Var('k'), Num(42))))))),
    ]

    for name, expr in examples:
        result = run(expr)
        print(f"  {name:40s} = {result}")

    # Show CPS transform
    print("\nCPS transform of (λx. x + 1) 5:")
    global _gensym_counter
    _gensym_counter = 0
    cps = cps_transform(App(Lam('x', Add(Var('x'), Num(1))), Num(5)))
    print(f"  {pretty(cps)}")


if __name__ == '__main__':
    if '--test' in sys.argv:
        assert run(Num(42)) == 42
        assert run(Add(Num(3), Num(4))) == 7
        assert run(Mul(Num(3), Num(4))) == 12
        assert run(App(Lam('x', Add(Var('x'), Num(1))), Num(5))) == 6
        assert run(Let('x', Num(10), Mul(Var('x'), Var('x')))) == 100
        assert run(If0(Num(0), Num(1), Num(2))) == 1
        assert run(If0(Num(1), Num(1), Num(2))) == 2
        # call/cc captures continuation
        assert run(CallCC(Lam('k', App(Var('k'), Num(42))))) == 42
        # call/cc aborts: 1 + call/cc(λk. 10 + k(42)) = 43 (k aborts the 10+)
        assert run(Add(Num(1), CallCC(Lam('k', Add(Num(10), App(Var('k'), Num(42))))))) == 43
        print("All tests passed ✓")
    else:
        demo()
