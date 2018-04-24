import sympy as sy

x, y, z, a, b, c, d, e, f, g, h, k, l, m, n, o, p, q, r, s, t, u, v, w = sy.symbols(
    'x, y, z, a, b, c, d, e, f, g, h, k, l, m, n, o, p, q, r, s, t, u, v, w')
sol = sy.solve([x+y - 3, x - -5], dict=True)
print(sol)