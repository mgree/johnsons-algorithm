edge(a,b).
edge(a,c).
edge(b,d).
edge(c,d).

reach(X, Y) :- edge(X, Y).
reach(X, Z) :- edge(X, Y), reach(Y, Z).