+++
id = "def-weil-pbc-etale-sheaves"
kind = "definition"
title = "Sheaves of abelian groups and of modules"
order = 581
uses = ["def-weil-pbc-etale-site", "def-weil-pbc-scheme-conventions"]
+++
For a scheme $T$, let $\Ab(T_{\Et})$ be the abelian category of sheaves of
abelian groups on the small etale site [def-weil-pbc-etale-site] $T_{\Et}$;
it is a Grothendieck abelian category. For a commutative ring $R$, let $R_T$
be the constant sheaf of rings on $T_{\Et}$ and write $\Mod(T_{\Et},R)$ for
the abelian category of sheaves of $R_T$-modules. A sheaf $F\in\Ab(T_{\Et})$
is *torsion* if every local section of $F$ is locally killed by a positive
integer: for $s\in F(U)$ there are an etale covering $\{U_i\to U\}$ and
integers $n_i>0$ with $n_is|_{U_i}=0$. Equivalently every geometric stalk of
$F$ is torsion. This is weaker than asking every group $F(U)$ to be torsion:
the constant sheaf $\mathbf Q/\mathbf Z$ is torsion, while its sections over
$U=\coprod_{n\ge1}T$ contain $(1/2^n)_n$, of infinite order. A
sheaf of sets on $T_{\Et}$ is *locally constant* if it is locally isomorphic
to a constant sheaf, and *lisse* if it is locally constant with finite
stalks. It is *constructible* if $T$ admits a finite partition into locally
closed constructible subschemes on each of which it is finite locally
constant. A sheaf has *torsion cohomology* if every cohomology sheaf is
torsion.
