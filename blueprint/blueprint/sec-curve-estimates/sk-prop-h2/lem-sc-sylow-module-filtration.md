+++
id = "lem-sc-sylow-module-filtration"
kind = "lemma"
title = "Sylow reduction of a finite torsion module"
order = 978
uses = ["def-exc-continuous-cohomology"]
+++
Let $G$ be profinite, $\ell$ a prime, and $M$ a finite
$\ell$-primary discrete
continuous $G$-module. There is an open subgroup $H\subset G$
of index prime to $\ell$ such that $M|_H$ has a finite filtration
whose successive quotients are trivial $\mathbf F_\ell$-modules.

## Proof

The intersection of the stabilizers of the finitely many elements
of $M$ is open and normal, by
[def-exc-continuous-cohomology]. Thus the action factors through
a finite quotient $Q$. Choose an $\ell$-Sylow subgroup $P$
of $Q$, and let $H$ be its inverse image. The index $[G:H]$
is prime to $\ell$. First filter $M$ by its powers of $\ell$;
the quotients are finite-dimensional $\mathbf F_\ell[P]$-modules.
Every nonzero such module $V$ has a nonzero invariant vector:
the nontrivial $P$-orbits in its underlying finite set have
cardinality divisible by $\ell$, so
$\#V^P\equiv\#V=0\pmod\ell$. Since $0\in V^P$, this
forces $\#V^P\geq\ell$. The line spanned by a nonzero invariant
vector is a trivial submodule. Induction on $\dim V$, applied
to its quotient by this line, gives the required filtration.
Refining the powers-of-$\ell$ filtration proves the assertion.
