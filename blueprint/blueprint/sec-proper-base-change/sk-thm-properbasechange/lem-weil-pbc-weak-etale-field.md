+++
id = "lem-weil-pbc-weak-etale-field"
kind = "lemma"
title = "Weakly etale algebras over a field"
order = 1217
uses = ["def-weil-pbc-ind-etale-algebra", "lem-weil-pbc-ind-etale-stability", "lem-weil-pbc-weak-etale-tor"]
+++
If $k$ is a field and $B/k$ is weakly etale
[def-weil-pbc-ind-etale-algebra], every finitely generated $k$-subalgebra of
$B$ is finite etale. In particular $B$ is ind-etale, is reduced, and all its
residue fields are separable algebraic over $k$.

## Proof

By [lem-weil-pbc-weak-etale-tor], every $B$-module is flat. For a local ring
with this property, flatness of the quotient by $(b)$ gives $b=bc$ for some
$c\in(b)$. If $b$ is a nonunit, $1-c$ is a unit, so $b=0$. All local rings of
$B$ are therefore fields; in particular $B$ is reduced.

We first treat a weakly etale field extension $k\subset L$. By
[lem-weil-pbc-ind-etale-stability] and the Tor formula, $L\otimes_kL$ also
has every module flat. For any subfield $E\subset L$ containing $k$, the map
$E\otimes_kE\to L\otimes_kL$ is faithfully flat. Flatness of every module
descends along a faithfully flat ring map, by the tensor criterion for
injectivity. Thus $E\otimes_kE$ has every module flat. If $t\in L$ were
transcendental, take $E=k(t)$. Then $E\otimes_kE$ is a domain with the
nonzero nonunit $t\otimes1-1\otimes t$, and its localization at the diagonal
prime is not a field, a contradiction. Hence $L/k$ is algebraic. An
inseparable element would instead give a finite subextension $E/k$ for which
$E\otimes_kE$ is nonreduced: its presentation by the minimal polynomial has a
repeated factor at the root already in $E$. This is the same contradiction.
Thus $L/k$ is separable algebraic.

Apply this result to the fields $B_{\mathfrak q}$. They are weakly etale over
$k$, since localization is ind-Zariski and weak etaleness is preserved by
composition. Given $b\in B$, at each prime choose a monic separable
polynomial annihilating its germ. This relation holds on a basic open
neighbourhood. Finitely many such neighbourhoods cover $\operatorname{Spec}B$;
the product of their polynomials annihilates $b$ in every local ring, hence
in $B$. Thus every element of $B$ is integral over $k$. A finitely generated
subalgebra is consequently finite-dimensional and reduced, hence a product of
finite field extensions. Each factor embeds into some $B_{\mathfrak q}$, so
each extension is separable. These finite etale subalgebras form the filtered
presentation of [def-weil-pbc-ind-etale-algebra]. This proves the field
calculation also recorded in
[Stacks Project, Tag 092Q](https://stacks.math.columbia.edu/tag/092Q).
