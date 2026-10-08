+++
id = "lemma-weil-pbc-curve-separably-closed-passage"
kind = "lemma"
title = "Passage between separably closed fields"
order = 1148
uses = ["lem-pc-homeo-pure-insep", "lem-pc-kbar-pure-insep", "lemma-weil-pbc-universal-homeomorphism-coverings", "lemma-weil-pbc-universal-homeomorphism-site-equivalence"]
+++
Let $k\subseteq k'$ be separably closed fields, let $C$ be proper of
dimension at most one over $k$, and let $F$ be a torsion etale sheaf. If
proper-curve cohomology is invariant for algebraically closed extensions,
then the specified restriction
$H^q(C,F)\to H^q(C_{k'},F|)$ is an isomorphism for every $q$.

## Proof

Choose compatible algebraic closures $\bar k\subseteq\bar k'$. Since $k$
and $k'$ are separably closed, by [lem-pc-kbar-pure-insep] $\bar k/k$ and $\bar k'/k'$ are purely
inseparable. Their spectrum maps are universal homeomorphisms ([lem-pc-homeo-pure-insep]); the explicit
site equivalence and covering compatibility give the vertical isomorphisms
in

$$
\begin{CD}
H^q(C,F) @>>> H^q(C_{k'},F|)\\
@V{\sim}VV @VV{\sim}V\\
H^q(C_{\bar k},F|) @>>> H^q(C_{\bar k'},F|).
\end{CD}
$$

The lower arrow is an isomorphism by the algebraically closed case. The
square commutes because each route pulls a representative cocycle through
the same composite field map; identity and composition compatibility of the
site equivalence identify the two pullbacks. The upper arrow is therefore
an isomorphism. In particular spectra of separably closed fields, which are
strictly henselian local schemes, introduce no additional stalk ambiguity.
