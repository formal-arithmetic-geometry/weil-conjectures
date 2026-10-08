+++
id = "lem-weil-pbc-constructible-finite-pushforward-approximation"
kind = "lemma"
title = "Noetherian approximation for finite-pushforward embeddings"
order = 1131
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-direct-image", "def-weil-pbc-etale-sheaves", "def-weil-pbc-scheme-conventions", "lem-weil-pbc-constructible-finite-pushforward-noetherian", "lem-weil-pbc-etale-finite-data-descent", "lem-weil-pbc-etale-section-continuity"]
+++
Let $U$ be quasi-compact and quasi-separated and $C$ a constructible torsion
abelian sheaf on $U_{\Et}$. There is an affine inverse-system $U\cong\varprojlim
U_\lambda$ with Noetherian quasi-compact quasi-separated $U_\lambda$ and
affine transition maps, an index $\lambda$, a constructible torsion sheaf
$C_\lambda$ on $U_\lambda$ pulling back to $C$, and a finite-pushforward
embedding of $C_\lambda$ whose pullback is an embedding of $C$.

## Proof

*Step 1: the approximation.* A quasi-compact quasi-separated scheme is the
inverse limit $U=\varprojlim_\lambda U_\lambda$ of Noetherian quasi-compact
quasi-separated schemes with affine transition maps (absolute Noetherian
approximation, Stacks Project, Limits of Schemes, Tag
[01ZA](https://stacks.math.columbia.edu/tag/01ZA), Proposition 32.5.4).

*Step 2: the sheaf descends.* Constructibility of $C$ means that $U$ carries a
finite partition into locally closed constructible subschemes on each of which
$C$ is finite locally constant; a finite locally constant sheaf with finite
stalks is specified by finitely many etale finite-presentation objects,
finitely many sections and finitely many equalities expressing the
trivializations and the compatibility on the overlaps. By descent of
finite-presentation data at an inverse limit all of this datum descends: there
are an index $\lambda$, a finite family of etale finite-presentation objects
of $U_\lambda$, finitely many sections and equalities over $U_\lambda$, and a
covering condition, whose pullbacks to $U$ present $C$. This gives a
constructible torsion sheaf $C_\lambda$ on $U_\lambda$ with
$\nu_\lambda^*C_\lambda=C$.

*Step 3: the embedding descends.* Applying
[lem-weil-pbc-constructible-finite-pushforward-noetherian] to $C_\lambda$ on
the Noetherian $U_\lambda$ produces finite morphisms
$h_{\lambda,i}:V_{\lambda,i}\to U_\lambda$ and finite abelian groups $M_i$
with a monomorphism
$C_\lambda\hookrightarrow\bigoplus_i(h_{\lambda,i})_*\underline{M_i}$. A
finite morphism between finitely presented schemes is finitely presented, so
the source and target of this morphism are finite-presentation data; the same
descent lemma therefore applies a second time, and after increasing $\lambda$
there are finite morphisms $h_i:V_i\to U_\lambda$ and a morphism of sheaves
$C_\lambda\to\bigoplus_i(h_i)_*\underline{M_i}$ over $U_\lambda$ whose
pullback to $U$ is the embedding; since pullback is exact and reflects
monomorphisms, and since a monomorphism over $U_\lambda$ already holds there,
the descended map is a monomorphism.

*Step 4: the pullback is a monomorphism of $C$.* Pullback along $U\to
U_\lambda$ is exact, and for a finite morphism the formation of direct image
commutes with the affine base change $U\to U_\lambda$:
$\nu_\lambda^*(h_i)_*\underline{M_i}=(\nu_\lambda^*h_i)_*\underline{M_i}$,
which is the finite-base-change compatibility of the direct image applied to
the finite $h_i$. Hence the pullback of the descended monomorphism is the
required $C\hookrightarrow\bigoplus_i(h_i)_*\underline{M_i}$ on $U$, where
each $h_i$ is finite and finitely presented as the pullback of a finite
morphism between finitely presented schemes.

*Remark on the limits input.* Step 2 uses only the descent of
finite-presentation data at an inverse limit, and the identification
$h_*\underline M=\varinjlim_i(h_i)_*\underline M$ used in the Noetherian case
is the section formula $\varinjlim_i\underline M\bigl(W\times_UV_i\bigr)
=\underline M\bigl(W\times_UV\bigr)$ over the etale finite-presentation
objects $W\to U$. No separate limits statement is assumed.
