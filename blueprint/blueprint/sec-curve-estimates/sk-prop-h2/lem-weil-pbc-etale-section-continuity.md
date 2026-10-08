+++
id = "lem-weil-pbc-etale-section-continuity"
kind = "lemma"
title = "Continuity of sections at an inverse limit"
order = 951
uses = ["def-weil-pbc-etale-sheaves", "def-weil-pbc-inverse-image", "def-weil-pbc-scheme-conventions", "lem-weil-pbc-etale-finite-data-descent"]
+++
Let $X=\varprojlim_jX_j$ be as in the quasi-compact quasi-separated
[def-weil-pbc-scheme-conventions] setting above. Let $F_i$ be an abelian
etale sheaf on $X_i$, and let $F_j,F$ be its inverse images
[def-weil-pbc-inverse-image]. Then

$$
 \varinjlim_{j\geq i}F_j(X_j)\xrightarrow{\sim}F(X).
$$

The same formula holds on every etale finite-presentation object $W_j\to X_j$,
with $W=X\times_{X_j}W_j$.

## Proof

Work on the basis of quasi-compact quasi-separated etale objects of finite
presentation. By [lem-weil-pbc-etale-finite-data-descent], every basis object
and every finite covering diagram descend to a stage. Define on this basis

$$
 G(W)=\varinjlim_{k\geq j}F_k(W_k)
 \quad\text{if }W=W_j\times_{X_j}X.
$$

This is independent of the chosen presentation: an isomorphism between two
presentations and its inverse descend at a later stage, and so do the
identities and any equality of morphisms. The restriction maps are defined by
descending the relevant morphisms in the same way.

This presheaf is a sheaf. Indeed, a covering of a basis object has a finite
refinement by basis objects. Its equalizer diagram involves only finitely
many section groups, including the pairwise intersections. Descend that
finite covering diagram; filtered colimits commute with its finite products
and equalizer. The sheaf axiom for every $F_k$, in
[def-weil-pbc-etale-sheaves], is therefore the sheaf axiom for $G$.

To identify $G$, first fix a stage $j$. The inverse image of $F_i$ on $X_j$
is, by [def-weil-pbc-inverse-image], the sheafification of the presheaf of
sections on objects mapping to etale objects of $X_i$. Thus a section of
$F_j(W_j)$ is locally represented by such sections; equality of
representatives is also local. Only finite coverings are needed when $W_j$ is
quasi-compact. It follows that a section of $G(W)$ is locally represented by
the same inverse-image presheaf for $X\to X_i$. Conversely, the finitely many
objects, morphisms and equalities in any such local representation on $X$
descend by the cited finite-data lemma. They consequently define a section in
some $F_j(W_j)$; equality descends by the same argument. These two local
constructions give inverse morphisms between $G$ and the sheafified inverse
image $F$. Evaluating on $X$, or on $W$, gives the asserted formula.
