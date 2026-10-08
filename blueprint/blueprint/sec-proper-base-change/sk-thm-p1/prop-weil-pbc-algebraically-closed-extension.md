+++
id = "prop-weil-pbc-algebraically-closed-extension"
kind = "theorem"
title = "Algebraically closed extension for proper curves"
order = 1178
uses = ["def-weil-pbc-eight-curve-assertions", "def-weil-pbc-etale-sheaves", "def-weil-pbc-scheme-conventions", "lem-weil-pbc-curve-constructible-reduction", "lem-weil-pbc-curve-dense-open-localization", "lem-weil-pbc-zero-dimensional-field-extension", "lemma-weil-pbc-curve-filtered-cohomology", "lemma-weil-pbc-curve-locally-constant-reduction", "lemma-weil-pbc-eight-curve-devissage", "lemma-weil-pbc-finite-l-group-filtration", "lemma-weil-pbc-finite-pushforward-extension-zero", "lemma-weil-pbc-normalization-exact-sequence", "thm-sc-main"]
tags = ["latex:proposition"]
+++
Let $k\subset k'$ be algebraically closed, let $C$ be proper of dimension at
most one over $k$, and let $F$ be a torsion etale sheaf. Then

$$
 H^q(C,F)\xrightarrow{\sim}H^q(C_{k'},F|_{C_{k'}})
 \qquad(q\geq0).
$$

## Proof

The assertion is $\mathcal C_7(C,F)$ of
[def-weil-pbc-eight-curve-assertions]. By
[lem-weil-pbc-curve-constructible-reduction] the instances for reduced curves
with constructible $\mathbf F_r$-coefficients imply $\mathcal C_7(C,F)$. A
reduced scheme of finite type over $k$ with dimension at most one is the
disjoint union of its zero-dimensional irreducible components and its
one-dimensional components: there are finitely many components, and a
zero-dimensional irreducible component is a closed point contained in no other
component, so both unions are open and closed. The zero-dimensional union
satisfies the assertion by [lem-weil-pbc-zero-dimensional-field-extension].
Cohomology and pullback over a finite disjoint union are the products of those
on its components, so it remains to treat the pure one-dimensional union. Now
the dense-open localization of [lem-weil-pbc-curve-dense-open-localization]
and the extension-by-zero comparison of
[lemma-weil-pbc-finite-pushforward-extension-zero] reduce to the
sheaves $j_{a,!}\mathbf F_r$ on irreducible curves. On the normalization,
[lemma-weil-pbc-normalization-exact-sequence] transfers the assertion from the
smooth case, where [thm-sc-main] supplies it for
the constant sheaf; the locally constant reduction of
[lemma-weil-pbc-curve-locally-constant-reduction], using the filtration of
[lemma-weil-pbc-finite-l-group-filtration] and the trace splitting, passes from
the constant sheaf to finite locally constant sheaves. The short-exact
devissage of [lemma-weil-pbc-eight-curve-devissage] and the filtered cohomology
of [lemma-weil-pbc-curve-filtered-cohomology] assemble the assertion for
arbitrary torsion sheaves.
