+++
id = "lemma-constructible-universal-homeomorphism-invariance"
kind = "lemma"
title = "Invariance under universal homeomorphisms"
order = 1168
lean = ["AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.of_upperStar", "AlgebraicGeometry.Scheme.IsFiniteSheaf.of_upperStar", "AlgebraicGeometry.Scheme.IsLocallyConstantSheaf.of_upperStar", "AlgebraicGeometry.Scheme.exists_comp_eq_of_surjective", "AlgebraicGeometry.Scheme.isFiniteLocallyConstantSheaf_upperStar_iff", "CategoryTheory.Sheaf.isConstant_upperStar_iff"]
uses = ["def-constructible-constant", "def-constructible-finite", "def-constructible-finite-locally-constant", "def-constructible-locally-constant", "def-kun-separably-closed", "lem-weil-pbc-closed-immersion-from-composite", "lemma-constructible-pullback-constant", "lemma-constructible-pullback-finite", "lemma-constructible-pullback-locally-constant", "lemma-nagata-affine-finite-type-is-quasi-affine", "lemma-openclosed-stalk-upperstar", "prop-constructible-pullback", "prop-weil-pbc-universal-homeomorphism-topos", "thm-weil-pbc-universal-homeomorphism-invariance"]
+++
Let $u\colon Z'\to Z$ be a universal homeomorphism. Then
$\mathcal G\in\shv{\et Z}$ is constant (locally constant) if and only if
$u^*\mathcal G$ is. If moreover $u$ is a surjective closed immersion, then
$\mathcal G$ is finite (finite locally constant) if and only if
$u^*\mathcal G$ is.

## Proof

The direction ``only if'' is
[lemma-constructible-pullback-locally-constant], [lemma-constructible-pullback-finite].
For the converse, base change along $u$ is an equivalence of sites
$\et Z\simeq\et{Z'}$ (Stacks Project, Tag `04DZ`), hence $u^*$ is an
equivalence of categories of sheaves
([thm-weil-pbc-universal-homeomorphism-invariance]). Constancy: $u^*$ is
fully faithful and carries constant sheaves to constant sheaves, so from
$u^*\mathcal G\cong u^*M_{Z}$ we get $\mathcal G\cong M_Z$. Local
constancy: let $(V'_i\to Z')_i$ be a trivialising étale cover of
$u^*\mathcal G$. Each $V'_i$ is isomorphic over $Z'$ to $V_i\times_ZZ'$
for an étale $V_i\to Z$, and the $V_i$ cover $Z$ since $u$ is
surjective. The projection $u_i\colon V_i\times_ZZ'\to V_i$ is a
universal homeomorphism, and $u_i^*(\mathcal G|_{V_i})\cong (u^*\mathcal G)|_{V'_i}$ is constant, so $\mathcal G|_{V_i}$ is constant
by the first part applied to $u_i$. Finiteness, for $u$ a surjective closed
immersion: the residue field maps of a closed immersion are surjective,
hence isomorphisms, so every geometric point $\bar z$ of $Z$ lifts to a
geometric point $\bar z'$ of $Z'$ with $u\circ\bar z'=\bar z$, and the
stalk of $\mathcal G$ at $\bar z$ is the stalk of $u^*\mathcal G$ at
$\bar z'$.
