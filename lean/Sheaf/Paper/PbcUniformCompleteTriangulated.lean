/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Sheaf.Paper.BoundedConstructibleComplete
public import Mathlib.CategoryTheory.Triangulated.Subcategory

import Sheaf.Paper.BoundedConstructibleTower
import Sheaf.Paper.IntrinsicCompletion
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf
import Sheaf.Paper.ConstantModuleSectionProperties
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.Paper.CompactSupportComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.DerivedGeometricStalkConservative
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.Paper.ProEtaleCanonicalTensorPullback
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.NormalizedConstructibleTowerLocalEffectivity

/-! # Triangulation of the compatible uniform integral category

Source: Weil blueprint, proper base change, constructible-complete restriction
(blueprint: lem-weil-pbc-uniform-complete-triangulated).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- The compatible uniform completed integral category is an isomorphism-closed
triangulated full subcategory of its actual ambient derived category.
Source: blueprint proper base change, constructible-complete restriction
(blueprint: lem-weil-pbc-uniform-complete-triangulated).
Proof plan, following the eight steps of the matching DAG node:

1. Write $B=A_T$ and $R_n=(P_n)_T$. The ambient category is $D(\operatorname{Mod}(B))$, with the
cone and shift conventions of [def-weil-abstract-derived-category]. Let
$\Phi(K)=K^{\wedge}_{\mathrm{Kos}}$ and $\eta_K:K\to\Phi(K)$ be the specified construction and
unit in [def-weil-pbc-intrinsic-completion]. This construction preserves zero and is functorial
on complexes and on the derived category: tensor by each finite free Koszul complex preserves
quasi-isomorphisms, and exact countable products preserve acyclic complexes, so the displayed
mapping-fiber construction does too. Its naturality is the componentwise identity $(\prod
f_m)(1-s)=(1-s')(\prod f_m)$. Hence completeness is invariant under ambient isomorphisms.
Membership in the tower condition is invariant under isomorphisms by composing its level
isomorphisms with the reductions of that isomorphism; their normalization squares commute by
naturality of coefficient reduction. Compose the witness isomorphisms in the same way. This
proves isomorphism closure of the full subcategory. Zero has zero local complexes, any interval
containing zero, the one-stratum partition when $T$ is nonempty (the empty partition when $T$ is
empty), and zero etale witnesses with the unique normalization maps; its completion map is the
identity of zero.

2. There is a uniform cohomological bound for the reductions of each object $K$ in our
subcategory, even though the tower definition initially bounds the terms of its local models.
Indeed, the constant sheaf functor is exact by
[lem-weil-pbc-constant-module-section-properties]. Since $A$ is a valuation subring of the field
$E$ and $\varpi\ne0$, the sequence $0\to A\xrightarrow{\varpi^n}A\to P_n\to0$ is exact for every
$n\geq1$. Flatness and the quotient identification in
[lem-weil-pbc-constant-completion-equivalence] turn this into $0\to B\xrightarrow{\varpi^n}B\to
R_n\to0$. Exact inverse image preserves this sequence on each stratum and each local covering
member, with the restricted coefficient ring; no equality with a newly completed coefficient
ring on that stratum is used. This is a length-one free resolution of the restricted $R_n$. If
$L$ is any defining local complex with terms only in $[d_0,d_1]$, then $L\otimes^L R_n$ is
represented by the total complex of $[L\xrightarrow{\varpi^n}L]$ in the two tensor degrees
$[-1,0]$, and is therefore zero outside $[d_0-1,d_1]$. This computes derived reduction because
the resolution is bounded and free. Thus the restrictions of $\mathcal H^q(K_n)$ vanish outside
this interval; inside it they are finite lisse by the tower definition, so the cohomology
sheaves are intrinsically constructible. To justify global vanishing, use the given etale
witness $\nu_T^*L_n\simeq K_n$. Exactness and the sheaf unit isomorphism of finite-level
comparison show that $\nu^*$ commutes with cohomology and detects zero sheaves. The
comparison-pullback isomorphism therefore implies $\mathcal H^q(L_n)$ vanishes on every stratum
for these $q$. Every geometric point belongs to a stratum, so etale stalk conservativity,
applied to $0\to\mathcal H^q(L_n)[0]$ after forgetting to abelian sheaves, gives global
vanishing. Exact inverse image then gives the asserted global bound for $K_n$.

3. For an integer $m$, derived reduction is exact and hence $(K[m])_n\simeq K_n[m]$. The same
local models shifted by $m$ have term window $[d_0-m,d_1-m]$ and finite-lisse reduction
cohomology $\mathcal H^q(K_n[m])=\mathcal H^{q+m}(K_n)$. Shift every normalization and every
witness $(L_n,\alpha_n,\beta_n)$; the witness compatibility equation is the original equation
shifted by $m$, with the canonical tensor-shift identification. In the completion model of step
1, tensor, products and the mapping fiber commute with shift, with the usual tensor-shift
identification. For the mapping fiber $F(C)^i=B(C)^i\oplus B(C)^{i-1}$, its comparison with
$F(C)[m]$ multiplies the second coordinate by $(-1)^m$; substitution in
$d_F(x,y)=(d_Bx,(1-s)x-d_By)$ checks it is a chain isomorphism. The unit becomes $\eta_K[m]$
under this identification, so it remains invertible. This verifies each defining clause for
$K[m]$, for positive, zero and negative $m$.

4. Fix an arbitrary ambient distinguished triangle $K\xrightarrow{u}L\to C\to K[1]$ with $K,L$
in the subcategory. The Koszul completion functor $\Phi$ of step 1 is exact: on complexes,
tensor by $Q_m$ distributes over the two cone summands and commutes with its differential;
products distribute over the two finite summands; and for the mapping fiber, write a degree-$i$
element of $F(\operatorname{Cone}(u))$ as $((l,k),(l',k'))$ with $l\in B_L^i$, $k\in B_K^{i+1}$,
$l'\in B_L^{i-1}$, $k'\in B_K^i$. The map $((l,k),(l',k'))\mapsto((l,l'),(k,-k'))$ identifies it
with $\operatorname{Cone}(F(u))$. Substitution in the two displayed differential formulas in the
cited definitions verifies the chain-map equation; the inverse regroups these coordinates and
negates the last one again. Thus the completion of a cone triangle is its cone triangle after
completion. Exact products ensure these computations descend through quasi-isomorphisms, as in
step 1. The unit on a cone is the block map induced by its units on the two summands, so the
three units form a morphism from the displayed triangle to its image under $\Phi$, including the
connecting arrow. The first two components are isomorphisms by completeness of $K,L$;
[lem-sf-triangle-morphism-iso] proves that $\eta_C$ is an isomorphism. Hence $C$ is derived
complete. This argument uses the specified Koszul completion unit, rather than an arbitrary
isomorphism between two limit objects.

5. Apply exact derived reduction to the triangle in step 4, obtaining $K_n\to L_n\to C_n\to
K_n[1]$ over the finite commutative ring $P_n$. Choose a common cohomological interval $[a,b]$
containing the two intervals furnished by step 2. By [lem-weil-proetale-dbc-triangulated], the
finite-level property of bounded intrinsically constructible cohomology is shift-stable and has
the stated outer-vertex closure. Rotate the reduced triangle to $L_n\to C_n\to K_n[1]\to L_n[1]$
and apply that closure: $C_n$ has intrinsically constructible cohomology. The long exact
cohomology sequence gives the sharper bound $\mathcal H^q(C_n)=0$ for $q\notin[a-1,b]$,
independent of $n$, since the two adjacent sheaves $\mathcal H^q(L_n)$ and $\mathcal
H^{q+1}(K_n)$ both vanish there. The normalized reduction tower of $C$ is the one defined by the
completed coefficient datum; it has its specified quotient cocycle. Thus we have a normalized
tower, levelwise constructibility and a single cohomological interval, not just separately
bounded levels.

6. Here are compatible etale witnesses for $C$, including the missing compatibility check for
arbitrary $u$. Write the given witnesses of $K_n,L_n$ as $E_n,F_n\in D^+(T_{\Et},P_n)$ with
isomorphisms $\alpha^K_n,\alpha^L_n$. Full faithfulness in [thm-weil-pbc-site-comparison] lifts
$(\alpha^L_n)^{-1}u_n\alpha^K_n$ to a unique $v_n:E_n\to F_n$. Choose a cone triangle of $v_n$
with third vertex $G_n$. The bounded-below subcategory is closed under cones, so $G_n\in D^+$.
Finite-level inverse image is exact and its termwise derived functor is triangulated; applying
it to this triangle and using TR3 with the first two witness isomorphisms gives
$\alpha_n:\nu_T^*G_n\simeq C_n$, by the two-isomorphism lemma. For $b\geq a$, tensor-pullback
compatibility identifies $\nu_T^*(G_b\otimes^L_{P_b}P_a)$ with $C_b\otimes^L_{P_b}P_a\simeq
C_a$. Before using bounded-below full faithfulness again, note that exact inverse image commutes
with all cohomology and detects zero sheaves by its sheaf unit. Therefore
$G_b\otimes^L_{P_b}P_a$ has the same bounded cohomological interval as $C_a$, and belongs to
$D^+$. Full faithfulness lifts the isomorphism $\alpha_a^{-1}\rho^C_{b,a}(\alpha_b\otimes^L
P_a)$ uniquely to an isomorphism $\beta_{b,a}:G_b\otimes^L_{P_b}P_a\simeq G_a$, lifting its
inverse as well. Its defining equality is exactly
$\alpha_a\nu^*(\beta_{b,a})=\rho^C_{b,a}(\alpha_b\otimes^L P_a)$. For three indices, applying
$\nu^*$ to the two composites of the $\beta$ gives the same map by the quotient cocycle of
$\rho^C$ and naturality of tensor-pullback; faithfulness makes those composites equal. All these
sources are bounded below by the same preceding check. This supplies the compatible witnesses
required in the definition without assuming functorial cones in an ordinary derived category.

7. Apply [lem-weil-pbc-normalized-constructible-local-effectivity] to the normalized reduction
tower of $C$ from step 5. Its hypotheses hold: $T$ is Noetherian, the coefficients are the given
completed adic datum, the reductions carry their $R_n$ actions and the quotient normalization
cocycle, every cohomology sheaf is intrinsically constructible, and $[a-1,b]$ is independent of
$n$. Its statement supplies the common finite stratification, pro-etale covers, bounded
adic-lisse finite-type local complexes and compatible local reduction isomorphisms required by
[def-weil-pbc-bounded-constructible-tower]. No assertion of local projectivity or finite Tor
dimension over the Artinian $P_n$ is needed. Together with completeness from step 4 and
compatible witnesses from step 6, these data prove $C\in\Dbc(T_{\Proet},A)$ by its definition.
The argument applied to an arbitrary ambient triangle, so every cone of every morphism between
the selected objects belongs.

8. We now verify the precise full-subcategory criterion, including the omitted middle-vertex and
additive checks. For a distinguished triangle $K\to L\to M\to K[1]$ with $K,M$ in the
subcategory, inverse rotation gives $M[-1]\to K\to L\to M$. Steps 3 and 7 imply $L$ lies in the
subcategory. If the known pair is $L,M$, rotate to $L\to M\to K[1]\to L[1]$, use step 7 and then
shift back. Thus every pair of vertices gives the third. Step 1 already proved ambient
isomorphism closure. For two objects $K,L$, the cone of the zero map $K[-1]\to L$ is $L\oplus
K$, by the explicit cone differential, so steps 3 and 7 imply closure under finite biproducts;
zero is present by step 1. The full subcategory consequently inherits the abelian-group
structure on Hom and these biproducts and is additive. Its shift is an autoequivalence, with
inverse the inherited shift by $-1$. All hypotheses of [def-weil-triangulated-subcategory] are
now satisfied, in the ambient triangulated derived category. Its statement supplies the
inherited distinguished triangles, the triangulated structure and exact inclusion. Explicitly
the inclusion uses the identity shift comparison and takes each inherited distinguished triangle
to that same ambient triangle. -/
theorem pbcIntegralUniformComplete_isTriangulated (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) [IsNoetherian T]
    (_hDim : ∃ d : ℕ, topologicalKrullDim T ≤ d)
    (_hInv : ∀ t : T, IsUnit (l : T.presheaf.stalk t)) :
    ObjectProperty.IsClosedUnderIsomorphisms.{u + 2, u + 2}
      (C := PbcCompletedDerived T (pbcIntegralDatum l E))
      (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) ∧
    ObjectProperty.IsTriangulated.{u + 2, u + 2}
      (C := PbcCompletedDerived T (pbcIntegralDatum l E))
      (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) := by
  sorry

end AlgebraicGeometry.Scheme
