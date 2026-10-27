/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.CategoryTheory.SemisimplicialRingedTotalCategory
import Sheaf.CategoryTheory.SemisimplicialEvaluationFreeAdjoint
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.CategoryTheory.DerivedCountableSumsExact
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.CategoryTheory.FunctorPreservesSequentialHomotopyColimit
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! # Realization of flat semisimplicial derived systems

Source: Stacks Project, spaces-simplicial.tex, Tags 0D9T and 0D9L,
with injective order maps only
(blueprint: lem-sfb-flat-semisimplicial-derived-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Bicategory

namespace CategoryTheory.SemisimplicialRingedTotal

variable {F : LocallyDiscrete (SemiSimplexCategoryᵒᵖ)ᵒᵖ ⥤ᵖ Cat.{u, u}}
  {D : CoherentSitePseudofunctor SemiSimplexCategoryᵒᵖ F}
  {R : RingDiagram D} {h : Presheaf.IsSheaf D.totalTopology R.presheaf}

/--
Source: Stacks Project, `spaces-simplicial.tex`, Tag 0D9T, lemma
`lemma-cartesian-module-derived-from-simplicial`, with the simplex maps restricted
to injective order maps (blueprint: lem-sfb-flat-semisimplicial-derived-realization).

Given exact module pullbacks and a compatible semisimplicial family in the component
unbounded derived categories, with vanishing negative self-Homs, the family is
realized by a cartesian object of the derived category of the total ringed site.
Proof, following the injective-order-map adaptation of Tags 0D9T and 0D9L:
1. Use lem-sfb-semisimplicial-evaluation-free-adjoint to form X_r = j_{r!} B_r.
The inverse face isomorphisms define its alternating boundary by adjunction.
Exactness identifies ordinary and derived pullback. In component m the alpha
summand maps to alpha delta_i by pullback of theta_delta_i inverse, with the
canonical composition comparison.
2. The two ways to omit vertices a < b have equal coefficient maps by the
cocycle. Their opposite alternating signs cancel, so the boundary squares to zero.
Check this by derived adjunction on the identity summand as well.
3. For i > j+2, adjunction identifies Hom(X_i[i-j-2], X_j) with the finite sum,
over injections [j] into [i], of Hom(B_i[i-j-2], f_alpha^* B_j). The theta_alpha
identify these targets with B_i, so negative self-Hom vanishing kills them.
The node lem-sfb-countable-postnikov-extension-comparison extends this complex to
compatible triangles Y_r -> X_r -> Y_{r-1} -> Y_r[1]. Set E_r = Y_r[r].
4. Exact filtered colimits of abelian sheaves, and the faithful exact module
forgetful functor preserving colimits, imply exact countable module sums.
lem-kun-derived-countable-sums-exact supplies their unbounded derived coproducts.
Take a telescope X of E_r, the cone of 1-successor on their coproduct, with zeroth
leg b : X_0 -> X. Evaluation preserves sums: module pullbacks are left adjoints,
and component sums with their induced transitions satisfy the systems universal
property. Termwise evaluation is exact and preserves cones and shifts.
lem-kun-functor-preserves-hocolim therefore identifies evaluation of this telescope
with the evaluated telescope, respecting its actual legs.
5. In component m identify e_m X_r by the sum of theta_alpha with A_{m,r}, the
sum of copies of B_m indexed by injections [r] into [m], zero for r > m.
The cocycle makes these identifications commute with the alternating boundaries.
For a complex K_m representing B_m form the finite total complexes T_{m,r},
with terms the sum of K_m^{q+n} over 0 <= n <= min(r,m) and injective simplices.
The differential is the face boundary plus (-1)^n d_K on simplex degree n.
The inclusions T_{m,r-1} -> T_{m,r} have quotient A_{m,r}[r]; the degreewise split
short exact sequence gives the triangles by lem-weil-pbc-complex-ses-triangle.
For Z_{m,r}=T_{m,r}[-r], multiply top projection by (-1)^{r(r-1)/2} and the face
map into the preceding top summand by (-1)^{r(r+1)/2+1}. Their composite is the
prescribed boundary; identifying with the shifted cone gives the Postnikov
triangles with connecting arrows the literal inclusions of total complexes.
6. The comparison obstruction groups Hom(e_m X_i[i-j-1], A_{m,j}) for i > j+1
vanish: they are finite sums of negative self-Homs of B_m. The Postnikov
comparison node extends the component identifications to an isomorphism of
systems, respecting the connecting arrows and the maps from e_m X_0.
For r > m the evaluated cone e_m X_r[r] is zero, so the evaluated tower is
stationary. lem-sfb-sequential-telescope-calculus makes its actual mth leg an
isomorphism. Compose its inverse with the comparison to T_{m,m} and the fold
augmentation to B_m to obtain gamma_m.
7. The fold augmentation is a homotopy equivalence even for unbounded K_m.
On the augmented simplex complex, prepend vertex 0 when the first vertex is
positive, and use zero when it is 0; send augmented degree -1 to vertex 0.
The alternating boundary gives boundary h + h boundary = 1. On the total
complex the vertical terms cancel because (-1)^{n+1}+(-1)^n=0. This contracts
the augmentation onto the vertex-zero copy of K_m, proving gamma_m invertible.
8. On every vertex summand nu the construction gives gamma_m e_m(b) iota_nu
= theta_nu. Naturality of b and the cocycle show that the two sides of the
transition square agree after precomposition with the pullback of
 e_m(b) iota_nu. This is invertible since its composite with gamma_m is
 theta_nu. Cancel it to prove every displayed intertwining equation. Each
transition is then invertible, giving P.IsCartesian X. No amplitude or
quasi-coherence restriction occurs in this argument.
-/
theorem flat_semisimplicial_derived_realization
    (P : Presentation R h)
    (exact : ∀ {i j : SemiSimplexCategoryᵒᵖ} (a : i ⟶ j),
      PreservesFiniteLimits (P.pullback a).ordinary ∧
        PreservesFiniteColimits (P.pullback a).ordinary)
    (B : ∀ i : SemiSimplexCategoryᵒᵖ, (R.fibre i).D)
    (theta : ∀ {i j : SemiSimplexCategoryᵒᵖ} (a : i ⟶ j),
      (P.pullback a).derived.obj (B j) ≅ B i)
    (theta_id : ∀ i : SemiSimplexCategoryᵒᵖ,
      (theta (𝟙 i)).hom = (P.identity i).derived.hom.app (B i))
    (theta_comp : ∀ {i j k : SemiSimplexCategoryᵒᵖ}
      (a : i ⟶ j) (b : j ⟶ k),
      (theta (a ≫ b)).hom =
        (P.composition a b).derived.hom.app (B k) ≫
          (P.pullback a).derived.map (theta b).hom ≫ (theta a).hom)
    (negative_self_hom : ∀ i : SemiSimplexCategoryᵒᵖ, ∀ (t : ℤ), t < 0 →
      ∀ (f : B i ⟶ (B i)⟦t⟧), f = 0) :
    ∃ (X : (R.total h).D)
      (e : ∀ i : SemiSimplexCategoryᵒᵖ, (P.evaluation i).derived.obj X ≅ B i),
      P.IsCartesian X ∧
        ∀ {i j : SemiSimplexCategoryᵒᵖ} (a : i ⟶ j),
          (P.derivedTransition a).app X ≫ (e i).hom =
            (P.pullback a).derived.map (e j).hom ≫ (theta a).hom := by
  sorry

end CategoryTheory.SemisimplicialRingedTotal
