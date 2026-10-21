/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q158
-/
module

public import Sheaf.TraceFormula.ComparisonInductionStep
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt

import Sheaf.CategoryTheory.GrothendieckSpectralSequence
import WeilConjectures.CategoryTheory.GrothendieckCocycleComparison
import WeilConjectures.CategoryTheory.GrothendieckBottomResolutionComparison
import Sheaf.CategoryTheory.SiteCohomologyPullback
import Sheaf.Paper.SiteHigherDirectImageSheafifiedPresheaf
import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.AlgebraicGeometry.ObjectCohomologyPresheafResolution
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Image of the next-degree topology comparison

Source: Stacks Project, Cohomology on Sites, Tag 0EZC and section-compare-general
(blueprint: lem-trf-comparison-next-degree-image).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite ZeroObject

namespace CategoryTheory.RefinedTopologyComparison

/-- The canonical comparison on object cohomology, obtained by exact finer
sheafification of extensions, then its counit. The generator arrow is the finer
sheafification of the coarser sheafification unit of the free representable.
Source: Stacks Project, Tag 0EZC, first sentence of proof; Tags 01F7--01FB
(blueprint: lem-trf-comparison-next-degree-image). -/
def comparisonCohomologyMap {C : Type u} [SmallCategory C]
    (J K : GrothendieckTopology C) (h : K ≤ J)
    (H : Sheaf J AddCommGrpCat.{u}) (n : ℕ) (U : C) :
    Sheaf.H' ((comparison J K h).direct.obj H) n U ⟶ Sheaf.H' H n U := by
  let e := comparison J K h
  letI := e.leftExact
  letI := e.adj.isLeftAdjoint
  letI := e.adj.left_adjoint_additive
  exact AddCommGrpCat.ofHom
    (((Abelian.Ext.mk₀ (e.adj.counit.app H)).postcomp _ (add_zero n)).comp
      (((Abelian.Ext.mk₀ ((presheafToSheaf J AddCommGrpCat.{u}).map
        (toSheafify K (yoneda.obj U ⋙ AddCommGrpCat.free)))).precomp _ (zero_add n)).comp
        (e.inverse.mapExtAddHom _ (e.direct.obj H) n)))

/-- The canonical comparison on the slice over `X`, evaluated on any slice object `U`.
Source: Stacks Project, Tag 0EZC and section-compare-general
(blueprint: lem-trf-comparison-next-degree-image). -/
def sliceComparisonCohomologyMap {C : Type u} [SmallCategory C]
    (τ τ' : Precoverage C) (hτ : τ' ≤ τ) (X : C)
    (H : Sheaf (τ.toGrothendieck.over X) AddCommGrpCat.{u}) (n : ℕ) (U : Over X) :
    Sheaf.H' ((sliceComparison τ τ' hτ X).direct.obj H) n U ⟶ Sheaf.H' H n U :=
  comparisonCohomologyMap (τ.toGrothendieck.over X) (τ'.toGrothendieck.over X)
    (fun _ _ hS ↦ Precoverage.toGrothendieck_mono hτ _ hS) H n U

/-- The next-degree comparison is injective, its image is exactly the classes
killed by a coarser covering, and it commutes with all restrictions in the slice.
Source: Stacks Project, Tag 0EZC, lemma-V-implies-cohomology-extra-general,
and section-compare-general (blueprint: lem-trf-comparison-next-degree-image).

Proof:
1. Set e = epsilon_X, G = e_*H and m = r + 1. Direct image leaves the
underlying presheaf unchanged, so G is already a finer sheaf and the counit
from its finer sheafification to H is an isomorphism.
2. Apply the Leray spectral sequence (sk-thm-groth-ss) in its Cartan--Eilenberg
realization (thm-sp-grothendieck). Abelian sheaves are constant-integer modules,
so lem-pur-ringed-site-grothendieck-abelian gives the Grothendieck hypotheses.
The double-complex spectral-sequence theorem gives the finite abutment filtration.
3. The band 1 <= q <= m - 1 vanishes. All differentials entering or leaving
(m,0) vanish, so E_2^(m,0) = E_infinity^(m,0). The intermediate graded pieces
in total degree m vanish. The convergence convention def-sp-convergence gives
F^1 H^m = F^m H^m = E_2^(m,0), and E_infinity^(0,m) embeds in E_2^(0,m).
Hence 0 -> H^m(G) -> H^m(H) -> (R^m e_*H)(X) is exact, including m = 1.
4. Resolve H by I and G by J. The adjoint of the resolution map e^-1 J -> I
is J -> e_*I. The bottom-resolution-comparison lemma identifies the first edge
with its section cohomology map. This is the pullback of
lem-weil-pbc-site-cohomology-pullback followed by the counit, equivalently the
exact-functor Ext construction `comparisonCohomologyMap` above.
5. The higher-direct-image sheafified-presheaf theorem identifies R^m e_*H
with the coarser sheafification of U |-> H^m(U,H). The cocycle-comparison lemma
lem-pc-grothendieck-cocycle-comparison identifies the second edge with that
sheafification unit: sections preserve kernels and every class has a cocycle.
6. Sheafification of its unit is invertible, so
lem-weil-pbc-site-sheafification-iso-locally-bijective makes the unit locally
injective. Its kernel is therefore the locally zero classes. Conversely, a
section of the sheaf vanishing on a covering is zero. Exactness proves the image
claim and the first-edge injection.
7. Fix the resolution comparison J -> e_*I. Its section maps commute with every
arrow in the slice. The object-cohomology-presheaf-resolution theorem identifies
these with the canonical cohomology restrictions. The pullback formula of
lem-weil-pbc-site-cohomology-pullback identifies all horizontal maps with the
same comparison, proving the final naturality equation independently of choices.
-/
theorem comparisonNextDegreeImage
    {C : Type u} [SmallCategory C]
    (τ τ' : Precoverage C)
    (hτsite : τ.IsSiteForCoverings) (hτ'site : τ'.IsSiteForCoverings)
    (hτ : τ' ≤ τ)
    (P : ∀ ⦃X Y : C⦄, (X ⟶ Y) → Prop)
    (A' : ∀ X : C, Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u} → Prop)
    (hzero : ∀ X : C, A' X 0)
    (hiso : ∀ (X : C) (H K : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u}),
      Nonempty (H ≅ K) → A' X H → A' X K)
    (hkernel : ∀ (X : C) (H K : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u})
      (f : H ⟶ K), A' X H → A' X K → A' X (kernel f))
    (hcokernel : ∀ (X : C) (H K : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u})
      (f : H ⟶ K), A' X H → A' X K → A' X (cokernel f))
    (hextension : ∀ (X : C)
      (S : ShortComplex (Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u})),
      S.ShortExact → A' X S.X₁ → A' X S.X₃ → A' X S.X₂)
    (hbaseChange : ∀ (X Y Y' : C) (f : X ⟶ Y), P f → ∀ g : Y' ⟶ Y,
      ∃ (T : C) (p : T ⟶ X) (q : T ⟶ Y'), IsPullback p q f g ∧ P q)
    (hrelocalization : ∀ (X Y : C) (f : X ⟶ Y)
      (H : Sheaf (τ'.toGrothendieck.over Y) AddCommGrpCat.{u}),
      A' Y H → A' X ((relocalization τ'.toGrothendieck f).inverse.obj H))
    (htauSheaf : ∀ (X : C) (H : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u}),
      A' X H → Presheaf.IsSheaf (τ.toGrothendieck.over X) H.obj)
    (hderivedImage : ∀ (X Y : C) (f : X ⟶ Y), P f →
      ∀ (H : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u}), A' X H →
        ∀ i : ℕ, A' Y (((relocalization τ'.toGrothendieck f).direct.rightDerived i).obj H))
    (r : ℕ)
    (hr : ∀ (X : C) (H : Sheaf (τ.toGrothendieck.over X) AddCommGrpCat.{u}),
      (∃ H' : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u},
        A' X H' ∧ Nonempty (H ≅ (sliceComparison τ τ' hτ X).inverse.obj H')) →
      ∀ i : ℕ, 1 ≤ i → i ≤ r →
        IsZero (((sliceComparison τ τ' hτ X).direct.rightDerived i).obj H))
    (X : C) (H : Sheaf (τ.toGrothendieck.over X) AddCommGrpCat.{u})
    (hH : ∃ H' : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u},
      A' X H' ∧ Nonempty (H ≅ (sliceComparison τ τ' hτ X).inverse.obj H')) :
    Function.Injective
      (sliceComparisonCohomologyMap τ τ' hτ X H (r + 1) (Over.mk (𝟙 X))) ∧
    (∀ ξ : Sheaf.H' H (r + 1) (Over.mk (𝟙 X)),
      (∃ η, sliceComparisonCohomologyMap τ τ' hτ X H (r + 1) (Over.mk (𝟙 X)) η = ξ) ↔
        ∃ (I : Type u) (U : I → C) (a : ∀ i, U i ⟶ X),
          Presieve.ofArrows U a ∈ τ' X ∧
          ∀ i, (H.cohomologyPresheaf (r + 1)).map
            (Over.homMk (a i) : Over.mk (a i) ⟶ Over.mk (𝟙 X)).op ξ = 0) ∧
    (∀ (U V : Over X) (f : U ⟶ V),
      (((sliceComparison τ τ' hτ X).direct.obj H).cohomologyPresheaf (r + 1)).map f.op ≫
          sliceComparisonCohomologyMap τ τ' hτ X H (r + 1) U =
        sliceComparisonCohomologyMap τ τ' hτ X H (r + 1) V ≫
          (H.cohomologyPresheaf (r + 1)).map f.op) := by
  sorry

end CategoryTheory.RefinedTopologyComparison
