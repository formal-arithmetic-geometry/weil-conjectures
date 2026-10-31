/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerShriekData
import WeilConjectures.AlgebraicGeometry.SmoothPurityStrictBaseCoordinates
import WeilConjectures.AlgebraicGeometry.SmoothPurityStrictGeometricCoordinates
import WeilConjectures.AlgebraicGeometry.SmoothPurityStrictOpenTensorCoordinates

/-! # Constant-section coordinates for strict quotient towers

Source: Zheng Construction 4.1 and Lemma 4.10; blueprint tower operations proof (2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Constant-section coordinates and ordinary geometric operations, before imposing
three-index scalar/tensor or coefficient-mate coherence.
Source: blueprint `sk-lem-sp-tower-bound-operations.proof.md` (2), realization of
ordinary tower operations; Zheng Construction 4.1 and Lemma 4.10; Stacks 07A4, 06YS.
(blueprint: lem-sp-strict-coordinates-existence).

Proof: factor ell as a unit times a positive power of the specified uniformizer.
The equality of principal ideals and its powers identify the actual ell-power
quotients with finite positive uniformizer quotients. Rebundle the actual product-site
module presheaves as module sheaves for the vertical sequence topology. This changes
only the sheaf-condition proof, so sections, restrictions, and linear maps are fixed.
Construct the scalar and K-flat tensor calculus on this ringed sequence site and the
ordinary inverse and direct images from the actual constant quotient sheaves. Use the
same level constructions for every scheme, so the target calculus is the selected
source-scheme calculus. The constant-ring section comparisons transport both level
functors and their adjunction together. Apply semilinearDerivedSections with these
constructions, retaining the system calculus and its Hom reduction formula. Localize
ordinary inverse image termwise and derive direct image on K-injective system
resolutions; this gives Geometry with its ordinary and derived evaluation identities.
Ordinary inverse-image composition gives ordinaryComp; its exact localization is comp,
and localization of the ordinary evaluation equation gives comp_evaluation. Extension
by zero on the sequence site supplies Open, with its level adjunction normalized by
the same constant-section maps. The normalized open tensor comparison is the transpose
of inverse-image tensor comparison and the open unit; openTensorNormalization proves
it invertible and supplies openTensor_mate. Assemble Base and Operations. This step
constructs coordinates only and asserts neither three-index equation. Identity maps,
empty schemes, zero complexes, and ramified coefficient extensions are included. -/
theorem strictCoordinatesExistence :
    ∃ b : Base l E, ∃ _o : Operations l E b,
      ∀ T : Scheme.{u},
        ∃ s : SemilinearSections.SemilinearDerivedSectionsData.{u + 1, u, u + 1}
          (Scheme.ProEt.topology T) (B l E T) (tau l E T),
          s.systems = b.calculus T := by
  classical
  obtain ⟨b, hs⟩ := strictBaseCoordinates l E
  obtain ⟨geometry, ordinaryComp, hcomp⟩ := strictGeometricCoordinates l E b
  have hOpen (U T : Scheme.{u}) (j : U ⟶ T) [hj : IsOpenImmersion j] :
      ∃ o : Open l E b j (geometry j), ∀ (K : D l E U) (L : D l E T),
        IsIso ((o.derivedAdjunction.homEquiv _ _).symm
          ((tensor l E b U).map (Prod.mkHom (o.derivedAdjunction.unit.app K) (𝟙 _)) ≫
            (geometry j).tensorPullback.inv.app ((openD l E b o).obj K, L))) :=
    strictOpenTensorCoordinates l E b j (geometry j)
  choose opens hopen using hOpen
  let openOp : ∀ {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j],
      Open l E b j (geometry j) := fun {_ _} j hj ↦ @opens _ _ j hj
  let openTensor : ∀ {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
      (K : D l E U) (L : D l E T),
      (tensor l E b T).obj ((openD l E b (openOp j)).obj K, L) ≅
        (openD l E b (openOp j)).obj
          ((tensor l E b U).obj (K, (pull l E b (geometry j)).obj L)) := by
    intro U T j hj K L
    letI := @hopen U T j hj K L
    exact (asIso (((openOp j).derivedAdjunction.homEquiv _ _).symm
      ((tensor l E b U).map
          (Prod.mkHom ((openOp j).derivedAdjunction.unit.app K) (𝟙 _)) ≫
        (geometry j).tensorPullback.inv.app ((openD l E b (openOp j)).obj K, L)))).symm
  refine ⟨b, {
    geometry := geometry
    openOp := openOp
    ordinaryComp := ordinaryComp
    comp := fun f g ↦ (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (ordinaryComp f g)
    comp_termwise := fun _ _ ↦ rfl
    comp_evaluation := hcomp
    openTensor := openTensor
    openTensor_mate := ?_ }, hs⟩
  intro U T j hj K L
  exact ((openOp j).derivedAdjunction.homEquiv _ _).apply_symm_apply _

end AlgebraicGeometry.ProEtale.SpTowerShriek
