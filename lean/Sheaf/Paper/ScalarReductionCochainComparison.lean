/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import all Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel

/-! # Independence of the cochain and homotopy presentations of scalar reduction
(blueprint: lem-pod-scalar-reduction-cochain-comparison) -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace WeilConjectures
local instance scalarCochainSiteSmall (Y : AlgebraicGeometry.Scheme.{u}) :
    EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0} _
local instance scalarCochainAbSheafify (Y : AlgebraicGeometry.Scheme.{u}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} Y
local instance scalarCochainAbLocallyBijective (Y : AlgebraicGeometry.Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} := integralCoefficientAbLocallyBijective.{u, u} Y

/-- The cochain universal model and the prescribed homotopy-category scalar reduction
are the same derived functor up to natural isomorphism.

Proof: both ordinary functors have the specified sheafified tensor objects and maps,
so the object identifications give a natural isomorphism. Precompose the homotopy
universal counit with the full, essentially surjective homotopy quotient and transport
through the localization comparison. This is a pointwise right Kan extension on
cochains. Uniqueness of left derived functors now identifies the two derived functors.
Source: Stacks Tags 05SV and 06YY.
(blueprint: lem-pod-scalar-reduction-cochain-comparison) -/
theorem scalarReductionCochainModel_iso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    (M : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2}
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (O := completedIntegralCommRingSheafUnrestricted l E Y)
      (S := integralCoefficientCommRingSheaf l E Y n)
      (WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E Y n)) :
    Nonempty (M.T ≅ scalarReductionDerivedExtension l E Y n) := by
  have := M.additive
  let A := scalarReductionSource l E Y
  let B := scalarReductionTarget l E Y n
  let E₀ := scalarReductionExtension l E Y n
  let : E₀.Additive := scalarReductionExtensionAdditive l E Y n
  have hobj := (scalarReductionExistence l E Y n).choose_spec.choose
  have hmap := @(scalarReductionExistence l E Y n).choose_spec.choose_spec.choose
  let e : M.E ≅ E₀ := NatIso.ofComponents
    (fun X ↦ eqToIso (M.obj_eq X) ≪≫ (eqToIso (hobj X)).symm) (by
      intro X X' f
      dsimp
      erw [M.map_eq, hmap]
      simp)
  let T := scalarReductionDerivedExtension l E Y n
  let ε := scalarReductionCounit l E Y n
  let F := E₀.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let : F.HasPointwiseLeftDerivedFunctor (HomotopyCategory.quasiIso A (.up ℤ)) :=
    (scalarReductionExistence l E Y n).choose_spec.choose_spec.choose_spec.choose_spec.2.1
  let : T.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ)) :=
    (scalarReductionDerivedExistence l E Y n).choose_spec.choose_spec.1
  let q := HomotopyCategory.quotient A (.up ℤ)
  let α := (Functor.associator q DerivedCategory.Qh T).hom ≫ Functor.whiskerLeft q ε
  have hα := pointwise_precomp_full q DerivedCategory.Qh F T ε
    (Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor T ε
      (HomotopyCategory.quasiIso A (.up ℤ)))
  let i := DerivedCategory.quotientCompQhIso A
  let j : q ⋙ F ≅ M.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E₀.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B) ≪≫
      Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e.symm (.up ℤ)) _
  let β := Functor.whiskerRight i.inv T ≫ α ≫ j.hom
  have hβ := pointwise_change_iso T i j α hα
  let : T.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso A (.up ℤ)) :=
    ⟨hβ.isRightKanExtension⟩
  let := M.universal
  exact ⟨Functor.leftDerivedUnique T M.T M.ε β
    (HomologicalComplex.quasiIso A (.up ℤ))⟩

end WeilConjectures
