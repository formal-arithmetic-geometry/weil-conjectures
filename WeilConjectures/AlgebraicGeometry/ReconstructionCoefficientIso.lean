/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerInjectiveComponents
public import WeilConjectures.ProperBaseChange.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.Algebra.Homology.RestrictedTowerResolution.RestrictedTowerResolutionAcyclicity
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.Algebra.Homology.SequenceProjection.SequenceProjectionDerivedAdjunction

/-! # The normalized section-ring coefficient comparison

Source: latest blueprint, sk-def-sp-coefficient-towers, coefficient-limit paragraph
(blueprint: lem-sp-reconstruction-coefficient-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory
open scoped TensorProduct CategoryTheory.Obj
open CategoryTheory.MonObj
open AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] upperStarFromPoint HasDerivedCategory.standard
local instance reconstructionSiteSmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{u, u, u + 1} _

local instance reconstructionComm (T : Scheme.{u})
    (S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) :
    IsCommMonObj ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)) := by
  apply Sheaf.isCommMonObj_sheafCompose_obj
  intro U a b
  exact @mul_comm (S.obj.obj U) inferInstance a b

set_option maxHeartbeats 800000 in
-- Comparing the section-ring operations unfolds the monoidal inclusion.
private def recoverSectionRing (T : Scheme.{u})
    (S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) :
    InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology T)
      ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)) ≅ S := by
  let A := (sheafCompose (Scheme.ProEt.topology T)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
  letI : MonObj A.obj := (S.obj ⋙ forget₂ CommRingCat RingCat).monObjCompForget₂
  let R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology T) A
  have hone (U : T.ProEtᵒᵖ) :
      @One.one _ (CommRingCat.commRing (R.obj.obj U)).toOne =
        @One.one _ (CommRingCat.commRing (S.obj.obj U)).toOne := by
    change (((Functor.LaxMonoidal.ε (sheafToPresheaf (Scheme.ProEt.topology T) Ab)) ≫
      (sheafToPresheaf (Scheme.ProEt.topology T) Ab).map (η[A])).app U).hom
        (ULift.up 1) = _
    rw [Sheaf.ε_comp_map_one A]
    change (@AddCommGrpCat.ringMonObj (S.obj.obj U)
      (CommRingCat.commRing (S.obj.obj U)).toRing).one.hom (ULift.up 1) = _
    exact (@AddCommGrpCat.ringMonObj_one_apply (S.obj.obj U)
      (CommRingCat.commRing (S.obj.obj U)).toRing (ULift.up 1)).trans (by
        exact Int.cast_one)
  have hmul (U : T.ProEtᵒᵖ) (a b : S.obj.obj U) :
      @Mul.mul _ (CommRingCat.commRing (R.obj.obj U)).toMul a b =
        @Mul.mul _ (CommRingCat.commRing (S.obj.obj U)).toMul a b := by
    change (((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology T) Ab) A A) ≫
      (sheafToPresheaf (Scheme.ProEt.topology T) Ab).map (μ[A])).app U).hom
        (a ⊗ₜ[ℤ] b) = _
    rw [Sheaf.μ_comp_map_mul A]
    change (AddCommGrpCat.ringMonObj (S.obj.obj U)).mul.hom (a ⊗ₜ[ℤ] b) = _
    exact AddCommGrpCat.ringMonObj_mul_tmul (S.obj.obj U) a b
  let f : (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology T) A) ⟶ S :=
    ⟨{ app := fun U ↦ CommRingCat.ofHom
        (R := (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology T) A).obj.obj U) (S := S.obj.obj U)
        { toFun := fun x ↦ x
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl
          map_one' := hone U
          map_mul' := hmul U }
       naturality := by intros; ext x; rfl }⟩
  let g : S ⟶ (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology T) A) :=
    ⟨{ app := fun U ↦ CommRingCat.ofHom
        (R := S.obj.obj U) (S := (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology T) A).obj.obj U)
        { toFun := fun x ↦ x
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl
          map_one' := (hone U).symm
          map_mul' := fun a b ↦ (hmul U a b).symm }
       naturality := by intros; ext x; rfl }⟩
  exact ⟨f, g, by ext U x; rfl, by ext U x; rfl⟩

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The unique internal ring comparison lifts to the actual section-ring comparison,
retaining all quotient maps. Source: sk-def-sp-coefficient-towers, coefficient-limit
paragraph (blueprint: lem-sp-reconstruction-coefficient-iso).

Proof: take the unique reduction-normalized internal comparison. Apply monoidal
inclusion into presheaves, the pointwise commutative-monoid equivalence, and the
commutative-ring reconstruction functor. Reconstructing the underlying internal
ring of a sheaf of commutative rings recovers its section rings: the sheafification
unit and multiplication comparison identities prove that the identity on sections
preserves one and multiplication. Compose with this recovery isomorphism. Its
underlying abelian map is the original comparison, so both uniqueness normalization
and every quotient identity are retained. -/
theorem spReconstructionCoefficientIso :
    spCondensedCoefficientLimitComparison l E T ∧
    ∃ b : spReconstructionBase l E T ≅ spCompletedCommRing l E T,
      spReconstructionCoefficientNormalized l E T b := by
  have hc := (spCompletedTowerRoos l E T).1
  let e := hc.exists.choose
  have he := hc.exists.choose_spec
  have : IsMonHom e.hom := he.1
  have : IsMonHom e.inv := he.2.1
  let ep := (Monoidal.commMonFunctorCategoryEquivalence T.ProEtᵒᵖ Ab.{u + 1}).functor.mapIso
      ((sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1}).mapCommMon.mapIso
        (CommMon.mkIso' e))
  let es := Functor.isoWhiskerRight ep InternalAbelianSheafModule.commMonToRing
  let bs : spReconstructionBase l E T ≅
      InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology T) (spCompletedRingAb l E T) :=
    { hom := ⟨es.hom⟩
      inv := ⟨es.inv⟩
      hom_inv_id := by ext1; exact es.hom_inv_id
      inv_hom_id := by ext1; exact es.inv_hom_id }
  let b := bs ≪≫ recoverSectionRing T (spCompletedCommRing l E T)
  have hb : (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso b = e := by
    apply Iso.ext
    ext U x
    rfl
  refine ⟨hc, b, ⟨hc, hb⟩, ?_⟩
  intro n
  have hf := congrArg Iso.hom hb
  change (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (b.hom ≫ (spCompletedCoefficientMap l E T).app (op n)) = _
  change (sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})).map b.hom = e.hom at hf
  rw [Functor.map_comp, hf]
  exact he.2.2 n

end AlgebraicGeometry.ProEtale
