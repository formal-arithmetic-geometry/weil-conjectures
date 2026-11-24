/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwistConstructionsSupplement

import WeilConjectures.AlgebraicGeometry.Sp.SpRootBasisTowerComparison
import WeilConjectures.AlgebraicGeometry.Sp.SpSliceScalarExtensionBasis

/-! # Local bases from a prescribed compatible root tower -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u c v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency true in
private def sectionUnitIso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    [MonObj R] [IsCommMonObj R] :
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) R).functor.obj (Mod.regular R) ≅
        SheafOfModules.unit.{u, u + 1, u + 1} ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
              (Scheme.ProEt.topology X) R)) := by
  let F := (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) R).functor
  let i : (F.obj (Mod.regular R)).val ≅
      (SheafOfModules.unit.{u, u + 1, u + 1} _).val :=
    PresheafOfModules.isoMk
      (fun _ ↦ ModuleCat.isoMk (Iso.refl _) (by intro r; ext x; rfl))
      (by intro U V f; rfl)
  exact
    { hom := ⟨i.hom⟩
      inv := ⟨i.inv⟩
      hom_inv_id := SheafOfModules.hom_ext i.hom_inv_id
      inv_hom_id := SheafOfModules.hom_ext i.inv_hom_id }

set_option backward.isDefEq.respectTransparency true in
private def overIsLimit (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}) (W : X.ProEt)
    {D : ℕᵒᵖ ⥤ SheafOfModules.{u + 1} R} {c : Cone D} (hc : IsLimit c) :
    IsLimit ((SheafOfModules.overFunctor R W).mapCone c) := by
  apply isLimitOfReflects (SheafOfModules.forget (R.over W))
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro V
  exact isLimitOfPreserves (SheafOfModules.evaluation R (op V.unop.left)) hc

set_option backward.isDefEq.respectTransparency true in
private def sectionOverIsLimit {C : Type c} [Category.{v} C] (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}) (W : X.ProEt)
    (A : C ≌ SheafOfModules.{u + 1} R)
    {D : ℕᵒᵖ ⥤ C} {c : Cone D} (hc : IsLimit c) :
    IsLimit ((SheafOfModules.overFunctor R W).mapCone (A.functor.mapCone c)) :=
  overIsLimit X R W (isLimitOfPreserves A.functor hc)

/-- On one slice with a normalized compatible root basis, the integral limit and its
rational scalar extension are free of rank one over the constructed coefficients. -/
theorem spIntegralRationalRootBasis
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : X, Invertible (ℓ : X.residueField x)] (W : X.ProEt)
    (ζ : ∀ n : ℕ, (Scheme.purTwistRootsModule X ℓ n).val.obj (op W))
    (e : ∀ n : ℕ,
      (SheafOfModules.unit (Scheme.purTwistRing X (Scheme.purTwistFiniteRing X ℓ n))).over W ≅
        (Scheme.purTwistRootsModule X ℓ n).over W)
    (hζ : ∀ n : ℕ,
      (Scheme.proEtaleRootsOfUnityTransition X (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
        (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
        (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))).hom.app (op W) (ζ (n + 1)) = ζ n)
    (he : ∀ (n : ℕ) (V : (Over W)ᵒᵖ)
      (a : ((Scheme.purTwistRing X (Scheme.purTwistFiniteRing X ℓ n)).over W).obj.obj V),
      (e n).hom.val.app V a =
        a • (Scheme.purTwistRootsModule X ℓ n).val.map V.unop.hom.op (ζ n))
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    Nonempty ((spSignedTwist X _ (spIntegralTwist X ℓ E) 1).over W ≅
      (spSignedTwist X _ (spIntegralTwist X ℓ E) 0).over W) ∧
    Nonempty ((spSignedTwist X _ (spRationalTwist X ℓ E) 1).over W ≅
      (spSignedTwist X _ (spRationalTwist X ℓ E) 0).over W) := by
  let R := condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X
  let S : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1} :=
    (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) R)
  let A : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R ≌
      SheafOfModules.{u + 1} S :=
    InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) R
  let O := SheafOfModules.overFunctor S W
  obtain ⟨t⟩ := spRootBasisTowerComparison X ℓ W ζ e hζ he E
  obtain ⟨hc⟩ := spEllCoefficientCone_isLimit X ℓ E
  let cT := O.mapCone (A.functor.mapCone (limit.cone (spIntegralTwistSystem X ℓ E)))
  let cC := O.mapCone (A.functor.mapCone (spEllCoefficientCone X ℓ E))
  have hT : IsLimit cT := sectionOverIsLimit X S W A
    (limit.isLimit (spIntegralTwistSystem X ℓ E))
  have hC : IsLimit cC := sectionOverIsLimit X S W A hc
  have t' : (spIntegralTwistSystem X ℓ E ⋙ A.functor) ⋙ O ≅
      (spEllCoefficientSystem X ℓ E ⋙ A.functor) ⋙ O := t
  have hT' := (IsLimit.postcomposeHomEquiv t' cT).symm hT
  let i := hT'.conePointUniqueUpToIso hC
  let j := (SheafOfModules.overFunctor _ W).mapIso (sectionUnitIso X R)
  let eI := i ≪≫ j
  constructor
  · exact ⟨eI⟩
  · exact spSliceScalarExtensionBasis X (padicIntegersToPadicSubfield X ℓ E)
      (spIntegralTwist X ℓ E) W eI

end AlgebraicGeometry.ProEtale
