/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenDerivedScalarData

import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Normalized clopen scalar comparison

Source: Stacks Project, Tags 06YY and 0D6D.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t u w
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules SheafOfModules.SuccessiveDerivedQuotient
namespace AlgebraicGeometry.Scheme.ProEt.ClopenScalar
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] ClopenLocalization.modulesAbelian ClopenLocalization.hasDerived
attribute [-instance] ClopenLocalization.sheafify ClopenLocalization.locallyBijective

attribute [local irreducible] HasDerivedCategory.standard
open scoped ChangeOfRings

private def scalarRestrictionId {Z : Scheme.{t}}
    (R : Sheaf (topology Z) CommRingCat.{max u (t + 1)}) :
    restriction.{t + 1, t, max u (t + 1)} (𝟙 R) ≅ 𝟭 (Mods.{t, u} R) :=
  NatIso.ofComponents (fun M ↦ {
    hom := { val := {
      app := fun U ↦ ModuleCat.ofHom {
        toFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
      naturality := by intros; ext; rfl } }
    inv := { val := {
      app := fun U ↦ ModuleCat.ofHom {
        toFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
      naturality := by intros; ext; rfl } }
    hom_inv_id := by ext; rfl
    inv_hom_id := by ext; rfl
  }) (by intros; ext; rfl)

private def ordinaryUnit {Z : Scheme.{t}} {p : Presentations.{t, u} Z}
    (n : Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (C := Z.ProEt) (J := topology Z) (hD := derived.{t, u} Z) @p)
    (R : Sheaf (topology Z) CommRingCat.{max u (t + 1)}) :
    ext (Z := Z) (p (𝟙 R)) ≅ 𝟭 (Mods.{t, u} R) :=
  ((n.ordinaryAdjunction (𝟙 R)).ofNatIsoRight (scalarRestrictionId R)).leftAdjointUniq
    Adjunction.id

private theorem tensor_smul_one {Z : Scheme.{t}}
    {R S : Sheaf (topology Z) CommRingCat.{max u (t + 1)}} {a : R ⟶ S}
    (p : SheafOfModules.SuccessiveDerivedQuotient.Presentation.{t + 1, t,
      max u (t + 1), max (u + 1) (t + 2)}
      (C := Z.ProEt) (J := topology Z) (hD := derived.{t, u} Z) a)
    (M : Mods.{t, u} R) (U : Z.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    sectionTensor.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)} p M U s x =
      s • sectionTensor.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)} p M U 1 x := by
  let η := (PresheafOfModules.sheafificationAdjunction.{max u (t + 1), t, max u (t + 1), t + 1}
    (𝟙 (derivedChangeRingIndependentCoefficients (topology Z) S).obj)).unit.app
      (changeOfRingsPresheaf.{t, t + 1, max u (t + 1)}
        (J := topology Z) a M)
  change (eqToHom (p.obj_eq M).symm).val.app U
      (η.app U (s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x)) =
    s • (eqToHom (p.obj_eq M).symm).val.app U
      (η.app U ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x))
  rw [← ((eqToHom (p.obj_eq M).symm).val.app U).hom.map_smul]
  rw [← (η.app U).hom.map_smul]
  congr 2
  change s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x =
    (s * 1) ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x
  rw [mul_one]

private theorem ordinaryUnit_sections {Z : Scheme.{t}} {p : Presentations.{t, u} Z}
    (n : Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (C := Z.ProEt) (J := topology Z) (hD := derived.{t, u} Z) @p)
    (R : Sheaf (topology Z) CommRingCat.{max u (t + 1)})
    (M : Mods.{t, u} R) (U : Z.ProEtᵒᵖ) (x : M.val.obj U) (s : R.obj.obj U) :
    ((ordinaryUnit n R).hom.app M).val.app U
      (sectionTensor.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)} (p (𝟙 R)) M U s x) = s • x := by
  have h := congrArg (fun f ↦ f.val.app U x)
    (Adjunction.unit_leftAdjointUniq_hom_app
      ((n.ordinaryAdjunction (𝟙 R)).ofNatIsoRight (scalarRestrictionId R))
      Adjunction.id M)
  change ((ordinaryUnit n R).hom.app M).val.app U
    (((n.ordinaryAdjunction (𝟙 R)).unit.app M).val.app U x) = x at h
  rw [n.ordinary_unit] at h
  rw [tensor_smul_one, ((ordinaryUnit n R).hom.app M).val.app U |>.hom.map_smul, h]

private def identityHomotopyIso {Z : Scheme.{t}} {p : Presentations.{t, u} Z}
    (n : Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (C := Z.ProEt) (J := topology Z) (hD := derived.{t, u} Z) @p)
    (R : Sheaf (topology Z) CommRingCat.{max u (t + 1)}) :
    (p (𝟙 R)).ordinary.mapHomotopyCategory (.up ℤ) ≅
      𝟭 (HomotopyCategory (Mods.{t, u} R) (.up ℤ)) :=
  NatIso.ofComponents (fun H ↦
    (HomotopyCategory.quotient _ _).mapIso
      ((NatIso.mapHomologicalComplex (ordinaryUnit n R) (.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso (Mods.{t, u} R) (.up ℤ)).app H.as))
    (by
      rintro ⟨P⟩ ⟨Q⟩ ⟨f⟩
      simpa only [Iso.app_hom, Functor.map_comp, Functor.mapIso_hom, Functor.id_map,
        HomotopyCategory.quot_mk_eq_quotient_map, Functor.mapHomotopyCategory_map] using
        congrArg ((HomotopyCategory.quotient _ _).map)
          ((NatIso.mapHomologicalComplex (ordinaryUnit n R) (.up ℤ) ≪≫
            Functor.mapHomologicalComplexIdIso (Mods.{t, u} R) (.up ℤ)).hom.naturality f))

private def unitFactors {Z : Scheme.{t}} {p : Presentations.{t, u} Z}
    (n : Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (C := Z.ProEt) (J := topology Z) (hD := derived.{t, u} Z) @p)
    (R : Sheaf (topology Z) CommRingCat.{max u (t + 1)}) :
    DerivedCategory.Qh ⋙ 𝟭 (DerivedCategory (Mods.{t, u} R)) ≅
      (p (𝟙 R)).ordinary.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  DerivedCategory.Qh.rightUnitor ≪≫ DerivedCategory.Qh.leftUnitor.symm ≪≫
    (Functor.isoWhiskerRight (identityHomotopyIso n R) DerivedCategory.Qh).symm

private def derivedUnit {Z : Scheme.{t}} {p : Presentations.{t, u} Z}
    (n : Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (C := Z.ProEt) (J := topology Z) (hD := derived.{t, u} Z) @p)
    (R : Sheaf (topology Z) CommRingCat.{max u (t + 1)}) :
    extD (Z := Z) (p (𝟙 R)) ≅ 𝟭 (DerivedCategory (Mods.{t, u} R)) := by
  let ε := unitFactors n R
  let := (p (𝟙 R)).universal
  let := Functor.isLeftDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso (Mods.{t, u} R) (.up ℤ))
    (𝟭 (DerivedCategory (Mods.{t, u} R))) ε
  exact Functor.leftDerivedUnique (𝟭 _) (p (𝟙 R)).derived
    (p (𝟙 R)).counit ε.hom (HomotopyCategory.quasiIso _ (.up ℤ))

private theorem derivedUnit_hom_app {Z : Scheme.{t}} {p : Presentations.{t, u} Z}
    (n : Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (C := Z.ProEt) (J := topology Z) (hD := derived.{t, u} Z) @p)
    (R : Sheaf (topology Z) CommRingCat.{max u (t + 1)})
    (H : HomotopyCategory (Mods.{t, u} R) (.up ℤ)) :
    (derivedUnit n R).hom.app (DerivedCategory.Qh.obj H) =
      (p (𝟙 R)).counit.app H ≫ DerivedCategory.Qh.map
        ((identityHomotopyIso n R).hom.app H) := by
  let ε := unitFactors n R
  let := (p (𝟙 R)).universal
  let := Functor.isLeftDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso (Mods.{t, u} R) (.up ℤ)) (𝟭 _) ε
  have h := Functor.leftDerivedNatTrans_app (p (𝟙 R)).derived (𝟭 _)
    (p (𝟙 R)).counit ε.hom (HomotopyCategory.quasiIso _ (.up ℤ)) (𝟙 _) H
  change (derivedUnit n R).hom.app (DerivedCategory.Qh.obj H) ≫ ε.hom.app H =
    (p (𝟙 R)).counit.app H ≫ 𝟙 _ at h
  rw [Category.comp_id] at h
  apply (cancel_mono (ε.hom.app H)).1
  rw [h]
  simp only [ε, unitFactors, Iso.trans_hom, NatTrans.comp_app,
    CategoryTheory.Functor.rightUnitor_hom_app,
    CategoryTheory.Functor.leftUnitor_inv_app, Iso.symm_hom,
    CategoryTheory.Functor.isoWhiskerRight_inv,
    CategoryTheory.Functor.whiskerRight_app]
  dsimp only [CategoryTheory.Functor.id_obj, CategoryTheory.Functor.id_map]
  simp only [Category.id_comp, Category.assoc]
  erw [Category.id_comp]
  rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).symm

/-- Scalar identity extension has its canonical multiplication unit, and its derived
unit is the image of multiplication through the universal computation counit.
Source: Stacks Project, Tag 0D6D, identity case of derived pullback composition.
(blueprint: lem-pur-clopen-scalar-unit-normalization).

Proof: scalar restriction along the identity is naturally the identity, section by
section. Uniqueness of left adjoints therefore identifies ordinary extension with
the identity. The adjunction unit is 1 tensor x, so linearity gives s tensor x maps
to sx. Pass multiplication to complexes and homotopy categories. Its inverse,
followed by Qh, makes the identity derived functor a left derived functor. Uniqueness
of left derived functors identifies the recorded presentation with this functor.
The defining counit equation gives the asserted representative formula after
conjugating by the canonical quotient-to-derived comparison. -/
theorem clopen_scalar_unit_normalization {Z : Scheme.{t}} {p : Presentations.{t, u} Z}
    (n : Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (C := Z.ProEt) (J := topology Z) (hD := derived.{t, u} Z) @p) :
    Nonempty (Units.{t, u} @p) := by
  refine ⟨{ ordinary := ordinaryUnit n
            sections := ordinaryUnit_sections n
            derived := derivedUnit n
            representative := ?_ }⟩
  intro R P hP hf
  have hn := (derivedUnit n R).hom.naturality
    ((DerivedCategory.quotientCompQhIso (Mods.{t, u} R)).hom.app P)
  change (p (𝟙 R)).derived.map _ ≫ (derivedUnit n R).hom.app
      (DerivedCategory.Q.obj P) = (derivedUnit n R).hom.app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫ _ at hn
  rw [derivedUnit_hom_app] at hn
  rw [← cancel_epi ((p (𝟙 R)).derived.map
    ((DerivedCategory.quotientCompQhIso (Mods.{t, u} R)).hom.app P))]
  rw [hn]
  let f := (NatIso.mapHomologicalComplex (ordinaryUnit n R) (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso (Mods.{t, u} R) (.up ℤ)).hom.app P
  change (_ ≫ DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ _).map f)) ≫ _ = _
  dsimp only [CategoryTheory.Functor.id_map]
  rw [Category.assoc]
  erw [DerivedCategory.quotientCompQhIso_hom_naturality]
  unfold computation
  simp only [Category.assoc]
  erw [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  have he : ((p (𝟙 R)).ordinary.mapHomotopyCategoryFactors (.up ℤ)).hom.app P = 𝟙 _ := rfl
  rw [he]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  congr 1
  exact (Category.id_comp _).symm

end AlgebraicGeometry.Scheme.ProEt.ClopenScalar
