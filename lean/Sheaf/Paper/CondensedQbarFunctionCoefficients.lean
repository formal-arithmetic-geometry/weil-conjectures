/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups H3 and B3
-/
module

public import Sheaf.Paper.CondensedQbarCoefficientConstruction

import all Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization
import Sheaf.Paper.GeometricFieldProEtaleEvaluation
import Sheaf.Paper.ProEtaleSheafificationWcontractibleSections
import WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import Sheaf.Paper.CondensedQbarScalarPullback
import Sheaf.Paper.CondensedQbarFieldFiberExtension

/-!
# Scalar functions and geometric evaluation for bounded condensed coefficients

Source: RefactorInstruction, Section 4, coefficient realization and geometric evaluation
(blueprint: lem-weil-pbc-condensed-qbar-function-coefficients).
-/

@[expose] public section

universe u v w z
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- Geometric fiber data, separating the constructed functors from their naturality proofs.
Source: RefactorInstruction, Section 4, geometric fibers
(blueprint: lem-weil-pbc-condensed-qbar-function-coefficients). -/
structure CondensedQbarFiberData (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) where
  /-- Geometric evaluation, after choosing an algebraic closure above the point. -/
  fiber (U : X.ProEt) (x : U.left) :
    Mod (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U.left) ⥤
        ModuleCat.{u + 1} (PadicAlgCl ℓ)
  fiber_additive (U : X.ProEt) (x : U.left) : (fiber U x).Additive
  fiber_colimits (U : X.ProEt) (x : U.left) : PreservesFiniteColimits (fiber U x)
  /-- The regular module has its ordinary one-dimensional coordinates. -/
  fiber_regular (U : X.ProEt) (x : U.left) :
    (fiber U x).obj (Mod.regular
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U.left)) ≃ₗ[PadicAlgCl ℓ] PadicAlgCl ℓ

/-- The fiber data are actual algebraic-closure pullbacks and terminal evaluations.
Source: RefactorInstruction, Section 4, geometric fibers
(blueprint: lem-weil-pbc-condensed-qbar-function-coefficients). -/
@[irreducible] noncomputable def condensedQbarCanonicalFiberData
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) : CondensedQbarFiberData ℓ X where
  fiber U x := CondensedQbarGeometricEvaluation.fiber ℓ U.left x
  fiber_additive _ _ := inferInstance
  fiber_colimits _ _ := inferInstance
  fiber_regular U x := CondensedQbarGeometricEvaluation.fiberRegularCoordinates ℓ U.left x

/-- The remaining naturality and basis properties of the explicitly constructed
coefficient action and geometric fibers. All data have already been constructed.
Source: RefactorInstruction, Section 4, coefficient naturality and geometric comparison
(blueprint: lem-weil-pbc-condensed-qbar-function-coefficients). -/
structure CondensedQbarCoefficientProperties (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    (d : CondensedQbarFiberData ℓ X) : Prop where
  /-- On the affine weakly contractible basis every scalar endomorphism is a function. -/
  scalar_surjective (U : X.ProEt) (hU : IsAffine U.left)
      (wU : PointLanWeaklyContractible U.left (Scheme.ProEt.mk (𝟙 U.left))) :
      Function.Surjective
        (condensedQbarScalar ℓ U.left)
  /-- Scalar actions commute with restriction along morphisms over X. -/
  scalar_restrict_mk {Y Z : Scheme.{u}}
      (f : Y ⟶ X) (g : Z ⟶ Y) [WeaklyEtale f] [WeaklyEtale g]
      (a : PadicAlgCl.finiteIntermediateFieldValued ℓ Y)
      (b : PadicAlgCl.finiteIntermediateFieldValued ℓ Z)
      (hab : b.1 = a.1.comp g.base.hom) :
    (condensedQbarRegularPullbackIso ℓ g).inv ≫
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) g).map
        (condensedQbarScalar ℓ Y a) ≫ (condensedQbarRegularPullbackIso ℓ g).hom =
      condensedQbarScalar ℓ Z b
  /-- In these coordinates a scalar acts by its value at the point. -/
  fiber_scalar (U : X.ProEt) (x : U.left)
      (a : PadicAlgCl.finiteIntermediateFieldValued ℓ U.left) :
    regularScalarValue (d.fiber U x) (d.fiber_regular U x)
      (condensedQbarScalar ℓ U.left a) = a.1 x
  /-- Evaluating a module pulled back from X depends only on its base point. -/
  fiber_compare (U V : X.ProEt) (x : U.left) (y : V.left) (h : U.hom x = V.hom y) :
    Nonempty
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) U.hom ⋙
          d.fiber U x ≅
        CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) V.hom ⋙
          d.fiber V y)

/-- Naturality and basis properties for the fixed, explicitly constructed fiber data.
Source: RefactorInstruction, Section 4, coefficient naturality and geometric fibers
(blueprint: lem-weil-pbc-condensed-qbar-function-coefficients). -/
abbrev CondensedQbarCanonicalCoefficientProperties
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) : Prop :=
  CondensedQbarCoefficientProperties ℓ X (condensedQbarCanonicalFiberData ℓ X)

/-- Coefficient functions, their restriction, and their geometric evaluation.
All data concern only regular modules and coefficient pullbacks; there is no
presentation, chosen module, or matrix in this interface.
Source: RefactorInstruction, Section 4, coefficient realization and geometric evaluation
(blueprint: lem-weil-pbc-condensed-qbar-function-coefficients). -/
structure CondensedQbarFunctionCoefficients (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) where
  /-- On the affine weakly contractible basis every scalar endomorphism is a function. -/
  scalar_surjective (U : X.ProEt) (hU : IsAffine U.left)
      (wU : PointLanWeaklyContractible U.left (Scheme.ProEt.mk (𝟙 U.left))) :
      Function.Surjective
        (condensedQbarScalar ℓ U.left)
  /-- Scalar actions commute with restriction along morphisms over X. -/
  scalar_restrict_mk {Y Z : Scheme.{u}}
      (f : Y ⟶ X) (g : Z ⟶ Y) [WeaklyEtale f] [WeaklyEtale g]
      (a : PadicAlgCl.finiteIntermediateFieldValued ℓ Y)
      (b : PadicAlgCl.finiteIntermediateFieldValued ℓ Z)
      (hab : b.1 = a.1.comp g.base.hom) :
    (condensedQbarRegularPullbackIso ℓ g).inv ≫
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) g).map
        (condensedQbarScalar ℓ Y a) ≫ (condensedQbarRegularPullbackIso ℓ g).hom =
      condensedQbarScalar ℓ Z b
  /-- Geometric evaluation, after choosing an algebraic closure above the point. -/
  fiber (U : X.ProEt) (x : U.left) :
    Mod (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U.left) ⥤
        ModuleCat.{u + 1} (PadicAlgCl ℓ)
  fiber_additive (U : X.ProEt) (x : U.left) : (fiber U x).Additive
  fiber_colimits (U : X.ProEt) (x : U.left) : PreservesFiniteColimits (fiber U x)
  /-- The regular module has its ordinary one-dimensional coordinates. -/
  fiber_regular (U : X.ProEt) (x : U.left) :
    (fiber U x).obj (Mod.regular
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U.left)) ≃ₗ[PadicAlgCl ℓ] PadicAlgCl ℓ
  /-- In these coordinates a scalar acts by its value at the point. -/
  fiber_scalar (U : X.ProEt) (x : U.left)
      (a : PadicAlgCl.finiteIntermediateFieldValued ℓ U.left) :
    regularScalarValue (fiber U x) (fiber_regular U x)
      (condensedQbarScalar ℓ U.left a) = a.1 x
  /-- Evaluating a module pulled back from X depends only on its base point. -/
  fiber_compare (U V : X.ProEt) (x : U.left) (y : V.left) (h : U.hom x = V.hom y) :
    Nonempty
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) U.hom ⋙ fiber U x ≅
        CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) V.hom ⋙ fiber V y)

/-- Assemble coefficient properties over abstract fiber data, so dependent type
comparisons do not unfold the geometric construction in downstream presentation proofs.
Source: RefactorInstruction, Section 4, geometric fibers
(blueprint: lem-weil-pbc-condensed-qbar-function-coefficients). -/
noncomputable def CondensedQbarFunctionCoefficients.ofData
    {ℓ : ℕ} [Fact ℓ.Prime] {X : Scheme.{u}} (d : CondensedQbarFiberData ℓ X)
    (p : CondensedQbarCoefficientProperties ℓ X d) : CondensedQbarFunctionCoefficients ℓ X where
  scalar_surjective := p.scalar_surjective
  scalar_restrict_mk := p.scalar_restrict_mk
  fiber := d.fiber
  fiber_additive := d.fiber_additive
  fiber_colimits := d.fiber_colimits
  fiber_regular := d.fiber_regular
  fiber_scalar := p.fiber_scalar
  fiber_compare := p.fiber_compare

/-- The scalar action is constructed, by sheafifying multiplication and transporting
through the explicit filtered-colimit ring realization.
Source: RefactorInstruction, Section 4, coefficient realization
(blueprint: lem-weil-pbc-condensed-qbar-function-coefficients). -/
noncomputable abbrev CondensedQbarFunctionCoefficients.scalar
    {ℓ : ℕ} [Fact ℓ.Prime] {X : Scheme.{u}}
    (_q : CondensedQbarFunctionCoefficients ℓ X) (U : X.ProEt) :
    PadicAlgCl.finiteIntermediateFieldValued ℓ U.left →+*
      End (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U.left)) :=
  condensedQbarScalar ℓ U.left

/-- A comparison stated directly for scheme morphisms, avoiding reduction of the
site-object constructor inside a module inverse image.
Source: RefactorInstruction, Section 4, geometric evaluation
(blueprint: lem-weil-pbc-condensed-qbar-function-coefficients). -/
theorem CondensedQbarFunctionCoefficients.fiber_compare_mk
    {ℓ : ℕ} [Fact ℓ.Prime] {X Y Z : Scheme.{u}}
    (q : CondensedQbarFunctionCoefficients ℓ X)
    (f : Y ⟶ X) (g : Z ⟶ X) [WeaklyEtale f] [WeaklyEtale g]
    (x : Y) (y : Z) (h : f x = g y) :
    Nonempty
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) f ⋙
          q.fiber (Scheme.ProEt.mk f) x ≅
        CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) g ⋙
          q.fiber (Scheme.ProEt.mk g) y) :=
  q.fiber_compare (Scheme.ProEt.mk f) (Scheme.ProEt.mk g) x y h

set_option backward.isDefEq.respectTransparency false in
private lemma bounded_unit_isIso (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    (U : X.ProEt) [IsAffine U.left] (wU : PointLanWeaklyContractible X U) :
    IsIso ((toSheafify (Scheme.ProEt.topology X)
      (CondensedQbarScalarConstruction.boundedP ℓ X)).app (op U)) := by
  let F := profiniteToProEtOf X
  let J := coherentTopology Profinite.{u}
  let K := Scheme.ProEt.topology X
  let Λ := Profinite.padicAlgClRingObj.{u} ℓ
  let P := F.op.lan.obj Λ.obj
  let η := F.op.lanUnit.app Λ.obj
  let hp := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension P η
  have hu := (proEtale_sheafification_wcontractible_sections X).2.1 Λ P η hp U
    inferInstance wU
  let a := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  let b := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F
    Ab.{u + 1} J K
  let e := Adjunction.leftAdjointUniq a b
  let c := CondensedQbarCoefficientRealization.globalCoefficientIso ℓ X
  let c' := (e.app Λ).inv ≫ c.hom.hom
  have hc' : IsIso c' := by dsimp [c']; infer_instance
  have : IsIso ((toSheafify K P).app (op U)) := hu.1
  let T := Profinite.of (ConnectedComponents U.left)
  let q := canonicalComponentArrow X U
  let k := η.app (op T) ≫ P.map q.op
  have hk : IsIso k :=
    (hp (op U)).isIso_ι_app_of_isTerminal
      (CostructuredArrow.mk (S := F.op) q.op)
      (canonicalComponentArrow_terminal X U)
  let h := k ≫ (toSheafify K P).app (op U) ≫ c'.hom.app (op U)
  have hh : IsIso h := by dsimp [h]; infer_instance
  let β : Λ.obj.obj (op T) ≅
      (CondensedQbarScalarConstruction.boundedP ℓ X).obj (op U) :=
    ((ULift.ringEquiv.toAddEquiv.trans
    (CondensedQbarScalarConstruction.boundedComponentsIso ℓ U.left).toAddEquiv).trans
      ULift.ringEquiv.symm.toAddEquiv).toAddCommGrpIso
  have heq : h = β.hom ≫
      (toSheafify K (CondensedQbarScalarConstruction.boundedP ℓ X)).app (op U) := by
    have hadj : b.homEquiv _ _ c' = a.homEquiv _ _ c.hom.hom := by
      have hc : c.hom.hom = e.hom.app Λ ≫ c' := by
        dsimp [c']
        simp only [← Category.assoc, Iso.hom_inv_id_app]
        exact (Category.id_comp _).symm
      rw [hc, a.homEquiv_naturality_right,
        Adjunction.homEquiv_leftAdjointUniq_hom_app]
      rfl
    have hleg : (η.app (op T) ≫
        (toSheafify K P).app (op (F.obj T))) ≫ c'.hom.app (op (F.obj T)) =
      (a.homEquiv _ _ c.hom.hom).hom.app (op T) := by
      rw [Category.assoc, ← hadj]
      rfl
    have hq (x : U.left) : profiniteTestProjection X T (q.left x) =
        ConnectedComponents.mk x := by
      have h := congrFun (congrArg DFunLike.coe
        ((pointComponentsEquiv X U T).apply_symm_apply (ContinuousMap.id _)))
        (ConnectedComponents.mk x)
      rw [pointComponentsEquiv_apply] at h
      exact h
    have hn := c'.hom.naturality q.op
    change (sheafify K P).map q.op ≫ c'.hom.app (op U) = _ at hn
    dsimp only [h, k]
    rw [Category.assoc, ← Category.assoc (P.map q.op),
      (toSheafify K P).naturality q.op, Category.assoc,
      hn, ← Category.assoc, ← Category.assoc, hleg]
    apply ConcreteCategory.hom_ext
    intro a₀
    cases a₀ with
    | up a₀ =>
      change (padicAlgClSheaf X ℓ).obj.map q.op
        (((a.homEquiv _ _ c.hom.hom).hom.app (op T)) (ULift.up a₀)) = _
      rw [CondensedQbarCoefficientRealization.globalCoefficientIso_test]
      rw [← NatTrans.naturality_apply]
      change ((toSheafify K (CondensedQbarScalarConstruction.boundedP ℓ X)).app (op U))
        ((CondensedQbarScalarConstruction.boundedP ℓ X).map q.op
          (ULift.up (CondensedQbarScalarConstruction.boundedComp ℓ
            (profiniteTestProjection X T) a₀))) =
        ((toSheafify K (CondensedQbarScalarConstruction.boundedP ℓ X)).app (op U))
          (β.hom (ULift.up a₀))
      apply congrArg
      apply ULift.ext
      apply Subtype.ext
      ext x
      exact congrArg a₀.1 (hq x)
  rw [heq] at hh
  have : IsIso (β.hom ≫
    (toSheafify K (CondensedQbarScalarConstruction.boundedP ℓ X)).app (op U)) := hh
  exact IsIso.of_isIso_comp_left β.hom _


set_option backward.isDefEq.respectTransparency false in
private lemma sheafScalar_surjective (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    [IsAffine Y] (wY : PointLanWeaklyContractible Y (Scheme.ProEt.mk (𝟙 Y))) :
    Function.Surjective (CondensedQbarScalarConstruction.sheafScalar ℓ Y) := by
  let J := Scheme.ProEt.topology Y
  let P := CondensedQbarScalarConstruction.boundedP ℓ Y
  let L := presheafToSheaf J Ab.{u + 1}
  let T := Scheme.ProEt.mk (𝟙 Y)
  let η := toSheafify J P
  have : IsAffine T.left := inferInstanceAs (IsAffine Y)
  have hi : IsIso (η.app (op T)) := bounded_unit_isIso ℓ Y T wY
  intro f
  obtain ⟨a, ha⟩ := ((ConcreteCategory.isIso_iff_bijective (η.app (op T))).mp hi).2
    ((f.hom.hom.app (op T)) (η.app (op T) (ULift.up 1)))
  refine ⟨a.down, ?_⟩
  apply (Mod.bijective_one_comp_hom (Mod.regular (padicAlgClSheaf Y ℓ))).1
  change Functor.LaxMonoidal.ε L ≫ L.map (MonObj.one (X := P)) ≫
      (CondensedQbarScalarConstruction.sheafScalar ℓ Y a.down).hom =
    Functor.LaxMonoidal.ε L ≫ L.map (MonObj.one (X := P)) ≫ f.hom
  congr 1
  apply ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _ _).injective
  change toSheafify J (𝟙_ (Y.ProEtᵒᵖ ⥤ Ab.{u + 1})) ≫
      (L.map (MonObj.one (X := P))).hom ≫
        (CondensedQbarScalarConstruction.sheafScalar ℓ Y a.down).hom.hom =
    toSheafify J (𝟙_ (Y.ProEtᵒᵖ ⥤ Ab.{u + 1})) ≫
      (L.map (MonObj.one (X := P))).hom ≫ f.hom.hom
  rw [← toSheafify_naturality_assoc, ← toSheafify_naturality_assoc]
  change MonObj.one (X := P) ≫ η ≫
      (sheafifyMap J (CondensedQbarScalarConstruction.boundedMul ℓ Y a.down)) = _
  rw [← toSheafify_naturality]
  ext U n
  have h1 :
      ((MonObj.one (X := P) ≫
        CondensedQbarScalarConstruction.boundedMul ℓ Y a.down ≫ η).app U)
          (ULift.up (1 : ℤ)) =
      ((MonObj.one (X := P) ≫ η ≫ f.hom.hom).app U) (ULift.up (1 : ℤ)) := by
    let t : U.unop ⟶ T := MorphismProperty.Over.homMk U.unop.hom
    have hf := ConcreteCategory.congr_hom ((η ≫ f.hom.hom).naturality t.op)
      (ULift.up 1)
    have hη := ConcreteCategory.congr_hom (η.naturality t.op) a
    change f.hom.hom.app U (η.app U (ULift.up 1)) =
      (padicAlgClSheaf Y ℓ).obj.map t.op
        (f.hom.hom.app (op T) (η.app (op T) (ULift.up 1))) at hf
    change η.app U ((P.map t.op) a) =
      (padicAlgClSheaf Y ℓ).obj.map t.op (η.app (op T) a) at hη
    change η.app U (ULift.up (1 *
      CondensedQbarScalarConstruction.restrictBounded ℓ Y U.unop a.down)) =
      f.hom.hom.app U (η.app U (ULift.up 1))
    rw [one_mul, hf, ← ha, ← hη]
    rfl
  have hn : n = n.down • (ULift.up (1 : ℤ) : ULift.{u + 1} ℤ) := by
    apply ULift.ext
    change n.down = n.down * 1
    rw [mul_one]
  rw [hn]
  simp only [map_zsmul]
  exact congrArg (n.down • ·) h1

private lemma condensedQbarScalar_surjective (ℓ : ℕ) [Fact ℓ.Prime]
    (Y : Scheme.{u}) [IsAffine Y]
    (wY : PointLanWeaklyContractible Y (Scheme.ProEt.mk (𝟙 Y))) :
    Function.Surjective (condensedQbarScalar ℓ Y) := by
  let e := CondensedQbarCoefficientRealization.globalCoefficientIso ℓ Y
  let F := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (inv e.inv.hom)
  let d := Mod.regularIsoOfIsIso e.inv.hom
  have : F.Full :=
    inferInstanceAs ((Mod.comapEquivalenceOfIsIso (inv e.inv.hom)).functor.Full)
  intro f
  obtain ⟨a, ha⟩ := sheafScalar_surjective ℓ Y wY
    (F.preimage (d.hom ≫ f ≫ d.inv))
  refine ⟨a, ?_⟩
  change CondensedQbarScalarConstruction.transportedScalar ℓ Y e a = f
  unfold CondensedQbarScalarConstruction.transportedScalar
  change d.inv ≫ F.map (CondensedQbarScalarConstruction.sheafScalar ℓ Y a) ≫ d.hom = f
  rw [ha, F.map_preimage]
  simp only [Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

private lemma fieldRegularCoordinates_apply (K : Type u) [Field K] [IsAlgClosed K]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (m : (CondensedQbarGeometricEvaluation.fieldFiber K ℓ).obj (Mod.regular
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K))))) :
    CondensedQbarGeometricEvaluation.fieldRegularCoordinates K ℓ m =
      (((CondensedQbarGeometricEvaluation.fieldCoefficientIso K ℓ).hom.hom) m).down := by
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma field_scalar (K : Type u) [Field K] [IsAlgClosed K]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (a : PadicAlgCl.finiteIntermediateFieldValued ℓ (Spec (.of K))) :
    (CondensedQbarGeometricEvaluation.fieldRegularCoordinates K ℓ)
      ((CondensedQbarGeometricEvaluation.fieldFiber K ℓ).map
        (condensedQbarScalar ℓ (Spec (.of K)) a)
          ((CondensedQbarGeometricEvaluation.fieldRegularCoordinates K ℓ).symm 1)) =
      a.1 default := by
  let Y := Spec (.of K)
  let T := Scheme.ProEt.mk (𝟙 Y)
  let P := CondensedQbarScalarConstruction.boundedP ℓ Y
  let η := toSheafify (Scheme.ProEt.topology Y) P
  let e := CondensedQbarCoefficientRealization.globalCoefficientIso ℓ Y
  let m : (CondensedQbarGeometricEvaluation.fieldFiber K ℓ).obj (Mod.regular
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)) :=
    e.inv.hom.hom.app (op T) (η.app (op T) (ULift.up 1))
  have hm : CondensedQbarGeometricEvaluation.fieldRegularCoordinates K ℓ m = 1 := by
    rw [fieldRegularCoordinates_apply]
    let d := ((sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1}).mapIso
      ((Mon.forget _).mapIso e)).app (op T)
    change ((CondensedQbarGeometricEvaluation.boundedPointIso K ℓ).hom.hom
      ((CondensedQbarGeometricEvaluation.fieldUnitIso K ℓ).inv.hom
        (d.hom (d.inv (η.app (op T) (ULift.up 1)))))).down = 1
    rw [Iso.inv_hom_id_apply]
    let d' := (Mon.forget _).mapIso (CondensedQbarGeometricEvaluation.fieldUnitIso K ℓ)
    change ((CondensedQbarGeometricEvaluation.boundedPointIso K ℓ).hom.hom
      (d'.inv (d'.hom (ULift.up 1)))).down = 1
    rw [Iso.hom_inv_id_apply]
    rfl
  have hm' : (CondensedQbarGeometricEvaluation.fieldRegularCoordinates K ℓ).symm 1 = m :=
    (LinearEquiv.symm_apply_eq _).mpr hm.symm
  rw [hm', fieldRegularCoordinates_apply]
  change (((CondensedQbarGeometricEvaluation.fieldCoefficientIso K ℓ).hom.hom)
    (((condensedQbarScalar ℓ Y a).hom.hom.app (op T)) m)).down = _
  unfold condensedQbarScalar CondensedQbarScalarConstruction.transportedScalar
  let d := ((sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1}).mapIso
    ((Mon.forget _).mapIso e)).app (op T)
  change (((CondensedQbarGeometricEvaluation.fieldCoefficientIso K ℓ).hom.hom)
    (((inv e.inv.hom ≫ (CondensedQbarScalarConstruction.sheafScalar ℓ Y a).hom ≫
      e.inv.hom).hom.app (op T)) m)).down = _
  rw [show inv e.inv.hom = e.hom.hom from
    (IsIso.inv_eq_of_hom_inv_id (show e.inv.hom ≫ e.hom.hom = 𝟙 _ from
      congrArg (fun f ↦ f.hom) e.inv_hom_id))]
  let σ := sheafifyMap (Scheme.ProEt.topology Y)
    (CondensedQbarScalarConstruction.boundedMul ℓ Y a)
  change ((CondensedQbarGeometricEvaluation.boundedPointIso K ℓ).hom.hom
    ((CondensedQbarGeometricEvaluation.fieldUnitIso K ℓ).inv.hom
      (d.hom (d.inv (σ.app (op T)
        (d.hom (d.inv (η.app (op T) (ULift.up 1))))))))).down = _
  rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
  have hs := ConcreteCategory.congr_hom
    (congr_app (toSheafify_naturality (Scheme.ProEt.topology Y)
      (CondensedQbarScalarConstruction.boundedMul ℓ Y a)) (op T)) (ULift.up 1)
  change η.app (op T) (ULift.up (1 *
    CondensedQbarScalarConstruction.restrictBounded ℓ Y T a)) =
    σ.app (op T) (η.app (op T) (ULift.up 1)) at hs
  rw [← hs, one_mul]
  let d' := (Mon.forget _).mapIso (CondensedQbarGeometricEvaluation.fieldUnitIso K ℓ)
  change ((CondensedQbarGeometricEvaluation.boundedPointIso K ℓ).hom.hom
    (d'.inv (d'.hom (ULift.up a)))).down = _
  rw [Iso.hom_inv_id_apply]
  rfl

section FiberComparison
attribute [local irreducible] CondensedRing.upperStar
  CondensedQbarGeometricEvaluation.fieldFiber

private lemma fiber_pullback (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} (f : Y ⟶ X) (x : Y) : Nonempty
    (CondensedQbarGeometricEvaluation.fiber ℓ X (f x) ≅
      CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) f ⋙
        CondensedQbarGeometricEvaluation.fiber ℓ Y x) := by
  let κs := X.residueField (f x)
  let κt := Y.residueField x
  let : Algebra κs (AlgebraicClosure κt) :=
    ((algebraMap κt (AlgebraicClosure κt)).comp (f.residueFieldMap x).hom).toAlgebra
  let ψ : AlgebraicClosure κs →ₐ[κs] AlgebraicClosure κt := IsAlgClosed.lift
  let ι := Spec.map (CommRingCat.ofHom ψ.toRingHom)
  have hι : ι ≫ CondensedQbarGeometricEvaluation.geometricPoint X (f x) =
      CondensedQbarGeometricEvaluation.geometricPoint Y x ≫ f := by
    unfold CondensedQbarGeometricEvaluation.geometricPoint
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
    ext a
    exact ψ.commutes a
  obtain ⟨e⟩ := condensedQbar_fieldFiber_extension ℓ (AlgebraicClosure κs) (AlgebraicClosure κt)
    ψ.toRingHom
  unfold CondensedQbarGeometricEvaluation.fiber
  let Λ := Profinite.padicAlgClRingObj.{u} ℓ
  exact ⟨Functor.isoWhiskerLeft _ e ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((CondensedRing.upperStarComp Λ ι
        (CondensedQbarGeometricEvaluation.geometricPoint X (f x))).symm ≪≫
        eqToIso (congrArg (CondensedRing.upperStar Λ) hι) ≪≫
        CondensedRing.upperStarComp Λ
          (CondensedQbarGeometricEvaluation.geometricPoint Y x) f) _ ≪≫
    Functor.associator _ _ _⟩

end FiberComparison

private lemma map_conjugate
    {C : Type v} [Category C] {D : Type w} [Category D]
    (E : C ⥤ D) {A B : C} (e : A ≅ B) (f : A ⟶ A) (q : B ⟶ B)
    (h : e.inv ≫ f ≫ e.hom = q) :
    (E.mapIso e).inv ≫ E.map f ≫ (E.mapIso e).hom = E.map q := by
  rw [Functor.mapIso_inv, Functor.mapIso_hom, ← E.map_comp, ← E.map_comp, h]

private lemma coordinates_conjugate
    {R : Type w} [CommRing R] {A B : ModuleCat.{z} R} (e : A ≅ B)
    (c : B ≃ₗ[R] R) (f : A ⟶ A) (q : B ⟶ B)
    (h : e.inv ≫ f ≫ e.hom = q) (b : R)
    (hb : c (q (c.symm 1)) = b) :
    (e.toLinearEquiv.trans c) (f ((e.toLinearEquiv.trans c).symm 1)) = b := by
  simp only [LinearEquiv.trans_apply, LinearEquiv.trans_symm,
    Iso.toLinearEquiv_apply, Iso.toLinearEquiv_symm, Iso.symm_hom]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, h]
  exact hb

private lemma regularScalarValue_comp
    {R : Type w} [CommRing R] {C : Type v} [Category C]
    {D : Type z} [Category D] (H : C ⥤ D) (E : D ⥤ ModuleCat.{u} R)
    {A : C} (c : (H ⋙ E).obj A ≃ₗ[R] R) (f : A ⟶ A) :
    regularScalarValue (H ⋙ E) c f = regularScalarValue E c (H.map f) := by
  unfold regularScalarValue
  rfl

private lemma regularScalarValue_conjugate
    {R : Type w} [CommRing R] {C : Type v} [Category C]
    (E : C ⥤ ModuleCat.{u} R) {A B : C} (e : A ≅ B)
    (c : E.obj B ≃ₗ[R] R) (f : A ⟶ A) (q : B ⟶ B)
    (h : e.inv ≫ f ≫ e.hom = q) :
    regularScalarValue E ((E.mapIso e).toLinearEquiv.trans c) f =
      regularScalarValue E c q := by
  rw [regularScalarValue_def, regularScalarValue_def]
  exact coordinates_conjugate (E.mapIso e) c _ _ (map_conjugate E e f q h) _ rfl

section FiberScalar
attribute [local irreducible] CondensedQbarGeometricEvaluation.fieldFiber
  CondensedRing.upperStar CondensedQbarGeometricEvaluation.fieldRegularCoordinates
attribute [local semireducible] CondensedQbarGeometricEvaluation.fiber
  CondensedQbarGeometricEvaluation.fiberRegularCoordinates

private lemma fiber_scalar (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u}) (x : Y)
    (a : PadicAlgCl.finiteIntermediateFieldValued ℓ Y) :
    regularScalarValue (CondensedQbarGeometricEvaluation.fiber ℓ Y x)
      (CondensedQbarGeometricEvaluation.fiberRegularCoordinates ℓ Y x)
      (condensedQbarScalar ℓ Y a) = a.1 x := by
  let g := CondensedQbarGeometricEvaluation.geometricPoint Y x
  let H := CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) g
  let E := CondensedQbarGeometricEvaluation.fieldFiber (AlgebraicClosure (Y.residueField x)) ℓ
  let e := condensedQbarRegularPullbackIso ℓ g
  let c := CondensedQbarGeometricEvaluation.fieldRegularCoordinates
    (AlgebraicClosure (Y.residueField x)) ℓ
  have hpoint : g default = x := Scheme.fromSpecResidueField_apply x _
  change regularScalarValue (H ⋙ E) ((E.mapIso e).toLinearEquiv.trans c)
    (condensedQbarScalar ℓ Y a) = _
  rw [regularScalarValue_comp, regularScalarValue_conjugate E e c _ _
    (condensedQbar_scalar_pullback ℓ g a)]
  exact (regularScalarValue_def _ _ _).trans
    ((field_scalar _ ℓ (CondensedQbarScalarConstruction.boundedComp ℓ g.base.hom a)).trans
      (congrArg a.1 hpoint))


end FiberScalar

private lemma fibers_compare (ℓ : ℕ) [Fact ℓ.Prime] {X : Scheme.{u}}
    (U V : X.ProEt) (x : U.left) (y : V.left) (h : U.hom x = V.hom y) :
    Nonempty (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) U.hom ⋙
        CondensedQbarGeometricEvaluation.fiber ℓ U.left x ≅
      CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) V.hom ⋙
        CondensedQbarGeometricEvaluation.fiber ℓ V.left y) := by
  obtain ⟨eU⟩ := fiber_pullback ℓ U.hom x
  obtain ⟨eV⟩ := fiber_pullback ℓ V.hom y
  exact ⟨eU.symm ≪≫ eqToIso
    (congrArg (CondensedQbarGeometricEvaluation.fiber ℓ X) h) ≪≫ eV⟩

attribute [local semireducible] condensedQbarCanonicalFiberData




/-- Bounded condensed coefficients admit scalar realization and compatible geometric
fiber functors, independently of any module or presentation.

Source: RefactorInstruction, Section 4, coefficient realization and geometric-fiber
comparison, steps 2--3 of the finite-matrix argument
(blueprint: lem-weil-pbc-condensed-qbar-function-coefficients).

Proof in words: the explicit construction above realizes the bounded coefficient ring
on every scheme by the filtered colimit of its canonical finite-extension realizations.
Its scalar action is multiplication on the bounded-function presheaf, followed by
monoidal sheafification and transport through that constructed ring isomorphism. These
constructions and their ring laws are already proved above. To finish the scalar
properties, use the normalization of the finite-extension realizations on profinite
test functions. Their uniqueness makes them compatible with localization along every
small-site object U to X. The bounded-function presheaf unit and multiplication commute
with restriction, giving scalar_restrict_mk after passage to the filtered colimit.
On an affine weakly contractible U, the point-basis evaluation identifies coefficient
sections with bounded functions on its profinite connected-component quotient.
Continuous functions on U factor through that quotient, and the surjective quotient
preserves the finite-subextension bound. A regular-module endomorphism is determined
by the image of one, so this proves scalar_surjective.

For fiber U x choose an algebraic closure of the residue field of x, pull modules to
its spectrum, and evaluate at the terminal object. The coefficient comparison there
identifies coefficient sections with Qbar_l. Transport the action through this
identification to obtain the stated module functor and fiber_regular. Inverse image
preserves finite colimits; evaluation on an algebraically closed field does so because
every pro-etale cover of the field splits. Colimits of module objects are created on
the underlying abelian sheaves. These facts give fiber_additive and fiber_colimits.
Naturality of coefficient realization identifies the action of a bounded function
with its point value, proving fiber_scalar. If two points have the same image in X,
choose a common algebraically closed overfield of their residue fields. The geometric
field extension comparison identifies both evaluated pullbacks from X with evaluation
at that common point, naturally in the module. This yields fiber_compare. No finite
presentation, matrix, corank, local constancy, or freeness assertion is used. Empty
objects have no point evaluations, and the scalar statement there uses the zero ring.
-/
theorem condensedQbar_canonical_coefficient_properties
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] :
    CondensedQbarCanonicalCoefficientProperties ℓ X := by
  change CondensedQbarCoefficientProperties ℓ X
    { fiber := fun U x ↦ CondensedQbarGeometricEvaluation.fiber ℓ U.left x
      fiber_additive := fun _ _ ↦ inferInstance
      fiber_colimits := fun _ _ ↦ inferInstance
      fiber_regular := fun U x ↦
        CondensedQbarGeometricEvaluation.fiberRegularCoordinates ℓ U.left x }
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro U hU wU
    let := hU
    exact condensedQbarScalar_surjective ℓ U.left wU
  · intro Y Z f g _ _ a b hab
    exact (condensedQbar_scalar_pullback ℓ g a).trans
      (congrArg (condensedQbarScalar ℓ Z) (Subtype.ext hab).symm)
  · intro U x a
    exact fiber_scalar ℓ U.left x a
  · exact fibers_compare ℓ


/-- Assemble the constructed scalar action, geometric fibers, regular coordinates,
and their proved additive and finite-colimit properties with coefficient naturality.
Source: RefactorInstruction, Section 4, coefficient realization and geometric fibers
(blueprint: lem-weil-pbc-condensed-qbar-function-coefficients). -/
theorem exists_condensedQbar_function_coefficients
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (_hcoeff : Nonempty
      (Mon.mk (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) ≅
        Mon.mk (padicAlgClSheaf X ℓ))) :
    Nonempty (CondensedQbarFunctionCoefficients ℓ X) := by
  exact ⟨CondensedQbarFunctionCoefficients.ofData (condensedQbarCanonicalFiberData ℓ X)
    (condensedQbar_canonical_coefficient_properties ℓ X)⟩

end AlgebraicGeometry.ProEtale
