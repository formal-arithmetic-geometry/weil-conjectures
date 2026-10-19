/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.Paper.PurityRelativeKummerMaps
import Sheaf.Paper.AffineLineOrdinaryInvariance
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # A component of the relative Kummer calculation

Source: blueprint sk-prop-a1-kummer, prop-pur-gm-relative-kummer.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local irreducible] ProEtale.upperStar ProEtale.lowerStar
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  ProEtale.derivedUpperStarLowerStarAdjunction ProEtale.derivedBaseChangeMap
  ProEtale.comparisonUpperStar Etale.upperStar
  Functor.mapDerivedCategory Functor.mapDerivedCategoryPlus
  Adjunction.derivedAdjunction Adjunction.derivedPlus


namespace WeilConjectures.PurityFiniteSetting
attribute [local irreducible] constant twist constantEtale twistEtale
end WeilConjectures.PurityFiniteSetting

namespace AlgebraicGeometry.Scheme
/-- Extending scalars from a `ZMod N`-module agrees with extending its underlying
abelian group: all additive maps between `ZMod N`-modules are automatically linear. -/
private noncomputable def zmodScalarExtensionIso
    (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    ModuleCat.extendScalars (finiteEtaleTwistScalar N A hA) ≅
      forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat ⋙
        ModuleCat.extendScalarsAddCommGrp A := by
  let f := finiteEtaleTwistScalar N A hA
  let adj := ModuleCat.extendScalarsAddCommGrpAdj A
  let e (M : ModuleCat.{u + 1} (ZMod N)) (P : ModuleCat.{u + 1} A) :
      ((forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat).obj M ⟶
          (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat).obj P) ≃
        (M ⟶ (ModuleCat.restrictScalars f).obj P) :=
    { toFun := fun g ↦ ModuleCat.ofHom (X := M) (Y := (ModuleCat.restrictScalars f).obj P)
        (AddMonoidHom.toZModLinearMap N (M := M)
          (M₁ := (ModuleCat.restrictScalars f).obj P) g.hom)
      invFun := fun g ↦ AddCommGrpCat.ofHom g.hom.toAddMonoidHom
      left_inv := fun g ↦ rfl
      right_inv := fun g ↦ by ext; rfl }
  let adj' : (forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat ⋙
      ModuleCat.extendScalarsAddCommGrp A) ⊣ ModuleCat.restrictScalars f :=
    Adjunction.mkOfHomEquiv
      { homEquiv := fun M P ↦ (adj.homEquiv _ _).trans (e M P)
        homEquiv_naturality_left_symm := by
          intro M' M P g k
          change (adj.homEquiv _ _).symm
            ((forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat).map g ≫
              (e M P).symm k) = _
          exact adj.homEquiv_naturality_left_symm _ _
        homEquiv_naturality_right := by
          intro M P P' g k
          change e M P' (adj.homEquiv _ _ (g ≫ k)) = _
          rw [adj.homEquiv_naturality_right]
          rfl }
  exact (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} f).leftAdjointUniq adj'

/-- The published finite twist line is the existing abelian-sheaf scalar extension. -/
private noncomputable def finiteEtaleLineAbIso
    (T : Scheme.{u}) (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    finiteEtaleTateLine T N A hA ≅
      (AlgebraicGeometry.Etale.extendScalars A T).obj (T.rootsOfUnitySheaf N) :=
  (presheafToSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapIso
    (Functor.isoWhiskerLeft (finiteEtaleMuModulePresheaf T N)
      (zmodScalarExtensionIso N A hA))

end AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

private theorem unbounded_unit_isIso (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
    [IsIso ((ProEtale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} P.Coefficient) f).derivedPlus.unit.app K)] :
    IsIso ((ProEtale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} P.Coefficient) f).unit.app K.obj) := by
  let adj := ProEtale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} P.Coefficient) f
  have hh : IsIso (DerivedCategory.Plus.ι.map (adj.derivedAdjunctionPlus.unit.app K)) := by
    rw [adj.derivedAdjunctionPlus_eq_derivedPlus]
    infer_instance
  simp only [Adjunction.derivedAdjunctionPlus,
    Adjunction.map_restrictFullyFaithful_unit_app, Adjunction.ofNatIsoLeft_unit] at hh
  simp only [NatTrans.comp_app,
    ← Category.assoc, isIso_comp_right_iff] at hh
  unfold ProEtale.derivedUpperStarLowerStarAdjunction
  exact hh

private noncomputable def constantOrdinaryIso (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level)
    (Y : Scheme.{u}) (a : Y ⟶ Spec (.of P.field.k)) :
    (P.a1OrdinaryProEtaleModule a 0).obj ≅ P.derivedSheaf h Y false := by
  let F := Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) a
  let N := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y
  exact (DerivedCategory.Plus.ι.mapIso
    (N.mapDerivedCategoryPlus.mapIso ((F.mapDerivedCategoryPlusSingleFunctor 0).app _) ≪≫
      (N.mapDerivedCategoryPlusSingleFunctor 0).app _)) ≪≫
    (DerivedCategory.Plus.singleFunctorιIso _ 0).app
      (N.obj (F.obj (P.constantEtale (Spec (.of P.field.k))))) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (N.mapIso ((Scheme.upperStarConstantSheafIso
        (ModuleCat.{u + 1} P.Coefficient) a).app _))

private noncomputable def twistConstantIso (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (.of P.field.k)) (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.exponent)
    [NeZero P.exponent] : P.twist h Y ≅ P.constant Y := by
  let N := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y
  exact N.mapIso
    (Scheme.finiteEtaleLineAbIso Y P.exponent P.Coefficient
      (P.exponent_coefficient_eq_zero h) ≪≫
      (Etale.extendScalars P.Coefficient Y).mapIso
        (Y.constantZModIsoRootsOfUnitySheaf P.exponent a hζ).symm ≪≫
      Etale.extendScalarsConstantZModIso Y (P.exponent_coefficient_eq_zero h))

private theorem unit_constant (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (.of P.field.k)) :
    IsIso ((ProEtale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} P.Coefficient) (lineProjection Y)).unit.app
        (P.derivedSheaf h Y false)) := by
  let : Y.Over (Spec (.of P.field.k)) := ⟨a⟩
  have hh : IsIso ((ProEtale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} P.Coefficient) (lineProjection Y)).derivedPlus.unit.app
        (P.a1OrdinaryProEtaleModule a 0)) :=
    (affineLineOrdinaryInvariance P Y 0 0).2.2.1
  have h' := unbounded_unit_isIso P (lineProjection Y) (P.a1OrdinaryProEtaleModule a 0)
  rw [NatTrans.isIso_app_iff_of_iso _ (constantOrdinaryIso P h Y a)] at h'
  exact h'

/-- The specified pullback map on constants is invertible.
Source: the constant-sheaf and comparison inverse-image isomorphisms
(blueprint: prop-pur-gm-relative-kummer). -/
private theorem isIso_constantPullback (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) : IsIso (P.constantPullback f) := by
  unfold constantPullback
  infer_instance

/-- The specified pullback map on the finite root line is invertible over a base
where the Kummer exponent is a unit. Source: the canonical root-line pullback
(blueprint: prop-pur-gm-relative-kummer). -/
private theorem isIso_twistPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hr : IsUnit (P.exponent : Γ(Y, ⊤))) : IsIso (P.twistPullback h f) := by
  have := P.isIso_twistEtalePullback h f hr
  unfold twistPullback
  infer_instance

/-- The degree-zero derived coefficient identification is invertible whenever the
Kummer exponent is invertible on the target. Source: exact inverse image and the
single-complex comparison (blueprint: prop-pur-gm-relative-kummer). -/
private theorem isIso_derivedCoefficientPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hr : IsUnit (P.exponent : Γ(Y, ⊤))) (twisted : Bool) :
    IsIso (P.derivedCoefficientPullback h f twisted) := by
  have := P.isIso_constantPullback f
  have := P.isIso_twistPullback h f hr
  cases twisted <;>
    dsimp only [derivedCoefficientPullback, Functor.mapWithComparison] <;> infer_instance

private theorem relative_line_isIso (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (.of P.field.k)) (twisted : Bool) :
    IsIso (P.relativeUnit h (lineProjection Y) twisted) := by
  have hco := P.isIso_derivedCoefficientPullback h (lineProjection Y)
    (P.exponent_isUnit Y a) twisted
  have hc := unit_constant P h Y a
  have hu : IsIso ((ProEtale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} P.Coefficient) (lineProjection Y)).unit.app
        (P.derivedSheaf h Y twisted)) := by
    cases twisted
    · exact hc
    · have he : IsUnit (P.exponent : P.field.k) := by
        simpa only [map_natCast] using (P.exponent_isUnit (Spec (.of P.field.k))
          (𝟙 _)).map (Scheme.ΓSpecIso (.of P.field.k)).hom.hom
      have : NeZero (P.exponent : P.field.k) := ⟨he.ne_zero⟩
      have : NeZero P.exponent := ⟨fun hn ↦ he.ne_zero (by simp [hn])⟩
      let : IsAlgClosed P.field.k := IsAlgClosure.isAlgClosed P.field.k₀
      obtain ⟨ζ, hζ, _⟩ := (IsSepClosed.exists_isPrimitiveRoot.{u, u} P.field.k P.exponent).2.2
      let e := (DerivedCategory.singleFunctor _ 0).mapIso
        (twistConstantIso P h Y a ζ hζ)
      exact (NatTrans.isIso_app_iff_of_iso _ e).2 hc
  dsimp only [relativeUnit]
  infer_instance



attribute [local irreducible] constantPullback twistPullback derivedCoefficientPullback
  relativeUnit kummerGenerator derivedSheaf coefficientSheaf constant twist
  constantEtale twistEtale coordinateKummer

/-- The affine-line unit is an isomorphism, for each of the
constant and root-tensor coefficient sheaves.
Source: blueprint prop-pur-gm-relative-kummer, proof steps 1--9 and 13--14
(blueprint: lem-pur-relative-line-cohomology).

Proof: Apply ordinary affine-line invariance to the bounded-below constant module
complex. The exact-functor single-complex comparison identifies its coefficient
object with the published constant sheaf. The compatibility of the bounded-below
and unbounded derived adjunctions transports invertibility of the unit. Choose a
primitive root of the invertible exponent in the algebraically closed field.
The standard roots-of-unity trivialization, followed by scalar extension, identifies
the actual finite root line with the constant coefficient sheaf. Uniqueness of left
adjoints identifies scalar extension from ZMod with scalar extension of the underlying
abelian group, so the trivialization applies to the actual twist used here. Naturality
of the adjunction unit transports its invertibility across this isomorphism. Both
canonical coefficient pullback maps are isomorphisms; composing with the direct-image
image of these maps gives the specified relativeUnit. Every homology functor preserves
that isomorphism. This includes the empty base and all integer degrees. -/
theorem relative_line_cohomology (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) (twisted : Bool) :
    IsIso (P.relativeUnit h (lineProjection Y) twisted) :=
  relative_line_isIso P h Y a twisted

end WeilConjectures.PurityFiniteSetting
