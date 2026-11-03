/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PrincipalCoefficient.PrincipalCoefficientUniversalPair
public import WeilConjectures.SixFunctors.Etale.Derived.CoextendScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.CategoryTheory.DerivedCategory.Complete.QuotPowTriangle
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Reduction
import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal

/-! # The quotient-linear dual of a regular principal quotient

Source: latest blueprint lem-fix-operation-reduction, principal coefficient comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory MonoidalCategory CategoryTheory.Limits
open scoped CategoryTheory.Functor
attribute [local instance 2000] CommRing.toRing
namespace AlgebraicGeometry.PrincipalCoefficient

/-- Restriction need only be fully faithful on the heart, not on derived objects. -/
private theorem liftSingleIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Full] [F.Faithful] (K : _root_.DerivedCategory C) (M : C) (n : ℤ)
    (e : F.mapDerivedCategory.obj K ≅
      (_root_.DerivedCategory.singleFunctor D n).obj (F.obj M)) :
    Nonempty (K ≅ (_root_.DerivedCategory.singleFunctor C n).obj M) := by
  have hge : (F.mapDerivedCategory.obj K).IsGE n :=
    _root_.DerivedCategory.TStructure.t.isGE_of_iso e.symm n
  have hle : (F.mapDerivedCategory.obj K).IsLE n :=
    _root_.DerivedCategory.TStructure.t.isLE_of_iso e.symm n
  have hc := F.homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj
    (a := n) (b := n) ⟨hge, hle⟩
  let := hc.1
  let := hc.2
  obtain ⟨N, ⟨d⟩⟩ := K.exists_iso_singleFunctor_obj_of_isGE_of_isLE n
  let h : (_root_.DerivedCategory.singleFunctor D n).obj (F.obj N) ≅
      (_root_.DerivedCategory.singleFunctor D n).obj (F.obj M) :=
    ((F.mapDerivedCategorySingleFunctor n).app N).symm ≪≫
      F.mapDerivedCategory.mapIso d.symm ≪≫ e
  exact ⟨d ≪≫ (_root_.DerivedCategory.singleFunctor C n).mapIso
    (F.preimageIso ((_root_.DerivedCategory.singleFunctor D n).preimageIso h))⟩

/-- The injective short exact sequence computes the underlying coefficient dual. -/
private theorem underlyingUnitIso
    {A : Type (u + 1)} [CommRing A] {r : A}
    (hr : r ∈ nonZeroDivisors A) (X : Scheme.{u}) :
    Nonempty
      ((Sheaf.derivedRestrictScalars X.smallEtaleTopology
          (Ideal.Quotient.mk (Ideal.span {r}))).obj
        ((Etale.coextendScalars (Ideal.Quotient.mk (Ideal.span {r})) X).rightDerivedFunctor.obj
            (𝟙_ (_root_.DerivedCategory
              (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))))) ≅
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology
          (Ideal.Quotient.mk (Ideal.span {r}))).obj
            (𝟙_ (_root_.DerivedCategory (Sheaf X.smallEtaleTopology
              (ModuleCat.{u + 1} (A ⧸ Ideal.span {r}))))))⟦(-1 : ℤ)⟧) := by
  let C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let B := A ⧸ Ideal.span {r}
  let D := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)
  let φ := Ideal.Quotient.mk (Ideal.span {r})
  let U := Sheaf.restrictScalars X.smallEtaleTopology φ
  let H := Etale.coextendScalars φ X
  let K := _root_.DerivedCategory.Q.objPreimage (𝟙_ (_root_.DerivedCategory C))
  let I := (CochainComplex.kInjectiveResolutionFunctor.{u + 1} C).obj K
  have : QuasiIso ((CochainComplex.toKInjectiveResolution.{u + 1} C).app K) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u + 1} C K).2
  let eC : 𝟙_ (_root_.DerivedCategory C) ≅ _root_.DerivedCategory.Q.obj I :=
    (_root_.DerivedCategory.Q.objObjPreimageIso _).symm ≪≫
      asIso (_root_.DerivedCategory.Q.map
        ((CochainComplex.toKInjectiveResolution.{u + 1} C).app K))
  let q := (HomotopyCategory.quotient C (.up ℤ)).obj I
  let eH : H.rightDerivedFunctor.obj (𝟙_ (_root_.DerivedCategory C)) ≅
      _root_.DerivedCategory.Q.obj ((H.mapHomologicalComplex (.up ℤ)).obj I) :=
    H.rightDerivedFunctor.mapIso
      (eC ≪≫ ((_root_.DerivedCategory.quotientCompQhIso C).app I).symm) ≪≫
      (asIso (H.rightDerivedFunctorUnit.app q)).symm ≪≫
      (_root_.DerivedCategory.quotientCompQhIso D).app _
  let S := Etale.coextendQuotientComplexShortComplex (ϖ := r) I
  have hs := Etale.shortExact_coextendQuotientComplexShortComplex r hr I
  let eU : U.mapDerivedCategory.obj
        (H.rightDerivedFunctor.obj (𝟙_ (_root_.DerivedCategory C))) ≅
      _root_.DerivedCategory.Q.obj S.X₁ :=
    U.mapDerivedCategory.mapIso eH ≪≫ U.mapDerivedCategoryFactors.app _
  let T := _root_.DerivedCategory.quotPowTriangle X.smallEtaleTopology hr rfl 1
  let eA : T.obj₁ ≅ 𝟙_ (_root_.DerivedCategory C) :=
    _root_.DerivedCategory.singleFunctorObjUnitIso C
  let e : T.obj₁ ≅ _root_.DerivedCategory.Q.obj I := eA ≪≫ eC
  have hT := _root_.DerivedCategory.quotPowTriangle_distinguished
    X.smallEtaleTopology hr rfl 1
  have hS := _root_.DerivedCategory.triangleOfSES_distinguished hs
  have hm : (_root_.DerivedCategory.triangleOfSES hs).rotate.mor₁ =
      r • 𝟙 (_root_.DerivedCategory.Q.obj I) := by
    change _root_.DerivedCategory.Q.map (r • 𝟙 I) = _
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  obtain ⟨d, _, _⟩ := Pretriangulated.exists_iso_of_arrow_iso _ _ hT
    (Pretriangulated.rot_of_distTriang _ hS)
    (Arrow.isoMk e e (by
      symm
      change T.mor₁ ≫ e.hom = e.hom ≫ _
      have ht : T.mor₁ = r • 𝟙 T.obj₁ := by
        exact (_root_.DerivedCategory.quotPowTriangle_mor₁
          X.smallEtaleTopology hr rfl 1).trans (by rw [pow_one])
      calc
        _ = (r • 𝟙 T.obj₁) ≫ e.hom := congrArg (fun k ↦ k ≫ e.hom) ht
        _ = e.hom ≫ (r • 𝟙 _) := by
          rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
        _ = _ := congrArg (fun k ↦ e.hom ≫ k) hm.symm))
  let e₃ := Pretriangulated.Triangle.π₃.mapIso d
  let eF : _root_.DerivedCategory.Q.obj S.X₁ ≅ T.obj₃⟦(-1 : ℤ)⟧ :=
    ((shiftFunctorCompIsoId (_root_.DerivedCategory C) 1 (-1 : ℤ) (by omega)).app _).symm ≪≫
      (shiftFunctor _ (-1 : ℤ)).mapIso e₃.symm
  let qB : ModuleCat.of A (A ⧸ Ideal.span {r} ^ 1) ≅ ModuleCat.of A B :=
    (Submodule.quotEquivOfEq _ _ (pow_one _)).toModuleIso
  let eB : T.obj₃ ≅ U.mapDerivedCategory.obj (𝟙_ (_root_.DerivedCategory D)) :=
    (_root_.DerivedCategory.singleFunctor C 0).mapIso
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).mapIso qB ≪≫
        ((constantCommuteCompose X.smallEtaleTopology
          (ModuleCat.restrictScalars φ)).app (𝟙_ (ModuleCat.{u + 1} B))).symm) ≪≫
      ((U.mapDerivedCategorySingleFunctor 0).app (𝟙_ D)).symm ≪≫
      U.mapDerivedCategory.mapIso (_root_.DerivedCategory.singleFunctorObjUnitIso D)
  exact ⟨eU ≪≫ eF ≪≫ (shiftFunctor _ (-1 : ℤ)).mapIso eB⟩

/-- The derived coinduction of the coefficient unit is the quotient unit shifted by -1.
The isomorphism is in the quotient coefficient category, including its B-action.
Source: latest blueprint lem-fix-operation-reduction, principal coefficient duality;
Stacks 0A70, 0BZE and 0BZH (the regular two-term resolution)
(blueprint: lem-principal-coefficient-dual-unit).

Proof: use the exact resolution A --a^n--> A of B = A/(a^n). For an injective
resolution I of the constant A-sheaf, the actual coinduction counit and scalar
multiplication give the termwise short exact sequence
0 -> Res Hom_A(B,I) -> I --a^n--> I -> 0. Its derived triangle identifies the
restricted coinduction of A[0] with the fiber of a^n on A[0]. Regularity and
exact constant sheafification identify its unique nonzero cohomology, in degree
one, with the constant B-sheaf. The counit identifies the A-action on that
cohomology with the quotient action. Ordinary restriction along a surjection is
fully faithful, so this cohomology identification is B-linear. Exact restriction
detects vanishing of all other cohomology. The canonical truncation isomorphism
for an object with a single cohomology sheaf then gives B[0][-1] inside D(X,B).
This lifts only the cohomology-sheaf map, where restriction is fully faithful;
it does not lift an arbitrary morphism of A-derived objects. When n = 0 the
quotient and its derived category are zero. -/
theorem principalCoinductionUnit
    {A : Type (u + 1)} [CommRing A] {a : A}
    (ha : a ∈ nonZeroDivisors A) (n : ℕ) (X : Scheme.{u}) :
    Nonempty
      ((Etale.coextendScalars
              (Ideal.Quotient.mk (Ideal.span {a} ^ n)) X).rightDerivedFunctor.obj
            (𝟙_ (_root_.DerivedCategory
              (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))) ≅
        (𝟙_ (_root_.DerivedCategory (Sheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n)))))⟦(-1 : ℤ)⟧) := by
  rw [Ideal.span_singleton_pow]
  let r := a ^ n
  let B := A ⧸ Ideal.span {r}
  let C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let D := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)
  let φ := Ideal.Quotient.mk (Ideal.span {r})
  let U := Sheaf.restrictScalars X.smallEtaleTopology φ
  let K := (Etale.coextendScalars φ X).rightDerivedFunctor.obj
    (𝟙_ (_root_.DerivedCategory C))
  have : U.Full := Sheaf.restrictScalars_full X.smallEtaleTopology φ
    Ideal.Quotient.mk_surjective
  let d : (𝟙_ (_root_.DerivedCategory D))⟦(-1 : ℤ)⟧ ≅
      (_root_.DerivedCategory.singleFunctor D 1).obj (𝟙_ D) :=
    (shiftFunctor _ (-1 : ℤ)).mapIso
      (_root_.DerivedCategory.singleFunctorObjUnitIso D).symm ≪≫
      ((_root_.DerivedCategory.singleFunctors D).shiftIso (-1) 1 0 (by omega)).app (𝟙_ D)
  let e : U.mapDerivedCategory.obj K ≅
      (_root_.DerivedCategory.singleFunctor C 1).obj (U.obj (𝟙_ D)) :=
    (underlyingUnitIso (pow_mem ha n) X).some ≪≫
      ((U.mapDerivedCategory.commShiftIso (-1 : ℤ)).app _).symm ≪≫
      U.mapDerivedCategory.mapIso d ≪≫
      (U.mapDerivedCategorySingleFunctor 1).app (𝟙_ D)
  exact ⟨(liftSingleIso U K (𝟙_ D) 1 e).some ≪≫ d.symm⟩

end AlgebraicGeometry.PrincipalCoefficient
