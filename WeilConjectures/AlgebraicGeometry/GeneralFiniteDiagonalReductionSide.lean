/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.CompExact
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtension
public import WeilConjectures.EtaleCohomology.TateTwist.KummerLevelIndependence
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.CategoryTheory.Sites.SheafAdjunctionUnitProjection

/-! # The live derived scalar comparison on the side framework

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-setup/sec-the-purity-statement/
sk-thm-purity-transport/sk-thm-purity-transport.proof.md, Step 1

This module records the comparison obtained from the canonical scalar square on the
pro-etale and small-etale sites. The derived square is the left-derived image of the
underived comparison, and its inverse is transported through the canonical left-adjoint
identification of the published small-etale scalar extension.
(blueprint: def-pur-side-derived-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

local instance proEtaleEssentiallySmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _

/-- The live derived pro-etale scalar extension used in finite reduction.
Source: Stacks Tags 06YY and 07A4; finite-coefficient derived scalar extension;
(blueprint: def-pur-side-derived-comparison). -/
abbrev sideScalar {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    [Functor.PreservesKFlatQuasiIso (sheafExtendScalars φ T)] :
    Etale.FiniteSmoothPurity.proCategory A T ⥤
      Etale.FiniteSmoothPurity.proCategory B T :=
  (sheafExtendScalars φ T).leftDerivedFunctor

/-- The canonical scalar/comparison isomorphism, derived from the ordinary scalar
comparison on common flat resolutions. On such resolutions both sides apply the
ordinary scalar/comparison square term by term. The left-derived universal property
then supplies the isomorphism; no invertibility of a general adjunction mate is asserted.
Source: Stacks Tags 06YY and 07A4; `sk-thm-purity-transport`, Step 1;
(blueprint: def-pur-side-derived-comparison). -/
noncomputable def sideComparisonReductionIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {T : Scheme.{u}} (φ : A →+* B)
    [Functor.PreservesKFlatQuasiIso (sheafExtendScalars φ T)] :
    Etale.FiniteSmoothPurity.comparison A T ⋙ sideScalar φ T ≅
      Etale.scalarExtension φ T ⋙ Etale.FiniteSmoothPurity.comparison B T := by
  letI : IsNoetherianRing A := isNoetherian_of_finite A A
  let F := comparisonUpperStar (ModuleCat.{u + 1} A) T
  let G := comparisonUpperStar (ModuleCat.{u + 1} B) T
  let E := etaleSheafExtendScalars φ T
  let U := Sheaf.restrictScalars T.smallEtaleTopology φ
  let H := sheafExtendScalars φ T
  letI : E.IsLeftAdjoint := (etaleSheafExtendScalarsAdjunction φ T).isLeftAdjoint
  letI : E.PreservesKFlatQuasiIso := by
    have : IsIso (Etale.scalarSheafTensorTransformation φ T) := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro P
      let := φ.toAlgebra
      have : T.smallEtaleTopology.PreservesSheafification
          (ModuleCat.restrictScalars.{u + 1} φ) :=
        Sheaf.preservesSheafification_of_adjunction _
          (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ)
      exact isIso_sheafAdjunction_unitProjection T.smallEtaleTopology
        (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} (algebraMap A B)) P
    let τ := asIso (Etale.scalarSheafTensorTransformation φ T)
    apply Functor.PreservesKFlatQuasiIso.mk'
    intro P hP hPa
    have ht := CochainComplex.acyclic_tensorRight_of_kFlat P hP hPa
      (Etale.scalarCoefficientSheaf φ T)
    have he : (((E ⋙ U).mapHomologicalComplex _).obj P).Acyclic :=
      ht.of_iso ((NatIso.mapHomologicalComplex τ _).app P)
    intro n
    exact (ShortComplex.exact_map_iff_of_faithful _ U).1 (he n)
  let ε₁ := Functor.leftDerivedFunctorCompMapDerivedCategoryCounit F H
  let ε₂ := Functor.leftDerivedFunctorCompMapDerivedCategoryRightCounit E G
  haveI : (F.mapDerivedCategory ⋙ H.leftDerivedFunctor).IsLeftDerivedFunctor ε₁
      (HomotopyCategory.quasiIso _ (.up ℤ)) := by
    let Φ := HomotopyCategory.quasiIsoLocalizerMorphism F.kFlatMap
    apply Φ.isLeftDerivedFunctor_of_isLeftDerivabilityStructure ε₁
    intro K
    have : IsIso (H.leftDerivedFunctorCounit.app
        ((F.mapHomotopyCategory (.up ℤ)).obj (Φ.functor.obj K))) :=
      H.isIso_leftDerivedFunctorCounit_app_of_kFlat' _ K.property
    dsimp only [ε₁, Functor.leftDerivedFunctorCompMapDerivedCategoryCounit,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  let e := (etaleSheafExtendScalarsCompComparisonUpperStarIso φ T).symm
  let eh : (F ⋙ H).mapHomotopyCategory (.up ℤ) ≅
      (E ⋙ G).mapHomotopyCategory (.up ℤ) :=
    { hom := NatTrans.mapHomotopyCategory e.hom (.up ℤ)
      inv := NatTrans.mapHomotopyCategory e.inv (.up ℤ)
      hom_inv_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id,
          NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id,
          NatTrans.mapHomotopyCategory_id] }
  let derivedSquare := Functor.leftDerivedNatIso
    (F.mapDerivedCategory ⋙ H.leftDerivedFunctor)
    (E.leftDerivedFunctor ⋙ G.mapDerivedCategory) ε₁ ε₂
    (HomotopyCategory.quasiIso _ (.up ℤ))
    (Functor.isoWhiskerRight eh _root_.DerivedCategory.Qh)
  let adj : E ⊣ U := etaleSheafExtendScalarsAdjunction φ T
  let ad : Etale.scalarExtension φ T ⊣ U.mapDerivedCategory :=
    Adjunction.ofIsRightAdjoint _
  let bd : E.leftDerivedFunctor ⊣ U.mapDerivedCategory :=
    adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
  let scalarIso : Etale.scalarExtension φ T ≅ E.leftDerivedFunctor :=
    ad.leftAdjointUniq bd
  exact derivedSquare ≪≫ Functor.isoWhiskerRight scalarIso.symm G.mapDerivedCategory

end AlgebraicGeometry.ProEtale
