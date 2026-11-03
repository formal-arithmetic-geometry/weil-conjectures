/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
public import WeilConjectures.AlgebraicGeometry.Vector.VectorPurityScalarSingle
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackIsoExistence
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate

/-! # Finite smooth coefficient arrows

Source: main-20261015 blueprint, sk-lem-sp-reduction and its compatibility proof
(blueprint: def-pur-finite-smooth-coefficient-arrows).

## Main definitions

* `CoefficientLineComparison`: generator-normalized reduction of the actual root line.
* `pullbackTwistComparison`, `proLambda`: canonical purity-source balancing.
* `proCoefficientMap`, `proCompactCoefficientMap`: the actual exceptional and support maps.
* `proPullbackMap`, `proTwistMap`: the separate transported comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity
/-- The quotient cocycle diagram, with both scalar associators displayed. In every
application below all six scalar functors and all three coefficient arrows are the
specified canonical maps. This notation avoids re-elaborating their expanded domains.
Source: sk-lem-sp-reduction/compatibilities (2)
(blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def QuotientCocycle {C₁ C₂ C₃ D₁ D₂ D₃ : Type v}
    [Category.{w} C₁] [Category.{w} C₂] [Category.{w} C₃]
    [Category.{w} D₁] [Category.{w} D₂] [Category.{w} D₃]
    (s₁₂ : C₁ ⥤ C₂) (s₂₃ : C₂ ⥤ C₃) (s₁₃ : C₁ ⥤ C₃)
    (t₁₂ : D₁ ⥤ D₂) (t₂₃ : D₂ ⥤ D₃) (t₁₃ : D₁ ⥤ D₃)
    (a : s₁₂ ⋙ s₂₃ ≅ s₁₃) (b : t₁₂ ⋙ t₂₃ ≅ t₁₃)
    (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (F₃ : C₃ ⥤ D₃)
    (c₁₂ : ∀ K : C₁, t₁₂.obj (F₁.obj K) ⟶ F₂.obj (s₁₂.obj K))
    (c₂₃ : ∀ K : C₂, t₂₃.obj (F₂.obj K) ⟶ F₃.obj (s₂₃.obj K))
    (c₁₃ : ∀ K : C₁, t₁₃.obj (F₁.obj K) ⟶ F₃.obj (s₁₃.obj K)) (K : C₁) : Prop :=
  t₂₃.map (c₁₂ K) ≫ c₂₃ (s₁₂.obj K) ≫ F₃.map (a.hom.app K) =
    b.hom.app (F₁.obj K) ≫ c₁₃ K

variable {A : Type (u + 1)} [CommRing A]
variable {B : Type (u + 1)} [CommRing B]

/-- The published ordinary scalar extension, with its functor type elaborated once.
Source: Stacks 06YY (blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def ordinaryScalar (phi : A →+* B) (T : Scheme.{u}) :
    DerivedCategoryModule A T ⥤ DerivedCategoryModule B T :=
  scalarExtension phi T

/-- The inverse component of the existing canonical scalar/pullback comparison.
Source: Stacks 07A4 (blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def ordinaryPullbackMap (phi : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategoryModule A Y) :
    (ordinaryScalar phi X).obj ((ordinaryFinitePullback A f).obj K) ⟶
      (ordinaryFinitePullback B f).obj ((ordinaryScalar phi Y).obj K) :=
  (scalarPullbackIso phi f).inv.app K

/-- The canonical shift comparison of scalar extension, as the mate of exact
restriction's shift. Source: Stacks 06YY
(blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def scalarShiftIso (phi : A →+* B) (T : Scheme.{u}) (i : ℤ) :
    shiftFunctor _ i ⋙ ordinaryScalar phi T ≅ ordinaryScalar phi T ⋙ shiftFunctor _ i :=
  letI : (ordinaryScalar phi T).CommShift ℤ :=
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology phi)).leftAdjointCommShift ℤ
  (ordinaryScalar phi T).commShiftIso i

section CompactSingle
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.pbcFixedScalarExtension
attribute [local instance] cachedEtaleGroth cachedEtaleSheafify
  cachedEtaleMonoidalPreadditive cachedEtaleCoproducts cachedEtaleColimits
  cachedEtaleFlatResolution cachedEtaleInjectiveResolution
  cachedEtaleExactColimits cachedEtaleTensor4 cachedEtaleTensor12
  cachedEtaleTensor23 cachedEtaleTensorColimits cachedEtaleTensorFlipColimits
section Abstract
variable {C : Type v} {D : Type w} [Category.{u + 1} C] [Category.{u + 1} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{u + 1} C] [HasDerivedCategory.{u + 1} D]
  (E : C ⥤ D) (U : D ⥤ C) [E.Additive] [U.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (a : E ⊣ U) {L : DerivedCategory C ⥤ DerivedCategory D}
  (ad : L ⊣ U.mapDerivedCategory) (M : C)
-- Compare the cochain unit with the degree-zero exact-restriction comparison.
private theorem cochainSingleAdjunct :
    (ad.homEquiv _ _).symm
        (DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app
          ((CochainComplex.singleFunctor C 0).obj M)) ≫
            U.mapDerivedCategoryFactors.inv.app
              ((E.mapHomologicalComplex (.up ℤ)).obj
                ((CochainComplex.singleFunctor C 0).obj M))) ≫
      DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
        E (.up ℤ) 0).hom.app M) =
    (ad.homEquiv _ _).symm ((DerivedCategory.singleFunctor C 0).map
      (a.unit.app M) ≫ (U.mapDerivedCategorySingleFunctor 0).inv.app (E.obj M)) := by
  rw [← ad.homEquiv_naturality_right_symm]
  congr 1
  rw [Category.assoc]
  have hn := U.mapDerivedCategoryFactors.inv.naturality
    ((HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).hom.app M)
  dsimp only [Functor.comp_map] at hn
  erw [← hn]
  erw [← DerivedCategory.Q.map_comp_assoc]
  have hc : (a.mapHomologicalComplex (.up ℤ)).unit.app
      ((CochainComplex.singleFunctor C 0).obj M) ≫
        (U.mapHomologicalComplex (.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).hom.app M) =
      (CochainComplex.singleFunctor C 0).map (a.unit.app M) ≫
        (HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).inv.app (E.obj M) := by
    ext n
    by_cases hn : n = 0
    · subst n
      simp only [HomologicalComplex.comp_f, Adjunction.mapHomologicalComplex_unit_app_f,
        Functor.mapHomologicalComplex_map_f]
      simp [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
        HomologicalComplex.single_map_f_self]
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M n hn).eq_of_src _ _
  erw [hc, DerivedCategory.Q.map_comp]
  have hs := U.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app
    (E.obj M)
  have hs' : (U.mapDerivedCategorySingleFunctor 0).inv.app (E.obj M) =
      DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).inv.app
            (E.obj M)) ≫
        U.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor D 0).obj
          (E.obj M)) := by
    exact (Iso.eq_comp_inv (U.mapDerivedCategoryFactors.app
      ((CochainComplex.singleFunctor D 0).obj (E.obj M)))).mpr hs
  rw [hs']
  simp only [Category.assoc]
  rfl
end Abstract

/-- The adjunction transpose on a single sheaf equals the original localized cochain
formula, for arbitrary abelian categories and an exact right adjoint. Specializing E,
U, L, a and ad to ordinary scalar extension/restriction and their specified derived
adjunction gives the formula previously used to define scalarSingleMap.
Source: Stacks 06YY (blueprint: def-pur-finite-smooth-coefficient-arrows). -/
theorem scalarSingleMap_cochain
    {C : Type v} {D : Type w} [Category.{u + 1} C] [Category.{u + 1} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{u + 1} C] [HasDerivedCategory.{u + 1} D]
    (E : C ⥤ D) (U : D ⥤ C) [E.Additive] [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (a : E ⊣ U) (L : DerivedCategory C ⥤ DerivedCategory D)
    (ad : L ⊣ U.mapDerivedCategory) (M : C) :
    L.map ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app M) ≫
      (ad.homEquiv _ _).symm
        (DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app
              ((CochainComplex.singleFunctor C 0).obj M) ≫
            (NatTrans.mapHomologicalComplex a.unit (.up ℤ)).app
              ((CochainComplex.singleFunctor C 0).obj M) ≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ U)) (.up ℤ)).inv.app
              ((CochainComplex.singleFunctor C 0).obj M)) ≫
          U.mapDerivedCategoryFactors.inv.app
            ((E.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor C 0).obj M))) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).hom.app M) ≫
      (DerivedCategory.singleFunctorIsoCompQ D 0).inv.app (E.obj M) =
    AlgebraicGeometry.Etale.purityAdjunctionSingleMap E U L
      U.mapDerivedCategory (DerivedCategory.singleFunctor C 0)
      (DerivedCategory.singleFunctor D 0) a ad (U.mapDerivedCategorySingleFunctor 0) M := by
  change L.map (𝟙 _) ≫ _ ≫ _ ≫ 𝟙 _ = _
  conv_lhs =>
    rw [L.map_id, Category.id_comp]
    rhs
    rw [Category.comp_id]
  rw [← AlgebraicGeometry.Etale.mapComplex_unit_formula]
  unfold AlgebraicGeometry.Etale.purityAdjunctionSingleMap
  have h := cochainSingleAdjunct E U a ad M
  dsimp only [Functor.id_obj, Functor.comp_obj] at h
  with_unfolding_all exact h

end CompactSingle

/-- The derived scalar counit at a single sheaf, with all localization identifications.
Source: Stacks 06YY (blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def scalarSingleMap (phi : A →+* B) (T : Scheme.{u})
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (ordinaryScalar phi T).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj M) ⟶
      (_root_.DerivedCategory.singleFunctor _ 0).obj
        ((ProEtale.etaleSheafExtendScalars phi T).obj M) :=
  AlgebraicGeometry.Etale.purityScalarSingleMap phi T M

/-- The root-line reduction, fixed on the root power map and every scalar/root generator.
The derived isomorphism is the actual scalar counit followed by that sheaf map.
Source: sk-lem-sp-reduction (blueprint: def-pur-finite-smooth-coefficient-arrows). -/
structure CoefficientLineComparison (phi : A →+* B) (N M : ℕ)
    (hA : (N : A) = 0) (hB : (M : B) = 0) (T : Scheme.{u}) where
  roots : T.rootsOfUnitySheaf N ⟶ T.rootsOfUnitySheaf M
  roots_power : roots ≫ kernel.ι (M • 𝟙 T.gmSheaf) =
    (N / M) • kernel.ι (N • 𝟙 T.gmSheaf)
  sheafIso : (ProEtale.etaleSheafExtendScalars phi T).obj
      (Scheme.finiteEtaleTateLine T N A hA) ≅ Scheme.finiteEtaleTateLine T M B hB
  generators : ∀ (W : T.Etaleᵒᵖ) (a : A) (z : (T.rootsOfUnitySheaf N).obj.obj W),
    ((ProEtale.etaleSheafExtendScalarsAdjunction phi T).homEquiv _ _
      sheafIso.hom).hom.app W (Scheme.finiteEtaleTateOneGenerator A N T hA W a z) =
      Scheme.finiteEtaleTateOneGenerator B M T hB W (phi a) (roots.hom.app W z)
  derivedIso : (ordinaryScalar phi T).obj (ordinaryFiniteLine A N hA T) ≅
    ordinaryFiniteLine B M hB T
  derived_normalization : derivedIso.hom =
    scalarSingleMap phi T (Scheme.finiteEtaleTateLine T N A hA) ≫
      (_root_.DerivedCategory.singleFunctor _ 0).map sheafIso.hom

/-- The zero-fold root comparison is the canonical scalar unit comparison.
Source: sk-lem-sp-reduction (blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def scalarZeroLineIso (phi : A →+* B) (N M : ℕ) (hA : (N : A) = 0)
    (hB : (M : B) = 0) (T : Scheme.{u}) :
    (ordinaryScalar phi T).obj (line A N hA T 0) ≅ line B M hB T 0 :=
  (ordinaryScalar phi T).mapIso
      (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) T) ≪≫
    ExceptionalCoefficients.unitIso phi T ≪≫
    (singleFunctorObjUnitIso (ModuleCat.{u + 1} B) T).symm

/-- One step of root-tensor reduction, using scalar tensor and shift comparisons.
Source: sk-lem-sp-reduction (blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def CoefficientLineComparison.tensorPowerStep {phi : A →+* B} {N M : ℕ}
    {hA : (N : A) = 0} {hB : (M : B) = 0} {T : Scheme.{u}}
    (e : CoefficientLineComparison phi N M hA hB T) (d : ℕ)
    (previous : (ordinaryScalar phi T).obj (line A N hA T d) ≅ line B M hB T d) :
    (ordinaryScalar phi T).obj (line A N hA T (d + 1)) ≅ line B M hB T (d + 1) :=
  (ExceptionalCoefficients.tensorIso phi T).app
      (line A N hA T d, (ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) ≪≫
    ((derivedTensor (ModuleCat.{u + 1} B) T).mapIso previous).app _ ≪≫
    ((derivedTensor (ModuleCat.{u + 1} B) T).obj (line B M hB T d)).mapIso
      ((scalarShiftIso phi T (2 : ℤ)).app _ ≪≫
        (shiftFunctor _ (2 : ℤ)).mapIso e.derivedIso)

/-- Canonical reduction of the ordered shifted tensor: scalar unit at zero, then
normalized tensor and shift comparisons on each concrete root-line factor.
Source: sk-lem-sp-reduction (blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def CoefficientLineComparison.tensorPower {phi : A →+* B} {N M : ℕ}
    {hA : (N : A) = 0} {hB : (M : B) = 0} {T : Scheme.{u}}
    (e : CoefficientLineComparison phi N M hA hB T) (d : ℕ) :
    (ordinaryScalar phi T).obj (line A N hA T d) ≅ line B M hB T d :=
  Nat.rec (motive := fun i ↦
    (ordinaryScalar phi T).obj (line A N hA T i) ≅ line B M hB T i)
    (scalarZeroLineIso phi N M hA hB T) (fun i previous ↦ e.tensorPowerStep i previous) d

/-- Coefficient extension on the pro-etale site, fixed by its adjunction to restriction.
Source: Stacks 06YY (blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def proScalar (phi : A →+* B) (T : Scheme.{u}) :
    proCategory A T ⥤ proCategory B T :=
  @ProEtale.pbcFixedScalarExtension.{u} T.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} T.ProEt) (Scheme.ProEt.topology T)
    A B inferInstance inferInstance phi

/-- The origin/scalar comparison is the transpose of the inverse of the specified
site/scalar comparison followed by scalar extension of the comparison counit.
Source: sk-lem-sp-reduction (blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def originReductionMap (phi : A →+* B) (T : Scheme.{u}) (K : proCategory A T) :
    (ordinaryScalar phi T).obj ((origin A T).obj K) ⟶
      (origin B T).obj ((proScalar phi T).obj K) :=
  (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} B) T).homEquiv _ _
    ((ProEtale.pbcComparisonReduction T phi).inv.app ((origin A T).obj K) ≫
      (proScalar phi T).map
        ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).counit.app K))

/-- Reduction of the actual comparison root line, with the canonical site/scalar mate.
Source: sk-lem-sp-reduction/compatibilities (3)
(blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def proTwistMap {phi : A →+* B} {N M : ℕ} {hA : (N : A) = 0} {hB : (M : B) = 0}
    {T : Scheme.{u}} (d : ℕ) (e : CoefficientLineComparison phi N M hA hB T) :
    (proScalar phi T).obj ((comparison A T).obj (line A N hA T d)) ⟶
      (comparison B T).obj (line B M hB T d) :=
  (ProEtale.pbcComparisonReduction T phi).hom.app (line A N hA T d) ≫
    (comparison B T).map (e.tensorPower d).hom

/-- The pure pullback comparison toward the chosen ordinary origin.
Source: sk-lem-sp-reduction (blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def pullbackToOrigin {X Y : Scheme.{u}} (f : X ⟶ Y) (K : proCategory A Y) :
    (proPullback A f).obj K ⟶
      (comparison A X).obj
        ((ordinaryFinitePullback A f).obj ((origin A Y).obj K)) :=
  (proPullback A f).map
      (originInverse A Y K) ≫
    (sitePullbackIso A f).hom.app ((origin A Y).obj K)

/-- The reverse pure pullback comparison, using the actual origin counit.
Source: sk-lem-sp-reduction (blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def pullbackFromOrigin {X Y : Scheme.{u}} (f : X ⟶ Y) (K : proCategory A Y) :
    (comparison A X).obj
        ((ordinaryFinitePullback A f).obj ((origin A Y).obj K)) ⟶
      (proPullback A f).obj K :=
  (sitePullbackIso A f).inv.app ((origin A Y).obj K) ≫
    (proPullback A f).map
      ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).counit.app K)

/-- Scalar/pullback balancing on the original pro-etale object. Both origin counits
are displayed in the preceding comparisons, so this transports ordinary balancing.
Source: sk-lem-sp-reduction/compatibilities (3)
(blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def proPullbackMap (phi : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : proCategory A Y) :
    (proScalar phi X).obj
        ((proPullback A f).obj K) ⟶
      (proPullback B f).obj
        ((proScalar phi Y).obj K) :=
  (proScalar phi X).map (pullbackToOrigin f K) ≫
    (ProEtale.pbcComparisonReduction X phi).hom.app
      ((ordinaryFinitePullback A f).obj ((origin A Y).obj K)) ≫
    (comparison B X).map
      ((scalarPullbackIso phi f).inv.app ((origin A Y).obj K) ≫
        (ordinaryFinitePullback B f).map
          (originReductionMap phi Y K)) ≫
    pullbackFromOrigin f ((proScalar phi Y).obj K)

end AlgebraicGeometry.Etale.FiniteSmoothPurity
