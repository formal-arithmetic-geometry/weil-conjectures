/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PbcQbarCompletedPullback
public import Sheaf.Paper.PbcActualRingedExchange
public import Sheaf.CategoryTheory.LocalizationInverseImageCoherence
public import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-! # Data for localized ordinary pullback normalization

Source: Stacks Project, Tags 03CB, 0D6D, 07A4; Bhatt--Scholze, Remark 6.8.15.
(blueprint: def-per-localized-ordinary-pullback-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.LocalizedOrdinary

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual completed coefficient sheaf B. Source: Stacks 099M
(blueprint: def-per-localized-ordinary-pullback-data). -/
abbrev B (X : Scheme.{u}) : Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
  pbcAdicCompletion X (pbcIntegralDatum l E)

variable (ϖ : PbcIntegralRing l E)

/-- The constant chosen uniformizer section. Source: BS 6.8.15
(blueprint: def-per-localized-ordinary-pullback-data). -/
def uniformizer (X : Scheme.{u}) :
    ((B l E X).obj ⋙ CategoryTheory.forget CommRingCat.{u + 1}).sections :=
  pbcCompletedScalarSections X (pbcIntegralDatum l E) ϖ

attribute [-instance] WeilConjectures.integralCoefficientRingSheafify in
/-- The actual sheaf localization B[1/varpi]. Source: Stacks 03EL
(blueprint: def-per-localized-ordinary-pullback-data). -/
abbrev R (X : Scheme.{u}) : Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
  ringedLocalizationRingOfUniverses.{u + 1, u + 1, u} (B l E X) (uniformizer l E ϖ X)

attribute [-instance] WeilConjectures.integralCoefficientRingSheafify in
/-- The localization unit. Source: Stacks 03EL
(blueprint: def-per-localized-ordinary-pullback-data). -/
abbrev iota (X : Scheme.{u}) :=
  ringedLocalizationRingUnitOfUniverses.{u + 1, u + 1, u} (B l E X) (uniformizer l E ϖ X)

/-- Ordinary localization as actual scalar extension. Source: Stacks 03EL
(blueprint: def-per-localized-ordinary-pullback-data). -/
abbrev F₀ (X : Scheme.{u}) := pbcExtend (iota l E ϖ X)

/-- Unbounded derived scalar localization. Source: Stacks 06YY
(blueprint: def-per-localized-ordinary-pullback-data). -/
abbrev F (X : Scheme.{u}) := pbcDerivedExtend (iota l E ϖ X)

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- The integral tensor-unit section, typed on the actual pulled-back chart.
This is the existing normalized adjunction unit, with no change in its data.
Source: Stacks 03D2 (blueprint: def-per-localized-ordinary-pullback-data). -/
abbrev integralUnitSection (M : pbcModules X (B l E X)) (V : X.ProEt)
    (m : M.val.obj (op V)) :
    ((pbcActualModulePull g (pbcIntegralDatum l E)).obj M).val.obj
      (op ((proEtaleBaseChange g).obj V)) :=
  pbcActualModuleUnitSection g (pbcIntegralDatum l E) M V m

/-- Ordinary ringed pullback along the localized structural map, without requiring it
invertible. Source: Stacks 03D2
(blueprint: def-per-localized-ordinary-pullback-data). -/
abbrev G₀ (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (R l E ϖ X) ⟶ R l E ϖ Y) :=
  proEtaleRingModulePullback g (R l E ϖ X)
    ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (R l E ϖ X)) (Iso.refl _) ⋙
      pbcExtend c

/-- Exact inverse image followed by derived scalar extension. Source: Stacks 06YY
(blueprint: def-per-localized-ordinary-pullback-data). -/
abbrev G (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (R l E ϖ X) ⟶ R l E ϖ Y) :=
  adicTowerPullback g (R l E ϖ X) ⋙ pbcDerivedExtend c

/-- Computation counit on arbitrary complexes. Source: Stacks 06YY
(blueprint: def-per-localized-ordinary-pullback-data). -/
def counit (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (R l E ϖ X) ⟶ R l E ϖ Y)
    (P : CochainComplex (pbcModules X (R l E ϖ X)) ℤ) :
    (G l E ϖ g c).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((G₀ l E ϖ g c).mapHomologicalComplex (.up ℤ)).obj P) :=
  (pbcDerivedExtend c).map
    ((proEtaleRingDerivedPullbackFactors g (R l E ϖ X)
      ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (R l E ϖ X))
        (Iso.refl _)).hom.app P) ≫
    pbcComplexCounit c
      (((proEtaleRingModulePullback g (R l E ϖ X)
        ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (R l E ϖ X))
          (Iso.refl _)).mapHomologicalComplex (.up ℤ)).obj P)

/-- The ordinary pullback tensor unit on a base-changed chart. Source: Stacks 03D2
(blueprint: def-per-localized-ordinary-pullback-data). -/
def unitSection
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (R l E ϖ X) ⟶ R l E ϖ Y)
    (M : pbcModules X (R l E ϖ X)) (V : X.ProEt) (m : M.val.obj (op V)) :=
  pbcTensorSection c
    ((proEtaleRingModulePullback g (R l E ϖ X)
      ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (R l E ϖ X))
        (Iso.refl _)).obj M) (op ((proEtaleBaseChange g).obj V)) 1
    (proEtaleRingModuleUnitSection g (R l E ϖ X)
      ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (R l E ϖ X))
        (Iso.refl _) M V m)

/-- A coefficient section pulled through the ring adjunction and structural map.
Source: Stacks 03D2 (blueprint: def-per-localized-ordinary-pullback-data). -/
def scalarSection
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (R l E ϖ X) ⟶ R l E ϖ Y)
    (V : X.ProEt) (e : (R l E ϖ X).obj.obj (op V)) :=
  c.hom.app (op ((proEtaleBaseChange g).obj V))
    (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app (R l E ϖ X)).hom.app (op V) e)


/-- Data for the specified localization comparison. Its ring map is fixed by the
localization unit. Its ordinary comparison is fixed on tensor-unit generators,
and its derived comparison is fixed by the ordinary computation counits.
Source: Stacks 03EL, 0D6D, 07A4; BS 6.8.15
(blueprint: def-per-localized-ordinary-pullback-data). -/
structure Edge where
  coefficient : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (R l E ϖ X) ⟶ R l E ϖ Y
  coefficient_unit : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map (iota l E ϖ X) ≫
    coefficient = completedCoefficientMap g (pbcIntegralDatum l E) ≫ iota l E ϖ Y
  ordinary : pbcActualModulePull g (pbcIntegralDatum l E) ⋙ F₀ l E ϖ Y ≅
    F₀ l E ϖ X ⋙ G₀ l E ϖ g coefficient
  ordinary_unit : ∀ (M : pbcModules X (B l E X)) (V : X.ProEt)
    (m : M.val.obj (op V)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
      (pbcTensorSection (iota l E ϖ Y)
        ((pbcActualModulePull g (pbcIntegralDatum l E)).obj M)
        (op ((proEtaleBaseChange g).obj V)) 1
        (integralUnitSection l E g M V m)) =
      unitSection l E ϖ g coefficient ((F₀ l E ϖ X).obj M) V
        (pbcTensorSection (iota l E ϖ X) M (op V) 1 m)
  ordinary_tensor : ∀ (M : pbcModules X (B l E X)) (V : X.ProEt)
    (m : M.val.obj (op V))
    (b : (B l E Y).obj.obj (op ((proEtaleBaseChange g).obj V)))
    (e : (R l E ϖ Y).obj.obj (op ((proEtaleBaseChange g).obj V))),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
      (pbcTensorSection (iota l E ϖ Y)
        ((pbcActualModulePull g (pbcIntegralDatum l E)).obj M)
        (op ((proEtaleBaseChange g).obj V)) e
        (b • integralUnitSection l E g M V m)) =
    (e * (iota l E ϖ Y).hom.app (op ((proEtaleBaseChange g).obj V)) b) •
      unitSection l E ϖ g coefficient ((F₀ l E ϖ X).obj M) V
        (pbcTensorSection (iota l E ϖ X) M (op V) 1 m)
  ordinary_inverse_unit : ∀ (M : pbcModules X (B l E X)) (V : X.ProEt)
    (m : M.val.obj (op V))
    (e : (R l E ϖ Y).obj.obj (op ((proEtaleBaseChange g).obj V))),
    (ordinary.inv.app M).val.app (op ((proEtaleBaseChange g).obj V))
      (e • unitSection l E ϖ g coefficient ((F₀ l E ϖ X).obj M) V
        (pbcTensorSection (iota l E ϖ X) M (op V) 1 m)) =
    pbcTensorSection (iota l E ϖ Y)
      ((pbcActualModulePull g (pbcIntegralDatum l E)).obj M)
      (op ((proEtaleBaseChange g).obj V)) e
      (integralUnitSection l E g M V m)
  derived : pbcActualDerivedPull g (pbcIntegralDatum l E) ⋙ F l E ϖ Y ≅
    F l E ϖ X ⋙ G l E ϖ g coefficient
  derived_model : ∀ P : CochainComplex (pbcModules X (B l E X)) ℤ,
    @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      X.ProEt inferInstance (essentiallySmallSelf.{0} _) (ProEt.topology X) (B l E X) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology X) (R := B l E X) (P.X n)) →
    derived.hom.app (DerivedCategory.Q.obj P) ≫
      (G l E ϖ g coefficient).map (pbcComplexCounit (iota l E ϖ X) P) ≫
      counit l E ϖ g coefficient
        (((F₀ l E ϖ X).mapHomologicalComplex (.up ℤ)).obj P) =
    (F l E ϖ Y).map (pbcActualPullComplexCounit g (pbcIntegralDatum l E) P) ≫
      pbcComplexCounit (iota l E ϖ Y)
        (((pbcActualModulePull g (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)

variable {Z : Scheme.{u}} (h : Z ⟶ Y)

/-- The composition comparisons with their rational tensor-generator value, inverse
unit insertion, and derived representative equation. The last equation is the
specified delta-compositor square on every unbounded derived object.
Source: Stacks 0D6D, 07A4; BS 6.8.15
(blueprint: def-per-localized-ordinary-pullback-data). -/
structure Composition (ag : Edge l E ϖ g) (ah : Edge l E ϖ h) (ac : Edge l E ϖ (h ≫ g)) where
  coefficient_comp : ac.coefficient =
    (proEtaleRingInverseImageComp h g).hom.app (R l E ϖ X) ≫
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map ag.coefficient ≫ ah.coefficient
  ordinary : G₀ l E ϖ g ag.coefficient ⋙ G₀ l E ϖ h ah.coefficient ≅
    G₀ l E ϖ (h ≫ g) ac.coefficient
  ordinary_tensor : ∀ (M : pbcModules X (R l E ϖ X)) (V : X.ProEt)
    (m : M.val.obj (op V))
    (e' : (R l E ϖ Y).obj.obj (op ((proEtaleBaseChange g).obj V)))
    (e'' : (R l E ϖ Z).obj.obj
      (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))),
    (ordinary.hom.app M).val.app
      (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))
      (e'' • unitSection l E ϖ h ah.coefficient ((G₀ l E ϖ g ag.coefficient).obj M)
        ((proEtaleBaseChange g).obj V)
        (e' • unitSection l E ϖ g ag.coefficient M V m)) =
    (e'' * scalarSection l E ϖ h ah.coefficient ((proEtaleBaseChange g).obj V) e') •
      (((G₀ l E ϖ (h ≫ g) ac.coefficient).obj M).val.map
        ((MorphismProperty.Over.pullbackComp h g).inv.app V).op
          (unitSection l E ϖ (h ≫ g) ac.coefficient M V m))
  ordinary_inverse_unit : ∀ (M : pbcModules X (R l E ϖ X)) (V : X.ProEt)
    (m : M.val.obj (op V)),
    (ordinary.inv.app M).val.app
      (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))
      (((G₀ l E ϖ (h ≫ g) ac.coefficient).obj M).val.map
        ((MorphismProperty.Over.pullbackComp h g).inv.app V).op
          (unitSection l E ϖ (h ≫ g) ac.coefficient M V m)) =
    unitSection l E ϖ h ah.coefficient ((G₀ l E ϖ g ag.coefficient).obj M)
      ((proEtaleBaseChange g).obj V) (unitSection l E ϖ g ag.coefficient M V m)
  derived : G l E ϖ g ag.coefficient ⋙ G l E ϖ h ah.coefficient ≅
    G l E ϖ (h ≫ g) ac.coefficient
  derived_model : ∀ P : CochainComplex (pbcModules X (R l E ϖ X)) ℤ,
    @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      X.ProEt inferInstance (essentiallySmallSelf.{0} _)
      (ProEt.topology X) (R l E ϖ X) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology X) (R := R l E ϖ X) (P.X n)) →
    derived.hom.app (DerivedCategory.Q.obj P) ≫ counit l E ϖ (h ≫ g) ac.coefficient P =
    (G l E ϖ h ah.coefficient).map (counit l E ϖ g ag.coefficient P) ≫
      counit l E ϖ h ah.coefficient
        (((G₀ l E ϖ g ag.coefficient).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)
  ordinary_square : ∀ M : pbcModules X (B l E X),
    (F₀ l E ϖ Z).map ((pbcActualModulePullCompIso h g (pbcIntegralDatum l E)).inv.app M) ≫
      ac.ordinary.hom.app M =
    ah.ordinary.hom.app ((pbcActualModulePull g (pbcIntegralDatum l E)).obj M) ≫
      (G₀ l E ϖ h ah.coefficient).map (ag.ordinary.hom.app M) ≫
      ordinary.hom.app ((F₀ l E ϖ X).obj M)
  ordinary_mixed_tensor : ∀ (M : pbcModules X (B l E X)) (V : X.ProEt)
    (m : M.val.obj (op V))
    (b' : (B l E Y).obj.obj (op ((proEtaleBaseChange g).obj V)))
    (e'' : (R l E ϖ Z).obj.obj
      (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))),
    (((F₀ l E ϖ Z).map
        ((pbcActualModulePullCompIso h g (pbcIntegralDatum l E)).inv.app M) ≫
      ac.ordinary.hom.app M).val.app
      (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V))))
      (pbcTensorSection (iota l E ϖ Z)
        ((pbcActualModulePull h (pbcIntegralDatum l E)).obj
          ((pbcActualModulePull g (pbcIntegralDatum l E)).obj M))
        (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V))) e''
        (integralUnitSection l E h
          ((pbcActualModulePull g (pbcIntegralDatum l E)).obj M)
          ((proEtaleBaseChange g).obj V)
          (b' • integralUnitSection l E g M V m))) =
    (e'' * (iota l E ϖ Z).hom.app
      (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))
      ((completedCoefficientMap h (pbcIntegralDatum l E)).hom.app
        (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))
        (((proEtaleSheafAdjunction h CommRingCat.{u + 1}).unit.app (B l E Y)).hom.app
          (op ((proEtaleBaseChange g).obj V)) b'))) •
      (((G₀ l E ϖ (h ≫ g) ac.coefficient).obj ((F₀ l E ϖ X).obj M)).val.map
        ((MorphismProperty.Over.pullbackComp h g).inv.app V).op
        (unitSection l E ϖ (h ≫ g) ac.coefficient ((F₀ l E ϖ X).obj M) V
          (pbcTensorSection (iota l E ϖ X) M (op V) 1 m)))
  derived_square : ∀ K : PbcCompletedDerived X (pbcIntegralDatum l E),
    (F l E ϖ Z).map ((pbcActualDerivedPullCompIso h g (pbcIntegralDatum l E)).inv.app K) ≫
      ac.derived.hom.app K =
    ah.derived.hom.app ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K) ≫
      (G l E ϖ h ah.coefficient).map (ag.derived.hom.app K) ≫
      derived.hom.app ((F l E ϖ X).obj K)

/-- Identity comparisons multiply the scalar into the module; their derived maps
are computed by exactly those chain maps on flat-term K-flat complexes.
Source: Stacks 0D6D, 07A4 (blueprint: def-per-localized-ordinary-pullback-data). -/
structure Identity (X : Scheme.{u}) (a : Edge l E ϖ (𝟙 X)) where
  coefficient_id : a.coefficient = (proEtaleRingInverseImageId X).hom.app (R l E ϖ X)
  ordinary : G₀ l E ϖ (𝟙 X) a.coefficient ≅ 𝟭 _
  ordinary_tensor : ∀ (M : pbcModules X (R l E ϖ X)) (V : X.ProEt)
    (m : M.val.obj (op V))
    (e : (R l E ϖ X).obj.obj (op ((proEtaleBaseChange (𝟙 X)).obj V))),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange (𝟙 X)).obj V))
      (e • unitSection l E ϖ (𝟙 X) a.coefficient M V m) =
    e • M.val.map ((MorphismProperty.Over.pullbackId _ _ X).hom.app V).op m
  derived : G l E ϖ (𝟙 X) a.coefficient ≅ 𝟭 _
  derived_model : ∀ P : CochainComplex (pbcModules X (R l E ϖ X)) ℤ,
    @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      X.ProEt inferInstance (essentiallySmallSelf.{0} _)
      (ProEt.topology X) (R l E ϖ X) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology X) (R := R l E ϖ X) (P.X n)) →
    derived.hom.app (DerivedCategory.Q.obj P) = counit l E ϖ (𝟙 X) a.coefficient P ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex ordinary (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app P)
  ordinary_square : ∀ M : pbcModules X (B l E X),
    a.ordinary.hom.app M ≫ ordinary.hom.app ((F₀ l E ϖ X).obj M) =
      (F₀ l E ϖ X).map ((pbcActualModulePullIdIso (pbcIntegralDatum l E) X).hom.app M)
  derived_square : ∀ K : PbcCompletedDerived X (pbcIntegralDatum l E),
    a.derived.hom.app K ≫ derived.hom.app ((F l E ϖ X).obj K) =
      (F l E ϖ X).map ((pbcActualDerivedPullIdIso (pbcIntegralDatum l E) X).hom.app K)


/-- Quotient transition, projection, identity and constant-scalar normalization.
Index n denotes the positive exponent n+1. Source: Stacks 03CB; BS 6.8.15
(blueprint: def-per-localized-ordinary-pullback-data). -/
structure Coefficients : Prop where
  finite_comp : ∀ n : ℕ,
    completedFiniteCoefficientMap (h ≫ g) (pbcIntegralDatum l E) n =
      (proEtaleRingInverseImageComp h g).hom.app
          ((pbcAdicRings X (pbcIntegralDatum l E)).obj (op n)) ≫
        (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
          (completedFiniteCoefficientMap g (pbcIntegralDatum l E) n) ≫
        completedFiniteCoefficientMap h (pbcIntegralDatum l E) n
  completed_comp : completedCoefficientMap (h ≫ g) (pbcIntegralDatum l E) =
    (proEtaleRingInverseImageComp h g).hom.app (B l E X) ≫
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
        (completedCoefficientMap g (pbcIntegralDatum l E)) ≫
      completedCoefficientMap h (pbcIntegralDatum l E)
  projection_comp : ∀ n : ℕ,
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
        (completedCoefficientMap g (pbcIntegralDatum l E)) ≫
      completedCoefficientMap h (pbcIntegralDatum l E) ≫
      pbcAdicProjection Z (pbcIntegralDatum l E) n =
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
        ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
          (pbcAdicProjection X (pbcIntegralDatum l E) n)) ≫
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
        (completedFiniteCoefficientMap g (pbcIntegralDatum l E) n) ≫
      completedFiniteCoefficientMap h (pbcIntegralDatum l E) n
  finite_id : ∀ n : ℕ,
    completedFiniteCoefficientMap (𝟙 X) (pbcIntegralDatum l E) n =
      (proEtaleRingInverseImageId X).hom.app
        ((pbcAdicRings X (pbcIntegralDatum l E)).obj (op n))
  completed_id : completedCoefficientMap (𝟙 X) (pbcIntegralDatum l E) =
    (proEtaleRingInverseImageId X).hom.app (B l E X)
  transitions : ∀ {S T : Scheme.{u}} (f : S ⟶ T) {b a : ℕᵒᵖ} (q : b ⟶ a),
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        ((pbcAdicRings T (pbcIntegralDatum l E)).map q) ≫
      completedFiniteCoefficientMap f (pbcIntegralDatum l E) a.unop =
    completedFiniteCoefficientMap f (pbcIntegralDatum l E) b.unop ≫
      (pbcAdicRings S (pbcIntegralDatum l E)).map q
  scalar : ∀ {S T : Scheme.{u}} (f : S ⟶ T) (V : T.ProEt) (a : PbcIntegralRing l E),
    (completedCoefficientMap f (pbcIntegralDatum l E)).hom.app
      (op ((proEtaleBaseChange f).obj V))
      (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app (B l E T)).hom.app
        (op V) (pbcCompletedSection T (pbcIntegralDatum l E) (op V) a)) =
    pbcCompletedSection S (pbcIntegralDatum l E)
      (op ((proEtaleBaseChange f).obj V)) a

end AlgebraicGeometry.Scheme.LocalizedOrdinary
