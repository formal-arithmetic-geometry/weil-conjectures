/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingPullbackFixed
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp

/-! # Inverse realization coordinates for finite condensed coefficients

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/
sk-thm-sf-tensor-hom/sk-rem-sf-pf-done/fix-prop-projection-formula.md, final sentence of the proof.
(blueprint: def-sf-finite-intrinsic-realization-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

namespace WeilConjectures.SfFiniteIntrinsicRealizationComparisons

/-- The ordinary constant-coefficient derived category on the small pro-etale site.
Source: `def-sf-finite-intrinsic-realization-comparisons`, first paragraph
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
abbrev OrdinaryDerived (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] [Finite A] (W : Scheme.{u}) :=
  DerivedCategory
    (Sheaf (ProEt.topology W) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))

/-- The derived category of module objects over the pulled-back discrete condensed coefficient.
Source: `def-sf-finite-intrinsic-realization-comparisons`, first paragraph
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
abbrev IntrinsicDerived (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] [Finite A] (W : Scheme.{u}) :=
  DerivedCategory (FiniteDiscreteOrdinary.Internal A W)

/-- The forward realization functor `e_W`.
Source: `lem-sf-module-object-ordinary-coefficient-equivalence`
(blueprint: def-sf-finite-intrinsic-realization-comparisons).
-/
noncomputable abbrev e (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] [Finite A] (W : Scheme.{u}) :
    OrdinaryDerived A W ⥤ IntrinsicDerived A W :=
  (realizationEquivalence A W).functor

/-- The inverse realization functor `h_W`.
Source: `lem-sf-module-object-ordinary-coefficient-equivalence`
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
noncomputable abbrev h (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] [Finite A] (W : Scheme.{u}) :
    IntrinsicDerived A W ⥤ OrdinaryDerived A W :=
  (realizationEquivalence A W).inverse

/-- The unit `η_W : id ≅ h_W e_W` of the specified realization equivalence.
Source: `lem-sf-module-object-ordinary-coefficient-equivalence`
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
noncomputable abbrev unit (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] [Finite A] (W : Scheme.{u}) :
    𝟭 (OrdinaryDerived A W) ≅ e A W ⋙ h A W :=
  (realizationEquivalence A W).unitIso

/-- The counit `ε_W : e_W h_W ≅ id` of the specified realization equivalence.
Source: `lem-sf-module-object-ordinary-coefficient-equivalence`
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
noncomputable abbrev counit (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] [Finite A] (W : Scheme.{u}) :
    h A W ⋙ e A W ≅ 𝟭 (IntrinsicDerived A W) :=
  (realizationEquivalence A W).counitIso

/-- The normalized ring and fixed-scalar encoding on reconstructed section modules.
It is the section equivalence inverse followed by the specified Encoding equivalences.
Source: `lem-sf-module-object-ordinary-coefficient-equivalence`, ring identification;
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
noncomputable def sectionScalarEquivalence
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [Finite A] (T : Scheme.{u}) :=
  (InternalModuleOperations.equivalence (FiniteDiscreteOrdinary.coefficient A) T).symm.trans
    ((chosenEncoding A T).ordinary.trans (chosenEncoding A T).fixed)

/-- Direct-image scalar transport: the identity on normalized coefficient sections,
conjugated from internal modules to their reconstructed section-ring modules.
Source: `lem-sf-module-object-ordinary-coefficient-equivalence`, section action;
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
noncomputable def scalarLowerComparison
    {U T : Scheme.{u}} (f : U ⟶ T) (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] [Finite A] :
    InternalModuleOperations.lowerStar (FiniteDiscreteOrdinary.coefficient A) f ⋙
        (sectionScalarEquivalence A T).functor ≅
      (sectionScalarEquivalence A U).functor ⋙
        ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f := by
  let ET := InternalModuleOperations.equivalence (FiniteDiscreteOrdinary.coefficient A) T
  let EU := InternalModuleOperations.equivalence (FiniteDiscreteOrdinary.coefficient A) U
  let KT := ((chosenEncoding A T).ordinary.trans (chosenEncoding A T).fixed).functor
  let r := InternalModuleOperations.lowerComparison (FiniteDiscreteOrdinary.coefficient A) f
  let k := Iso.isoCompInverse (H := ET) r ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := EU) k
  exact Functor.isoWhiskerRight kr.symm KT ≪≫
    Functor.isoWhiskerLeft EU.inverse
      (encodingPushforwardNatIso A T U f (chosenEncoding A T) (chosenEncoding A U))

/-- Pullback scalar transport, the unique adjunction mate of scalar direct-image transport.
Source: `lem-sfb-internal-module-operations-transport`, normalized adjunctions;
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
noncomputable def scalarUpperComparison
    {U T : Scheme.{u}} (f : U ⟶ T) (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] [Finite A] :
    InternalModuleOperations.upperStar (FiniteDiscreteOrdinary.coefficient A) f ⋙
        (sectionScalarEquivalence A U).functor ≅
      (sectionScalarEquivalence A T).functor ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f := by
  let ET := sectionScalarEquivalence A T
  let EU := sectionScalarEquivalence A U
  let i := scalarLowerComparison f A
  let k := Iso.isoCompInverse (H := ET) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := EU) k
  let a := ET.toAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)
  let b := (InternalModuleOperations.adjunction
    (FiniteDiscreteOrdinary.coefficient A) f).comp EU.toAdjunction
  exact (a.leftAdjointUniq (b.ofNatIsoRight kr)).symm

/-- Open-extension scalar transport, the unique adjunction mate of scalar pullback.
Source: `lem-sfb-internal-module-operations-transport`, open adjunctions;
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
noncomputable def scalarOpenComparison
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [Finite A] :
    InternalModuleOperations.extension (FiniteDiscreteOrdinary.coefficient A) j ⋙
        (sectionScalarEquivalence A T).functor ≅
      (sectionScalarEquivalence A U).functor ⋙
        ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j := by
  let ET := sectionScalarEquivalence A T
  let EU := sectionScalarEquivalence A U
  let i := scalarUpperComparison j A
  let k := Iso.isoCompInverse (H := EU) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := ET) k
  let a := (InternalModuleOperations.openAdjunction
    (FiniteDiscreteOrdinary.coefficient A) j).comp ET.toAdjunction
  let b := EU.toAdjunction.comp
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)
  exact a.leftAdjointUniq (b.ofNatIsoRight kr.symm)

/-- Compose a section-action operation comparison with its scalar-operation comparison.
Insert the section-equivalence unit at the target, apply both comparisons, then remove
its source unit. For pullback and open extension the scalar comparison is the mate
of the preceding operation's scalar comparison.
Source: `lem-sfb-internal-module-operations-transport`, coefficient conjugation;
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
noncomputable def throughSectionComparison
    {D₁ D₂ S₁ S₂ C₁ C₂ : Type*}
    [Category D₁] [Category D₂] [Category S₁] [Category S₂] [Category C₁] [Category C₂]
    (E : D₁ ≌ S₁) (H : D₂ ≌ S₂)
    (P : D₁ ⥤ D₂) (Q : S₁ ⥤ S₂) (K₁ : D₁ ⥤ C₁) (K₂ : D₂ ⥤ C₂)
    (F : C₁ ⥤ C₂) (r : P ⋙ H.functor ≅ E.functor ⋙ Q)
    (scalar : Q ⋙ H.inverse ⋙ K₂ ≅ E.inverse ⋙ K₁ ⋙ F) :
    P ⋙ K₂ ≅ K₁ ⋙ F :=
  Functor.isoWhiskerLeft P (Functor.isoWhiskerRight H.unitIso K₂) ≪≫
    Functor.isoWhiskerRight r (H.inverse ⋙ K₂) ≪≫
    Functor.isoWhiskerLeft E.functor scalar ≪≫
    Functor.isoWhiskerRight E.unitIso.symm (K₁ ⋙ F)

/-- The normalized forward pullback comparison from the section-action encoding.
Source: `lem-sf-module-object-ordinary-coefficient-equivalence`,
`lem-sfb-internal-module-operations-transport`;
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
noncomputable def exactPullbackComparison
    {U T : Scheme.{u}} (f : U ⟶ T) (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] [Finite A] :
    e A T ⋙ (CondensedRing.upperStar (FiniteDiscreteOrdinary.coefficient A) f).mapDerivedCategory ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).mapDerivedCategory ⋙
        e A U := by
  let ET := (chosenEncoding A T).ordinary.trans (chosenEncoding A T).fixed
  let EU := (chosenEncoding A U).ordinary.trans (chosenEncoding A U).fixed
  letI : ET.functor.Additive := inferInstanceAs
    ((chosenEncoding A T).ordinary.functor ⋙ (chosenEncoding A T).fixed.functor).Additive
  letI : EU.functor.Additive := inferInstanceAs
    ((chosenEncoding A U).ordinary.functor ⋙ (chosenEncoding A U).fixed.functor).Additive
  let EX := (chosenEncoding A T).fixedDerived
  let EU' := (chosenEncoding A U).fixedDerived
  let F := (CondensedRing.upperStar (FiniteDiscreteOrdinary.coefficient A) f).mapDerivedCategory
  let G := (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).mapDerivedCategory
  let q : F ⋙ EU'.functor ≅ EX.functor ⋙ G := by
    exact (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (throughSectionComparison
          (InternalModuleOperations.equivalence (FiniteDiscreteOrdinary.coefficient A) T)
          (InternalModuleOperations.equivalence (FiniteDiscreteOrdinary.coefficient A) U)
          (CondensedRing.upperStar (FiniteDiscreteOrdinary.coefficient A) f)
          (InternalModuleOperations.upperStar (FiniteDiscreteOrdinary.coefficient A) f)
          ET.functor EU.functor
          (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)
          (InternalModuleOperations.upperComparison (FiniteDiscreteOrdinary.coefficient A) f)
          (scalarUpperComparison f A)) ≪≫
        Functor.mapDerivedCategoryCompIso _ _
  change EX.inverse ⋙ F ≅ G ⋙ EU'.inverse
  exact Functor.isoWhiskerLeft (EX.inverse ⋙ F) EU'.unitIso ≪≫
    Functor.isoWhiskerLeft EX.inverse (Functor.isoWhiskerRight q EU'.inverse) ≪≫
    Functor.isoWhiskerRight EX.counitIso (G ⋙ EU'.inverse)

/-- The normalized right-derived direct-image comparison from the section-action encoding.
Source: `lem-sf-module-object-ordinary-coefficient-equivalence`,
`lem-sfb-internal-module-operations-transport`;
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
noncomputable def derivedDirectImageComparison
    {U T : Scheme.{u}} (f : U ⟶ T) (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] [Finite A] :
    (CondensedRing.lowerStar (FiniteDiscreteOrdinary.coefficient A) f).rightDerivedFunctor ⋙
        (chosenEncoding A T).fixedDerived.functor ≅
      (chosenEncoding A U).fixedDerived.functor ⋙
        (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctor := by
  let ET := (chosenEncoding A T).ordinary.trans (chosenEncoding A T).fixed
  let EU := (chosenEncoding A U).ordinary.trans (chosenEncoding A U).fixed
  let F := CondensedRing.lowerStar (FiniteDiscreteOrdinary.coefficient A) f
  let G := ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f
  letI : ET.functor.Additive := inferInstanceAs
    ((chosenEncoding A T).ordinary.functor ⋙ (chosenEncoding A T).fixed.functor).Additive
  letI : EU.functor.Additive := inferInstanceAs
    ((chosenEncoding A U).ordinary.functor ⋙ (chosenEncoding A U).fixed.functor).Additive
  change F.rightDerivedFunctor ⋙ ET.functor.mapDerivedCategory ≅
    EU.functor.mapDerivedCategory ⋙ G.rightDerivedFunctor
  exact (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F ET.functor).symm ≪≫
    Functor.rightDerivedFunctorNatIso
      (throughSectionComparison
        (InternalModuleOperations.equivalence (FiniteDiscreteOrdinary.coefficient A) U)
        (InternalModuleOperations.equivalence (FiniteDiscreteOrdinary.coefficient A) T)
        F _ EU.functor ET.functor G
        (InternalModuleOperations.lowerComparison (FiniteDiscreteOrdinary.coefficient A) f)
        (scalarLowerComparison f A)) ≪≫
    Functor.mapDerivedCategoryCompRightDerivedFunctorIso EU.functor G

/-- The exact open-extension comparison in the section-action presentation.
Source: `lem-sfb-internal-module-operations-transport`;
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
noncomputable def derivedOpenComparison
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [Finite A] :
    (CondensedRing.openImmersionLowerShriek
      (FiniteDiscreteOrdinary.coefficient A) j).mapDerivedCategory ⋙
        (chosenEncoding A T).fixedDerived.functor ≅
      (chosenEncoding A U).fixedDerived.functor ⋙
        (ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory := by
  let ET := (chosenEncoding A T).ordinary.trans (chosenEncoding A T).fixed
  let EU := (chosenEncoding A U).ordinary.trans (chosenEncoding A U).fixed
  let F := CondensedRing.openImmersionLowerShriek (FiniteDiscreteOrdinary.coefficient A) j
  let G := ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j
  letI : ET.functor.Additive := inferInstanceAs
    ((chosenEncoding A T).ordinary.functor ⋙ (chosenEncoding A T).fixed.functor).Additive
  letI : EU.functor.Additive := inferInstanceAs
    ((chosenEncoding A U).ordinary.functor ⋙ (chosenEncoding A U).fixed.functor).Additive
  change F.mapDerivedCategory ⋙ ET.functor.mapDerivedCategory ≅
    EU.functor.mapDerivedCategory ⋙ G.mapDerivedCategory
  exact (Functor.mapDerivedCategoryCompIso F ET.functor).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (throughSectionComparison
        (InternalModuleOperations.equivalence (FiniteDiscreteOrdinary.coefficient A) U)
        (InternalModuleOperations.equivalence (FiniteDiscreteOrdinary.coefficient A) T)
        F _ EU.functor ET.functor G
        (InternalModuleOperations.openComparison (FiniteDiscreteOrdinary.coefficient A) j)
        (scalarOpenComparison j A)) ≪≫
      Functor.mapDerivedCategoryCompIso EU.functor G

/-- The inverse comparison obtained by inserting the source counit, applying the
specified forward comparison, and removing the target unit.  For `N` in the intrinsic
source, this is exactly
`h_T F_int N → h_T F_int e_S h_S N → h_T e_T F_ord h_S N → F_ord h_S N`.
Source: the displayed `Delta_F` composite in
`def-sf-finite-intrinsic-realization-comparisons`
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
noncomputable def inverseComparisonAt
    {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    (eS : C₁ ≌ D₁) (eT : C₂ ≌ D₂)
    (Fint : D₁ ⥤ D₂) (Ford : C₁ ⥤ C₂)
    (r : eS.functor ⋙ Fint ≅ Ford ⋙ eT.functor) (N : D₁) :
    eT.inverse.obj (Fint.obj N) ≅ Ford.obj (eS.inverse.obj N) :=
  eT.inverse.mapIso
      (Fint.mapIso (eS.counitIso.symm.app N) ≪≫ r.app (eS.inverse.obj N)) ≪≫
    eT.unitIso.symm.app (Ford.obj (eS.inverse.obj N))

/-- The natural inverse comparison associated with a forward comparison.
Source: the `Delta_F` definition in
`def-sf-finite-intrinsic-realization-comparisons`
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
noncomputable def inverseComparison
    {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    (eS : C₁ ≌ D₁) (eT : C₂ ≌ D₂)
    (Fint : D₁ ⥤ D₂) (Ford : C₁ ⥤ C₂)
    (r : eS.functor ⋙ Fint ≅ Ford ⋙ eT.functor) :
    Fint ⋙ eT.inverse ≅ eS.inverse ⋙ Ford :=
  Functor.isoWhiskerRight eS.counitIso.symm (Fint ⋙ eT.inverse) ≪≫
    Functor.isoWhiskerLeft eS.inverse (Functor.isoWhiskerRight r eT.inverse) ≪≫
    Functor.isoWhiskerLeft (eS.inverse ⋙ Ford) eT.unitIso.symm

/-- The first two arrows of the inverse pullback coordinate, obtained from the
specified forward pullback comparison `r`.
Source: the displayed pullback composite in
`def-sf-finite-intrinsic-realization-comparisons`
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
noncomputable def pullbackComparisonAt
    {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    (eS : C₁ ≌ D₁) (eT : C₂ ≌ D₂)
    (Fint : D₁ ⥤ D₂) (Ford : C₁ ⥤ C₂)
    (r : eS.functor ⋙ Fint ≅ Ford ⋙ eT.functor) (N : D₁) :
    Fint.obj N ≅ eT.functor.obj (Ford.obj (eS.inverse.obj N)) :=
  Fint.mapIso (eS.counitIso.symm.app N) ≪≫ r.app (eS.inverse.obj N)

/-- The inverse pullback coordinate, obtained by applying `h_X` to the pullback
comparison and then the inverse unit `η_X⁻¹`.
Source: the displayed inversePullback definition in
`def-sf-finite-intrinsic-realization-comparisons`
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
noncomputable def inversePullbackAt
    {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    (eS : C₁ ≌ D₁) (eT : C₂ ≌ D₂)
    (Fint : D₁ ⥤ D₂) (Ford : C₁ ⥤ C₂)
    (r : eS.functor ⋙ Fint ≅ Ford ⋙ eT.functor) (N : D₁) :
    eT.inverse.obj (Fint.obj N) ≅ Ford.obj (eS.inverse.obj N) :=
  eT.inverse.mapIso (pullbackComparisonAt eS eT Fint Ford r N) ≪≫
    eT.unitIso.symm.app (Ford.obj (eS.inverse.obj N))

/-- The direct-image coordinate is the generic inverse comparison specialized to the
K-injective right-derived direct image and its section-action comparison.
Source: `def-weil-derived-direct-image`, `lem-sfb-internal-module-operations-transport`,
and the displayed `inverseDirectImage` clause in
`def-sf-finite-intrinsic-realization-comparisons`
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
noncomputable def inverseDirectImageAt
    {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    (eS : C₁ ≌ D₁) (eT : C₂ ≌ D₂)
    (Fint : D₁ ⥤ D₂) (Ford : C₁ ⥤ C₂)
    (r : eS.functor ⋙ Fint ≅ Ford ⋙ eT.functor) (N : D₁) :
    eT.inverse.obj (Fint.obj N) ≅ Ford.obj (eS.inverse.obj N) :=
  inverseComparisonAt eS eT Fint Ford r N

/-- The forward open-extension comparison `r_J`, with `J_int` the exact
module-object extension by zero and `J_ord = D(j_!)` its ordinary realization.
Source: `sk-def-sfb-module-lower-shriek`, `def-weil-extension-by-zero`, and
`lem-sfb-internal-module-operations-transport`;
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
noncomputable def openComparison
    {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [Finite A] :
    e A U ⋙ (CondensedRing.openImmersionLowerShriek
      (FiniteDiscreteOrdinary.coefficient A) j).mapDerivedCategory ≅
      (ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory ⋙ e A Z := by
  let q := derivedOpenComparison j A
  change (chosenEncoding A U).fixedDerived.inverse ⋙
      (CondensedRing.openImmersionLowerShriek
        (FiniteDiscreteOrdinary.coefficient A) j).mapDerivedCategory ≅
    (ProEtale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory ⋙
      (chosenEncoding A Z).fixedDerived.inverse
  exact Functor.isoWhiskerLeft
      ((chosenEncoding A U).fixedDerived.inverse ⋙
        (CondensedRing.openImmersionLowerShriek
          (FiniteDiscreteOrdinary.coefficient A) j).mapDerivedCategory)
      (chosenEncoding A Z).fixedDerived.unitIso ≪≫
    Functor.isoWhiskerLeft (chosenEncoding A U).fixedDerived.inverse
      (Functor.isoWhiskerRight q (chosenEncoding A Z).fixedDerived.inverse) ≪≫
    Functor.isoWhiskerRight (chosenEncoding A U).fixedDerived.counitIso
      ((ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory ⋙
        (chosenEncoding A Z).fixedDerived.inverse)

/-- The open endpoint in inverse coordinates, for `k : U ≅ K`.
Source: the displayed `openCoordinate` composite in
`def-sf-finite-intrinsic-realization-comparisons`
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
noncomputable def openCoordinateAt
    {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    (eS : C₁ ≌ D₁) (eT : C₂ ≌ D₂)
    (Jint : D₁ ⥤ D₂) (Jord : C₁ ⥤ C₂)
    (rJ : eS.functor ⋙ Jint ≅ Jord ⋙ eT.functor)
    {U K : D₁} (k : U ≅ K) :
    eT.inverse.obj (Jint.obj U) ≅ Jord.obj (eS.inverse.obj K) :=
  eT.inverse.mapIso (Jint.mapIso k) ≪≫
    inverseComparisonAt eS eT Jint Jord rJ K

end WeilConjectures.SfFiniteIntrinsicRealizationComparisons

namespace WeilConjectures.SfFiniteIntrinsicRealizationComparisons

/-- The canonical right-derived direct-image comparison for the finite condensed coefficient,
constructed from the K-injective derived comparison for the normalized encoding.
Source: `def-weil-derived-direct-image`, `lem-sfb-internal-module-operations-transport`;
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
noncomputable def directImageComparison
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] [Finite A] :
    e A X ⋙ (CondensedRing.lowerStar (FiniteDiscreteOrdinary.coefficient A) f).rightDerivedFunctor ≅
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctor ⋙
        e A Y := by
  let EX := (chosenEncoding A X).fixedDerived
  let EY := (chosenEncoding A Y).fixedDerived
  let F := (CondensedRing.lowerStar (FiniteDiscreteOrdinary.coefficient A) f).rightDerivedFunctor
  let G := (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctor
  let q := derivedDirectImageComparison f A
  change EX.inverse ⋙ F ≅ G ⋙ EY.inverse
  exact Functor.isoWhiskerLeft (EX.inverse ⋙ F) EY.unitIso ≪≫
    Functor.isoWhiskerLeft EX.inverse (Functor.isoWhiskerRight q EY.inverse) ≪≫
    Functor.isoWhiskerRight EX.counitIso (G ⋙ EY.inverse)

/-- The inverse direct-image coordinate specialized to the canonical right-derived comparison.
Source: `def-sf-finite-intrinsic-realization-comparisons`;
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
noncomputable def inverseDirectImage
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] [Finite A]
    (N : IntrinsicDerived A X) :
    (h A Y).obj
      ((CondensedRing.lowerStar
        (FiniteDiscreteOrdinary.coefficient A) f).rightDerivedFunctor.obj N) ≅
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctor.obj
        ((h A X).obj N) :=
  inverseComparisonAt (realizationEquivalence A X) (realizationEquivalence A Y)
    (CondensedRing.lowerStar (FiniteDiscreteOrdinary.coefficient A) f).rightDerivedFunctor
    (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctor
    (directImageComparison f A) N

/-- The intrinsic exact extension by zero on module objects, promoted termwise to the
derived category.  Its coefficient is the actual pulled-back discrete condensed ring.
Source: `sk-def-sfb-module-lower-shriek`;
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
noncomputable abbrev intrinsicOpenDerived
    {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [Finite A] :
    IntrinsicDerived A U ⥤ IntrinsicDerived A Z :=
  (CondensedRing.openImmersionLowerShriek
      (FiniteDiscreteOrdinary.coefficient A) j).mapDerivedCategory


/-- The total left-derived intrinsic pullback, canonically identified with exact
termwise pullback by `leftDerivedUpperStarIsoMapDerivedCategory`.
Source: `def-weil-derived-pullback-tensor-hom`;
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
noncomputable abbrev intrinsicPullback
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] [Finite A] :
    IntrinsicDerived A Y ⥤ IntrinsicDerived A X :=
  (CondensedRing.upperStar (FiniteDiscreteOrdinary.coefficient A) f).leftDerivedFunctor

/-- The ordinary total left-derived pullback on fixed scalar module sheaves.
Source: `def-weil-derived-pullback-tensor-hom`;
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
noncomputable abbrev ordinaryPullback
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] [Finite A] :
    OrdinaryDerived A Y ⥤ OrdinaryDerived A X :=
  (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).leftDerivedFunctor

/-- The specified forward comparison for total left-derived pullbacks: first use
exact-to-left-derived identification, then the localized normalized section comparison.
Source: `def-weil-derived-pullback-tensor-hom`, `lem-sfb-internal-module-operations-transport`;
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
noncomputable def pullbackComparison
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] [Finite A] :
    e A Y ⋙ intrinsicPullback f A ≅ ordinaryPullback f A ⋙ e A X :=
  Functor.isoWhiskerLeft (e A Y)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
      (FiniteDiscreteOrdinary.coefficient A) f) ≪≫
    exactPullbackComparison f A ≪≫
    Functor.isoWhiskerRight
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).symm (e A X)

/-- The two specified arrows before applying inverse realization in pullback coordinates.
Source: the displayed pullback formula in `def-sf-finite-intrinsic-realization-comparisons`;
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
noncomputable def pullback
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] [Finite A] (N : IntrinsicDerived A Y) :
    (intrinsicPullback f A).obj N ≅ (e A X).obj ((ordinaryPullback f A).obj ((h A Y).obj N)) :=
  pullbackComparisonAt (realizationEquivalence A Y) (realizationEquivalence A X)
    (intrinsicPullback f A) (ordinaryPullback f A) (pullbackComparison f A) N

/-- The inverse pullback coordinate specialized to the specified finite realization.
Source: the displayed inversePullback formula in `def-sf-finite-intrinsic-realization-comparisons`;
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
noncomputable def inversePullback
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] [Finite A] (N : IntrinsicDerived A Y) :
    (h A X).obj ((intrinsicPullback f A).obj N) ≅
      (ordinaryPullback f A).obj ((h A Y).obj N) :=
  (h A X).mapIso (pullback f A N) ≪≫
    (unit A X).symm.app ((ordinaryPullback f A).obj ((h A Y).obj N))

/-- The ordinary exact extension by zero localized termwise, namely `D(j_!)`.
Source: `def-weil-extension-by-zero`;
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
noncomputable abbrev ordinaryOpenDerived
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [Finite A] : OrdinaryDerived A X ⥤ OrdinaryDerived A Z :=
  (ProEtale.openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory

/-- The forward open comparison for the open factor of the specified compactification
`f = c.i ≫ c.g`, with `c.g` proper. No compactification is chosen or changed.
Source: `def-weil-compactifications-refinements`, `sk-def-sfb-module-lower-shriek`;
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
noncomputable def compactificationOpenComparison
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [Finite A] :
    e A X ⋙ intrinsicOpenDerived c.i A ≅ ordinaryOpenDerived c.i A ⋙ e A c.Z :=
  openComparison c.i A

/-- The open endpoint for arbitrary intrinsic objects and an isomorphism between them,
using the constructed forward comparison of the fixed compactification's open factor.
Source: the displayed openCoordinate formula in `def-sf-finite-intrinsic-realization-comparisons`;
(blueprint: def-sf-finite-intrinsic-realization-comparisons). -/
noncomputable def openCoordinate
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [Finite A] {U K : IntrinsicDerived A X} (k : U ≅ K) :
    (h A c.Z).obj ((intrinsicOpenDerived c.i A).obj U) ≅
      (ordinaryOpenDerived c.i A).obj ((h A X).obj K) :=
  openCoordinateAt (realizationEquivalence A X) (realizationEquivalence A c.Z)
    (intrinsicOpenDerived c.i A) (ordinaryOpenDerived c.i A)
    (compactificationOpenComparison c A) k

end WeilConjectures.SfFiniteIntrinsicRealizationComparisons
