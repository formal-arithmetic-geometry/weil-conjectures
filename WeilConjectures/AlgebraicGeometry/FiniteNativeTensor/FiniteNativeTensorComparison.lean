/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCtfInternalEtaleRealization
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.CategoryTheory.Adjunction.SixFunctors.FiniteCoefficientTensorPullbackEncoding
public import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSiteCoherence
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothTensorDuality
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.ModuleRingedToposDerivedComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonUpperStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientHeartEncoding
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientHeartTensor
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingCompactification
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.CategoryTheory.ExactMonoidalEquivalenceDerived.ExactMonoidalEquivalenceDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # Finite native tensor comparison

Source: the current blueprint, sk-prop-sp-composition, finite tensor maps, and
sk-thm-purity-transport, Steps 1 and 3.
(blueprint: lem-pur-finite-native-tensor-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.FiniteNativeTensor
open FiniteDiscreteOrdinary
-- Discard the imported instance with a free coefficient universe.
attribute [-instance] WeilConjectures.scalarReductionSiteSmall
attribute [local instance 20000] sheafBraidedCategory sheafSymmetricCategory
  sheafMonoidalCategory sheafMonoidalClosed
  preservesColimitsOfSize_tensorLeft_sheaf preservesColimitsOfSize_tensorRight_sheaf
attribute [local instance 2000] Mod.monoidalCategory Mod.monoidalClosed
attribute [local irreducible] Mod.monoidalClosed
attribute [local irreducible] Sheaf.monoidalCategory SheafOfModules.monoidalCategory

variable (A : Type u) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]

/-- The ordinary etale finite-Tor constructible domain, testing all degree-zero modules.
Source: the domain convention of the node
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def etaleDomain (T : Scheme.{u}) :
    ObjectProperty (Etale.DerivedCategoryModule (ULift.{u + 1} A) T) :=
  fun K ↦ Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) T K ∧
    ∃ a b : ℤ, a ≤ b ∧
      Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} A) T a b K

/-- The native domain uses the published constant local models and all Tor test modules.
Source: the domain convention of the node
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def internalDomain (T : Scheme.{u}) : ObjectProperty (DerivedCategory.{u + 1} (Internal A T)) := by
  letI : EssentiallySmall.{u + 1} T.ProEt := WeilConjectures.scalarReductionSiteSmall.{u, u} T
  exact fun K ↦ constantModelBoundedConstructible (coefficient A) T K ∧
    _root_.DerivedCategory.finiteTorAmplitude.{u + 1} (Internal A T) K

/-- The ordinary pro-etale version of the same domain.
Source: the final sentence of the node
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def ordinaryDomain (T : Scheme.{u}) : ObjectProperty
    (DerivedCategory.{u + 1} (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))) := by
  letI : EssentiallySmall.{u + 1} T.ProEt := WeilConjectures.scalarReductionSiteSmall.{u, u} T
  exact fun K ↦ ordinaryBoundedConstructible A T K ∧
    _root_.DerivedCategory.finiteTorAmplitude _ K

/-- The identity-coefficient heart comparison with the redundant scalar restriction removed.
Source: the section-action encoding and identity scalar restriction
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def heartIdentityIso (T : Scheme.{u}) (E : Encoding A T) :
    coefficientHeartEncoding A (Iso.refl (Mon.mk (coefficient A))) T E ≅
      (E.ordinary.trans E.fixed).functor :=
  Functor.isoWhiskerRight
    (Mod.comapCongr (coefficientMap_id T) ≪≫ Mod.comapId _) _ ≪≫
    Functor.leftUnitor _

/-- The pure-tensor normalized heart structure. The existence theorem used here retains
its pure-tensor formula; hence it determines the tensorator by the balanced universal
property, rather than choosing an unspecified monoidal structure.
Source: normalized coefficient-heart tensor comparison
(blueprint: lem-pur-finite-native-tensor-comparison). -/
@[instance_reducible] def heartMonoidal (T : Scheme.{u}) (E : Encoding A T) :
    (E.ordinary.functor ⋙ E.fixed.functor).Monoidal := by
  letI : EssentiallySmall.{u + 1} T.ProEt := WeilConjectures.scalarReductionSiteSmall.{u, u} T
  letI : (coefficientHeartEncoding A (Iso.refl (Mon.mk (coefficient A))) T E).Monoidal := by
    unfold coefficientHeartEncoding
    rw [E.ordinary_functor, E.fixed_functor]
    exact Classical.choose
      (coefficientSectionTensor_normalized A (Iso.refl (Mon.mk (coefficient A))) T E.ringIso)
  exact Functor.Monoidal.transport (heartIdentityIso A T E)

/-- Derivation of the normalized heart tensorator, with its actual localization square.
Source: termwise exact monoidal equivalence and K-flat derived tensor
(blueprint: lem-pur-finite-native-tensor-comparison). -/
@[instance_reducible] def encodingMonoidal (T : Scheme.{u}) (E : Encoding A T) :
    E.fixedDerived.functor.Monoidal := by
  letI : EssentiallySmall.{u + 1} T.ProEt := WeilConjectures.scalarReductionSiteSmall.{u, u} T
  let F := (E.ordinary.trans E.fixed).functor
  letI : F.Monoidal := heartMonoidal A T E
  letI : F.Additive := inferInstanceAs (E.ordinary.functor ⋙ E.fixed.functor).Additive
  letI : F.PreservesFlat := Functor.preservesFlat_of_isEquivalence F
  letI : F.leftDerivedFunctor.Monoidal := F.leftDerivedFunctorMonoidal
  exact Functor.Monoidal.transport F.leftDerivedFunctorIsoMapDerivedCategory

/-- Canonical section-action comparison obtained from the identity on sections and
its adjunction mate, then derived by the localization universal property.
Source: finite discrete ordinary encoding, compactification transport
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def nativeencodingPullbackIso {T U : Scheme.{u}} (f : U ⟶ T)
    (eT : Encoding A T) (eU : Encoding A U) :
    CondensedRing.upperStar (coefficient A) f ⋙ (eU.ordinary.trans eU.fixed).functor ≅
      (eT.ordinary.trans eT.fixed).functor ⋙
        upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f := by
  let ET := eT.ordinary.trans eT.fixed
  let EU := eU.ordinary.trans eU.fixed
  let R := lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  let i : CondensedRing.lowerStar (coefficient A) f ⋙ ET.functor ≅ EU.functor ⋙ R :=
    encodingPushforwardNatIso A T U f eT eU
  let k := Iso.isoCompInverse (H := ET) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := EU) k
  let a := ET.toAdjunction.comp
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) f)
  let b := (CondensedRing.upperStarLowerStarAdjunction (coefficient A) f).comp
    EU.toAdjunction
  exact (a.leftAdjointUniq (b.ofNatIsoRight kr)).symm

/-- Canonical section-action comparison obtained from the identity on sections and
its adjunction mate, then derived by the localization universal property.
Source: finite discrete ordinary encoding, compactification transport
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def nativeencodingOpenShriekIso {T U : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] (eT : Encoding A T) (eU : Encoding A U) :
    CondensedRing.openImmersionLowerShriek (coefficient A) j ⋙
        (eT.ordinary.trans eT.fixed).functor ≅
      (eU.ordinary.trans eU.fixed).functor ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) j := by
  let ET := eT.ordinary.trans eT.fixed
  let EU := eU.ordinary.trans eU.fixed
  let i := nativeencodingPullbackIso A j eT eU
  let k := Iso.isoCompInverse (H := EU) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := ET) k
  let a := (CondensedRing.openImmersionLowerShriekUpperStarAdjunction
    (coefficient A) j).comp ET.toAdjunction
  let b := EU.toAdjunction.comp
    (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) j)
  exact a.leftAdjointUniq (b.ofNatIsoRight kr.symm)

/-- Canonical section-action comparison obtained from the identity on sections and
its adjunction mate, then derived by the localization universal property.
Source: finite discrete ordinary encoding, compactification transport
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def nativeencodingDerivedPushforwardIso {T U : Scheme.{u}} (f : U ⟶ T)
    (eT : Encoding A T) (eU : Encoding A U) :
    (CondensedRing.lowerStar (coefficient A) f).rightDerivedFunctor ⋙
        eT.fixedDerived.functor ≅
      eU.fixedDerived.functor ⋙
        (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).rightDerivedFunctor := by
  let ET := eT.ordinary.trans eT.fixed
  let EU := eU.ordinary.trans eU.fixed
  let F := CondensedRing.lowerStar (coefficient A) f
  let G := lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  letI : ET.functor.Additive := inferInstanceAs
    (eT.ordinary.functor ⋙ eT.fixed.functor).Additive
  letI : EU.functor.Additive := inferInstanceAs
    (eU.ordinary.functor ⋙ eU.fixed.functor).Additive
  change F.rightDerivedFunctor ⋙ ET.functor.mapDerivedCategory ≅
    EU.functor.mapDerivedCategory ⋙ G.rightDerivedFunctor
  exact (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
      F ET.functor).symm ≪≫
    Functor.rightDerivedFunctorNatIso (encodingPushforwardNatIso A T U f eT eU) ≪≫
    Functor.mapDerivedCategoryCompRightDerivedFunctorIso EU.functor G

/-- Canonical section-action comparison obtained from the identity on sections and
its adjunction mate, then derived by the localization universal property.
Source: finite discrete ordinary encoding, compactification transport
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def nativeencodingDerivedOpenShriekIso {T U : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] (eT : Encoding A T) (eU : Encoding A U) :
    (CondensedRing.openImmersionLowerShriek (coefficient A) j).mapDerivedCategory ⋙
        eT.fixedDerived.functor ≅
      eU.fixedDerived.functor ⋙
        (openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).mapDerivedCategory := by
  let ET := eT.ordinary.trans eT.fixed
  let EU := eU.ordinary.trans eU.fixed
  let F := CondensedRing.openImmersionLowerShriek (coefficient A) j
  let G := openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) j
  letI : ET.functor.Additive := inferInstanceAs
    (eT.ordinary.functor ⋙ eT.fixed.functor).Additive
  letI : EU.functor.Additive := inferInstanceAs
    (eU.ordinary.functor ⋙ eU.fixed.functor).Additive
  change F.mapDerivedCategory ⋙ ET.functor.mapDerivedCategory ≅
    EU.functor.mapDerivedCategory ⋙ G.mapDerivedCategory
  exact (Functor.mapDerivedCategoryCompIso F ET.functor).symm ≪≫
    Functor.mapDerivedCategoryNatIso (nativeencodingOpenShriekIso A j eT eU) ≪≫
    Functor.mapDerivedCategoryCompIso EU.functor G


/-- The actual open/proper encoding paste for one compactification.
Source: the sectionwise proper comparison and the counit-normalized open comparison
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def compactEncoding (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient A) c ⋙
        (E Y).fixedDerived.functor ≅
      (E X).fixedDerived.functor ⋙
        rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) c :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (nativeencodingDerivedPushforwardIso A c.g (E Y) (E c.Z)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (nativeencodingDerivedOpenShriekIso A c.i (E c.Z) (E X)) _ ≪≫
    Functor.associator _ _ _

/-- The specified compact-support comparison, on bounded-below ordinary etale inputs.
Source: proper counit mate followed by the open comparison, then inverse encoding
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def compactComparison (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :
    (internalEtaleRealization A Y (E Y)).obj
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).obj M.obj) ≅
      (CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient A) c).obj
        ((internalEtaleRealization A X (E X)).obj M.obj) :=
  (E Y).fixedDerived.inverse.mapIso
      ((compactSupportSiteComparison (ULift.{u + 1} A) c).symm.app M) ≪≫
    (E Y).fixedDerived.inverse.mapIso
      ((rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).mapIso
          ((E X).fixedDerived.counitIso.app _).symm) ≪≫
    (E Y).fixedDerived.inverse.mapIso
      ((compactEncoding A E c).symm.app _) ≪≫
    ((E Y).fixedDerived.unitIso.app _).symm

/-- The internal projection is the actual proper counit projection followed by the
inverse open unit projection and the compactification pullback compositor.
Source: definition of P in the node and the upstream open projection construction
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def nativeProjection {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (Internal A X)) (K : DerivedCategory (Internal A Y)) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient A) c).obj M ⊗ K ⟶
      (CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient A) c).obj
        (M ⊗ (CondensedRing.upperStar (coefficient A) f).leftDerivedFunctor.obj K) := by
  let J := (CondensedRing.openImmersionLowerShriek (coefficient A) c.i).mapDerivedCategory
  let R := (CondensedRing.lowerStar (coefficient A) c.g).rightDerivedFunctor
  let P := (CondensedRing.upperStar (coefficient A) c.g).leftDerivedFunctor
  let t : (CondensedRing.upperStar (coefficient A) f).leftDerivedFunctor ≅
      P ⋙ (CondensedRing.upperStar (coefficient A) c.i).leftDerivedFunctor :=
    eqToIso (congrArg (fun a ↦ (CondensedRing.upperStar (coefficient A) a).leftDerivedFunctor)
      c.comm) ≪≫ CondensedRing.leftDerivedUpperStarComp (coefficient A) c.i c.g
  let pp := Adjunction.rightAdjointProjectionMap
    (CondensedRing.derivedUpperStarLowerStarAdjunction (coefficient A) c.g)
    (CondensedRing.leftDerivedUpperStarTensor (coefficient A) c.g)
  let op := CondensedRing.openImmersionProjectionComparison' (coefficient A) c.i
  exact (pp.app (J.obj M)).app K ≫
    R.map (inv ((op.app M).app (P.obj K)) ≫ J.map (M ◁ (t.app K).inv))

/-- The derived encoding pullback comparison is induced by the specified sectionwise
adjunction comparison, using the canonical exact/left-derived identifications.
Source: normalized internal/sectionwise pullback transport
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def encodingDerivedPull (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (E Y).fixedDerived.functor ⋙
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).leftDerivedFunctor ≅
      (CondensedRing.upperStar (coefficient A) f).leftDerivedFunctor ⋙
        (E X).fixedDerived.functor :=
by
  let NX := (E X).ordinary.functor ⋙ (E X).fixed.functor
  let NY := (E Y).ordinary.functor ⋙ (E Y).fixed.functor
  exact Functor.isoWhiskerRight NY.leftDerivedFunctorIsoMapDerivedCategory.symm _ ≪≫
    Functor.leftDerivedFunctorCompNatIso
      (CondensedRing.upperStar (coefficient A) f) NX NY
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f)
      (nativeencodingPullbackIso A f (E Y) (E X)).symm ≪≫
    Functor.isoWhiskerLeft _ NX.leftDerivedFunctorIsoMapDerivedCategory

/-- The canonical monoidal structure on derived site inverse image.
Source: the native K-flat left-derived tensor comparison
(blueprint: lem-pur-finite-native-tensor-comparison). -/
@[instance_reducible] def siteMonoidal (T : Scheme.{u}) :
    let F := (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).mapDerivedCategory
    F.Monoidal := by
  let F := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T
  letI : F.leftDerivedFunctor.Monoidal := F.leftDerivedFunctorMonoidal
  exact Functor.Monoidal.transport F.leftDerivedFunctorIsoMapDerivedCategory

/-- The internal realization's tensor structure is site inverse image followed by the
inverse of the normalized section-action equivalence.
Source: the definition V = E inverse composed with nu inverse image
(blueprint: lem-pur-finite-native-tensor-comparison). -/
@[instance_reducible] def realizationMonoidal (T : Scheme.{u}) (E : Encoding A T) :
    (internalEtaleRealization A T E).Monoidal := by
  let F := (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).mapDerivedCategory
  letI : F.Monoidal := siteMonoidal A T
  letI : E.fixedDerived.functor.Monoidal := encodingMonoidal A T E
  letI : E.fixedDerived.inverse.Monoidal := E.fixedDerived.inverseMonoidal
  exact inferInstanceAs
    ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).mapDerivedCategory ⋙
      E.fixedDerived.inverse).Monoidal

/-- The inverse-encoding pullback square, fixed by the adjunction-preserving heart square.
Source: inversion of the normalized section-action pullback comparison
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def inverseEncodingPull (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (E Y).fixedDerived.inverse ⋙
        (CondensedRing.upperStar (coefficient A) f).leftDerivedFunctor ≅
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).leftDerivedFunctor ⋙
        (E X).fixedDerived.inverse :=
  Iso.inverseCompIso (G := (E Y).fixedDerived)
    (Iso.isoCompInverse (H := (E X).fixedDerived) (encodingDerivedPull A E f).symm ≪≫
      Functor.associator _ _ _)

/-- The stipulated composite of the site square and the inverse-encoding square.
Source: the pullback comparison specified in the node
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def realizationPull (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).leftDerivedFunctor ⋙
        internalEtaleRealization A X (E X) ≅
      internalEtaleRealization A Y (E Y) ⋙
        (CondensedRing.upperStar (coefficient A) f).leftDerivedFunctor :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (derivedComparisonUpperStarUpperStarIso
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (inverseEncodingPull A E f).symm ≪≫
    (Functor.associator _ _ _).symm

/-- `false` is the internal model and `true` the ordinary pro-etale model. These are
exactly the published ambient derived categories, without replacement of their objects.
Source: the two versions of the statement
(blueprint: lem-pur-finite-native-tensor-comparison). -/
abbrev Native (ordinary : Bool) (T : Scheme.{u}) :=
  if ordinary then DerivedCategory (Sheaf (Scheme.ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1} A))) else DerivedCategory (Internal A T)

/-- The existing derived tensors, with their native associators and unitors.
Source: the two ambient derived tensor constructions
(blueprint: lem-pur-finite-native-tensor-comparison). -/
instance nativeMonoidal (ordinary : Bool) (T : Scheme.{u}) :
    MonoidalCategory (Native A ordinary T) := by
  cases ordinary <;> dsimp [Native] <;> infer_instance

/-- The finite-Tor constructible property in either presentation.
Source: the two domain conventions in the statement
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def nativeDomain (ordinary : Bool) (T : Scheme.{u}) : ObjectProperty (Native A ordinary T) :=
  match ordinary with
  | false => internalDomain A T
  | true => ordinaryDomain A T

/-- The actual realization in either presentation.
Source: V = E inverse nu inverse image, or simply nu inverse image
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def realization (ordinary : Bool) (E : ∀ T : Scheme.{u}, Encoding A T) (T : Scheme.{u}) :
    Etale.DerivedCategoryModule (ULift.{u + 1} A) T ⥤ Native A ordinary T := by
  cases ordinary
  · exact internalEtaleRealization A T (E T)
  · exact (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).mapDerivedCategory

/-- The actual compactification compact support functor in either presentation.
Source: Rp_* j_! in the node
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def nativeCompact (ordinary : Bool) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) : Native A ordinary X ⥤ Native A ordinary Y := by
  cases ordinary
  · exact CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient A) c
  · exact rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) c

/-- The published total derived inverse image in either presentation.
Source: the pullback used by the projection map in the node
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def nativeUpper (ordinary : Bool) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Native A ordinary Y ⥤ Native A ordinary X := by
  cases ordinary
  · exact (CondensedRing.upperStar (coefficient A) f).leftDerivedFunctor
  · exact (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).leftDerivedFunctor

/-- The actual proper-mate/open compactification projection in either presentation.
Source: P in the statement
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def nativeP (ordinary : Bool) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : Native A ordinary X) (K : Native A ordinary Y) :
    (nativeCompact A ordinary c).obj M ⊗ K ⟶
      (nativeCompact A ordinary c).obj (M ⊗ (nativeUpper A ordinary f).obj K) := by
  cases ordinary
  · exact nativeProjection A c M K
  · exact ((projectionMapOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).app M).app K

/-- The fixed ambient monoidal realization, in either presentation.
Source: normalized heart tensors, then K-flat derivation
(blueprint: lem-pur-finite-native-tensor-comparison). -/
@[instance_reducible] def nativeRealizationMonoidal (ordinary : Bool)
    (E : ∀ T : Scheme.{u}, Encoding A T) (T : Scheme.{u}) :
    (realization A ordinary E T).Monoidal := by
  cases ordinary
  · exact realizationMonoidal A T (E T)
  · exact siteMonoidal A T

/-- The specified ambient pullback square in either presentation.
Source: the normalized site square followed, in the internal case, by inverse encoding
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def nativePullComparison (ordinary : Bool) (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).leftDerivedFunctor ⋙
        realization A ordinary E X ≅
      realization A ordinary E Y ⋙ nativeUpper A ordinary f := by
  cases ordinary
  · exact realizationPull A E f
  · exact (derivedComparisonUpperStarUpperStarIso
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).symm

/-- The specified proper/open comparison in either presentation, at a bounded-below input.
Source: B in the statement
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def nativeB (ordinary : Bool) (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :
    (realization A ordinary E Y).obj
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).obj M.obj) ≅
      (nativeCompact A ordinary c).obj ((realization A ordinary E X).obj M.obj) := by
  cases ordinary
  · exact compactComparison A E c M
  · exact (compactSupportSiteComparison (ULift.{u + 1} A) c).symm.app M

/-- The canonical bounded-below witness supplied by bounded constructibility.
Source: boundedness in the domain definition
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def etalePlus (T : Scheme.{u}) (M : (etaleDomain A T).FullSubcategory) :
    DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} A))) :=
  ⟨M.obj, by
    obtain ⟨_, a, b, _, h⟩ := M.property.1
    exact ⟨a, (DerivedCategory.isGE_iff M.obj a).2 (fun i hi ↦ h i (Or.inl hi))⟩⟩

/-- Restriction of the actual realization to its prescribed full domains. The proof
argument asserts membership and changes neither the objects nor the morphisms.
Source: the restriction of V in the statement
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def restrictRealization (ordinary : Bool) (E : ∀ T : Scheme.{u}, Encoding A T)
    (T : Scheme.{u}) (h : ∀ M : (etaleDomain A T).FullSubcategory,
      nativeDomain A ordinary T ((realization A ordinary E T).obj M.obj)) :
    (etaleDomain A T).FullSubcategory ⥤ (nativeDomain A ordinary T).FullSubcategory :=
  ObjectProperty.lift _ ((etaleDomain A T).ι ⋙ realization A ordinary E T) h

/-- Domain equivalence and the inherited normalized strong monoidal structure.
The tensorator and unit equations pin this structure to the ambient realization.
Essential surjectivity includes every native finite-Tor constructible input.
Source: the first assertion and final transport assertion of the node
(blueprint: lem-pur-finite-native-tensor-comparison). -/
class DomainComparison (ordinary : Bool) (E : ∀ T : Scheme.{u}, Encoding A T)
    (T : Scheme.{u}) where
  [etaleMonoidal : (etaleDomain A T).IsMonoidal]
  [nativeMonoidal : (nativeDomain A ordinary T).IsMonoidal]
  mem : ∀ M : (etaleDomain A T).FullSubcategory,
    nativeDomain A ordinary T ((realization A ordinary E T).obj M.obj)
  [monoidal : (restrictRealization A ordinary E T mem).Monoidal]
  [equivalence : (restrictRealization A ordinary E T mem).IsEquivalence]
  tensor_normalization : ∀ M N,
    (nativeDomain A ordinary T).ι.map
        (Functor.LaxMonoidal.μ (restrictRealization A ordinary E T mem) M N) =
      (nativeRealizationMonoidal A ordinary E T).toLaxMonoidal.μ M.obj N.obj
  unit_normalization :
    (nativeDomain A ordinary T).ι.map
        (Functor.LaxMonoidal.ε (restrictRealization A ordinary E T mem)) =
      (nativeRealizationMonoidal A ordinary E T).toLaxMonoidal.ε


section Categorical

variable {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
  [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalCategory C'] [MonoidalCategory D']

/-- The tensor map is the actual adjunction transpose of the inverse projection,
followed by the counit at the unit and the left unitor.
Source: current blueprint, sk-prop-sp-composition, finite tensor maps
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def tensorTranspose (F : C ⥤ D) (U : D ⥤ C)
    (P : ∀ M : C, ∀ K : D, F.obj M ⊗ K ⟶ F.obj (M ⊗ U.obj K))
    (hP : ∀ M K, IsIso (P M K)) (G : D ⥤ C) (adj : F ⊣ G) (K : D) :
    G.obj (𝟙_ D) ⊗ U.obj K ⟶ G.obj K := by
  letI := hP (G.obj (𝟙_ D)) K
  exact adj.homEquiv _ _
    (inv (P (G.obj (𝟙_ D)) K) ≫ (adj.counit.app (𝟙_ D) ▷ K) ≫ (λ_ K).hom)

/-- The two canonical-map squares on the prescribed full finite-Tor domains.
The projections, compact-support comparison, pullback comparison and tensor structures
are parameters fixed by their geometric constructions, not existential substitutes.
Source: current blueprint, sk-prop-sp-composition, finite tensor maps
(blueprint: lem-pur-finite-native-tensor-comparison). -/
structure TensorAdjunctionTransport
    (F : C ⥤ D) (F' : C' ⥤ D') (U : D ⥤ C) (U' : D' ⥤ C')
    (V : C ⥤ C') (W : D ⥤ D') [V.Monoidal] [W.Monoidal]
    (B : F ⋙ W ≅ V ⋙ F') (pull : U ⋙ V ≅ W ⋙ U')
    (P : ∀ M : C, ∀ K : D, F.obj M ⊗ K ⟶ F.obj (M ⊗ U.obj K))
    (P' : ∀ M : C', ∀ K : D', F'.obj M ⊗ K ⟶ F'.obj (M ⊗ U'.obj K)) where
  projection : ∀ M K,
    W.map (P M K) ≫ B.hom.app (M ⊗ U.obj K) ≫
        F'.map ((Functor.Monoidal.μIso V M (U.obj K)).inv ≫
          (𝟙 (V.obj M) ⊗ₘ pull.hom.app K)) =
      (Functor.Monoidal.μIso W (F.obj M) K).inv ≫
        (B.hom.app M ⊗ₘ 𝟙 (W.obj K)) ≫ P' (V.obj M) (W.obj K)
  projection_isIso : ∀ M K, IsIso (P M K)
  nativeProjection_isIso : ∀ M K, IsIso (P' M K)
  adjoints : ∀ (G : D ⥤ C) (G' : D' ⥤ C') (adj : F ⊣ G) (adj' : F' ⊣ G'),
    ∃ a : G ⋙ V ≅ W ⋙ G',
      (∀ K, B.hom.app (G.obj K) ≫ F'.map (a.hom.app K) ≫
        adj'.counit.app (W.obj K) = W.map (adj.counit.app K)) ∧
      (∀ b : G ⋙ V ≅ W ⋙ G',
        (∀ K, B.hom.app (G.obj K) ≫ F'.map (b.hom.app K) ≫
          adj'.counit.app (W.obj K) = W.map (adj.counit.app K)) → b = a) ∧
      (∀ K, IsIso (tensorTranspose F U P projection_isIso G adj K)) ∧
      (∀ K, IsIso (tensorTranspose F' U' P' nativeProjection_isIso G' adj' K)) ∧
      (∀ K,
        V.map (tensorTranspose F U P projection_isIso G adj K) ≫ a.hom.app K =
          (Functor.Monoidal.μIso V (G.obj (𝟙_ D)) (U.obj K)).inv ≫
            ((a.hom.app (𝟙_ D) ≫ G'.map (Functor.Monoidal.εIso W).inv) ⊗ₘ
              pull.hom.app K) ≫
            tensorTranspose F' U' P' nativeProjection_isIso G' adj' (W.obj K))

end Categorical

attribute [instance_reducible] DomainComparison.monoidal

attribute [instance] DomainComparison.etaleMonoidal DomainComparison.nativeMonoidal
  DomainComparison.monoidal DomainComparison.equivalence

/-- The actual finite-Tor realization with the membership witness supplied by the
comparison datum. Source: restriction of V
(blueprint: lem-pur-finite-native-tensor-comparison). -/
abbrev V (ordinary : Bool) (E : ∀ T : Scheme.{u}, Encoding A T) (T : Scheme.{u})
    [h : DomainComparison A ordinary E T] :=
  restrictRealization A ordinary E T h.mem

section Restriction
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- Membership witnesses for restricting the already supplied geometric functors.
Source: the finite-Tor domains of f_! and f^* in the node
(blueprint: lem-pur-finite-native-tensor-comparison). -/
structure OperationRestriction (P : ObjectProperty C) (Q : ObjectProperty D)
    (F : C ⥤ D) (U : D ⥤ C) where
  lower_mem : ∀ M : P.FullSubcategory, Q (F.obj M.obj)
  upper_mem : ∀ K : Q.FullSubcategory, P (U.obj K.obj)

/-- Restrict compact support without changing objects or maps.
Source: restriction along the full finite-Tor inclusions
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def OperationRestriction.lower {P : ObjectProperty C} {Q : ObjectProperty D}
    {F : C ⥤ D} {U : D ⥤ C} (r : OperationRestriction P Q F U) :
    P.FullSubcategory ⥤ Q.FullSubcategory :=
  ObjectProperty.lift Q (P.ι ⋙ F) r.lower_mem

/-- Restrict pullback without changing objects or maps.
Source: restriction along the full finite-Tor inclusions
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def OperationRestriction.upper {P : ObjectProperty C} {Q : ObjectProperty D}
    {F : C ⥤ D} {U : D ⥤ C} (r : OperationRestriction P Q F U) :
    Q.FullSubcategory ⥤ P.FullSubcategory :=
  ObjectProperty.lift P (Q.ι ⋙ U) r.upper_mem

variable [MonoidalCategory C] [MonoidalCategory D]

/-- Restrict the actual ambient projection morphism to the full monoidal domains.
Source: P on the finite-Tor constructible inputs
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def OperationRestriction.projection {P : ObjectProperty C} {Q : ObjectProperty D}
    [P.IsMonoidal] [Q.IsMonoidal] {F : C ⥤ D} {U : D ⥤ C}
    (r : OperationRestriction P Q F U)
    (π : ∀ M : C, ∀ K : D, F.obj M ⊗ K ⟶ F.obj (M ⊗ U.obj K))
    (M : P.FullSubcategory) (K : Q.FullSubcategory) :
    r.lower.obj M ⊗ K ⟶ r.lower.obj (M ⊗ r.upper.obj K) :=
  ObjectProperty.homMk (π M.obj K.obj)
end Restriction

/-- The existing ordinary-etale compactification functor, used to shorten the diagrams.
Source: Rp_* j_! for the chosen compactification
(blueprint: lem-pur-finite-native-tensor-comparison). -/
abbrev etaleF {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) c

/-- The existing ordinary-etale total inverse image.
Source: the ordinary-etale pullback in the node
(blueprint: lem-pur-finite-native-tensor-comparison). -/
abbrev etaleU {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).leftDerivedFunctor

/-- The existing ordinary-etale proper/open projection.
Source: P in the ordinary-etale category
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def etaleP {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : Etale.DerivedCategoryModule (ULift.{u + 1} A) X)
    (K : Etale.DerivedCategoryModule (ULift.{u + 1} A) Y) :
    (etaleF A c).obj M ⊗ K ⟶ (etaleF A c).obj (M ⊗ (etaleU A f).obj K) :=
  ((Etale.projectionMapOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).app M).app K

/-- One arrow's canonical comparisons and its two asserted tensor squares.
The normalization fields name the already constructed B and pullback maps componentwise.
The generic transport field quantifies over both choices of the exceptional adjunction;
therefore it includes the restriction of the given Brown right adjoint with its counit.
Source: the middle assertions of the node
(blueprint: lem-pur-finite-native-tensor-comparison). -/
class ArrowComparison (ordinary : Bool) (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f)
    [DomainComparison A ordinary E X] [DomainComparison A ordinary E Y] where
  etaleRestriction : OperationRestriction (etaleDomain A X) (etaleDomain A Y)
    (etaleF A c) (etaleU A f)
  nativeRestriction : OperationRestriction (nativeDomain A ordinary X) (nativeDomain A ordinary Y)
    (nativeCompact A ordinary c) (nativeUpper A ordinary f)
  etaleAdjoint : etaleRestriction.lower.IsLeftAdjoint
  nativeAdjoint : nativeRestriction.lower.IsLeftAdjoint
  B : etaleRestriction.lower ⋙ V A ordinary E Y ≅
    V A ordinary E X ⋙ nativeRestriction.lower
  B_normalization : ∀ M,
    (nativeDomain A ordinary Y).ι.mapIso (B.app M) =
      nativeB A ordinary E c (etalePlus A X M)
  pull : etaleRestriction.upper ⋙ V A ordinary E X ≅
    V A ordinary E Y ⋙ nativeRestriction.upper
  pull_normalization : ∀ K,
    (nativeDomain A ordinary X).ι.mapIso (pull.app K) =
      (nativePullComparison A ordinary E f).app K.obj
  transport : TensorAdjunctionTransport
    etaleRestriction.lower nativeRestriction.lower etaleRestriction.upper nativeRestriction.upper
    (V A ordinary E X) (V A ordinary E Y) B pull
    (etaleRestriction.projection (etaleP A c))
    (nativeRestriction.projection (nativeP A ordinary c))


/-- The ordinary-etale proper/open compositor at the specified input and compactifications.
Source: the canonical compact-support coherence construction
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def etaleCompositorAt {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g) (ch : Compactification (f ≫ g))
    (M : (etaleDomain A X).FullSubcategory) :
    (etaleF A cg).obj ((etaleF A cf).obj M.obj) ≅ (etaleF A ch).obj M.obj :=
by
  let Λ := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let L := etalePlus A X M
  let a := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility Λ cf).app L
  let b := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility Λ cg).app
    ((Etale.rightDerivedLowerShriekOfCompactificationPlus Λ cf).obj L)
  exact ((etaleF A cg).mapIso a).symm ≪≫ b.symm ≪≫
    DerivedCategory.Plus.ι.mapIso
      ((coherenceEtaleCompositor (ULift.{u + 1} A) cf cg ch).app L) ≪≫
    (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility Λ ch).app L

/-- The ordinary pro-etale compositor is the computed proper/open tower paste, including
common-refinement changes, on the retained etale witness.
Source: finiteCompactSiteCompositionPlus, not transport of an arbitrary isomorphism
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def ordinaryCompositorAt {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g] [IsNoetherian Y] [IsNoetherian Z]
    (cf : Compactification f) (cg : Compactification g) (ch : Compactification (f ≫ g))
    (T : Compactification.Triangle f g) (M : (etaleDomain A X).FullSubcategory) :
    (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) cg).obj
      ((rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) cf).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).mapDerivedCategory.obj
          M.obj)) ⟶
    (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) ch).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).mapDerivedCategory.obj
        M.obj) :=
by
  let Λ := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let L := etalePlus A X M
  let N := (comparisonUpperStar Λ X).mapDerivedCategoryPlus.obj L
  let w := (comparisonUpperStar Λ X).mapDerivedCategoryPlusCompatibility.app L
  let Pf := rightDerivedLowerShriekOfCompactification Λ cf
  let Pg := rightDerivedLowerShriekOfCompactification Λ cg
  let Ph := rightDerivedLowerShriekOfCompactification Λ ch
  let a := (rightDerivedLowerShriekOfCompactificationPlusCompatibility Λ cf).app N
  let b := (rightDerivedLowerShriekOfCompactificationPlusCompatibility Λ cg).app
    ((rightDerivedLowerShriekOfCompactificationPlus Λ cf).obj N)
  let d := (rightDerivedLowerShriekOfCompactificationPlusCompatibility Λ ch).app N
  exact (Pg.mapIso (Pf.mapIso w)).inv ≫ (Pg.mapIso a).inv ≫ b.inv ≫
    DerivedCategory.Plus.ι.map
      (finiteCompactSiteCompositionPlus (ULift.{u + 1} A) cf cg ch T L) ≫
    d.hom ≫ (Ph.mapIso w).hom

/-- Compute the same native proper/open paste through the identity-on-sections encoding.
Full faithfulness takes the unique preimage of the actual ordinary tower map. All six
boundary factors are the constructed compactification encodings and their counit; no
compact-support comparison with the etale site is used to define this compositor.
Source: sectionwise proper/open operations transport and finite compact-support coherence
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def internalCompositorAt (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g] [IsNoetherian Y] [IsNoetherian Z]
    (cf : Compactification f) (cg : Compactification g) (ch : Compactification (f ≫ g))
    (T : Compactification.Triangle f g) (M : (etaleDomain A X).FullSubcategory) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient A) cg).obj
      ((CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient A) cf).obj
        ((internalEtaleRealization A X (E X)).obj M.obj)) ⟶
    (CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient A) ch).obj
      ((internalEtaleRealization A X (E X)).obj M.obj) := by
  let N := (internalEtaleRealization A X (E X)).obj M.obj
  let Pf := rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) cf
  let Pg := rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) cg
  let Ph := rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) ch
  let w := (E X).fixedDerived.counitIso.app
    ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).mapDerivedCategory.obj M.obj)
  exact (E Z).fixedDerived.functor.preimage
    ((compactEncoding A E cg).hom.app _ ≫
      Pg.map ((compactEncoding A E cf).hom.app N) ≫
      Pg.map (Pf.map w.hom) ≫ ordinaryCompositorAt A cf cg ch T M ≫
      Ph.map w.inv ≫ (compactEncoding A E ch).inv.app N)

/-- The specified native proper/open compositor in either presentation, evaluated on an
etale-origin object. Its source maps are the computed proper/open maps, independently
of the B-compositor equation asserted below.
Source: the compositor clause of the node
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def nativeCompositorAt (ordinary : Bool) (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g] [IsNoetherian Y] [IsNoetherian Z]
    (cf : Compactification f) (cg : Compactification g) (ch : Compactification (f ≫ g))
    (T : Compactification.Triangle f g) (M : (etaleDomain A X).FullSubcategory) :
    (nativeCompact A ordinary cg).obj
        ((nativeCompact A ordinary cf).obj ((realization A ordinary E X).obj M.obj)) ⟶
      (nativeCompact A ordinary ch).obj ((realization A ordinary E X).obj M.obj) := by
  cases ordinary
  · exact internalCompositorAt A E cf cg ch T M
  · exact ordinaryCompositorAt A cf cg ch T M

section CompositorMate
variable {C : Type u₁} {D : Type u₂} {H : Type u₃}
  {C' : Type u₄} {D' : Type u₅} {H' : Type u₆}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} H]
  [Category.{v₄} C'] [Category.{v₅} D'] [Category.{v₆} H']

/-- Counit compatibility fixes the right-adjoint comparison uniquely.
Source: the displayed counit equation in the node
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def CounitCompatible {F : C ⥤ D} {F' : C' ⥤ D'} {G : D ⥤ C} {G' : D' ⥤ C'}
    {V : C ⥤ C'} {W : D ⥤ D'} (B : F ⋙ W ≅ V ⋙ F')
    (adj : F ⊣ G) (adj' : F' ⊣ G') (a : G ⋙ V ≅ W ⋙ G') : Prop :=
  ∀ K, B.hom.app (G.obj K) ≫ F'.map (a.hom.app K) ≫ adj'.counit.app (W.obj K) =
    W.map (adj.counit.app K)

/-- Transport of the actual right-adjoint compositors, characterized by the composite
counits. This formula includes all functor associators componentwise.
Source: current blueprint, transpose under the composite adjunction
(blueprint: lem-pur-finite-native-tensor-comparison). -/
def AdjointCompositionCompatible
    {F : C ⥤ D} {J : D ⥤ H} {L : C ⥤ H}
    {F' : C' ⥤ D'} {J' : D' ⥤ H'} {L' : C' ⥤ H'}
    {V : C ⥤ C'} {W : D ⥤ D'} {Z : H ⥤ H'}
    (Bf : F ⋙ W ≅ V ⋙ F') (Bg : J ⋙ Z ≅ W ⋙ J') (Bh : L ⋙ Z ≅ V ⋙ L')
    (e : F ⋙ J ≅ L) (n : F' ⋙ J' ≅ L') : Prop :=
  ∀ (G : D ⥤ C) (I : H ⥤ D) (N : H ⥤ C)
    (G' : D' ⥤ C') (I' : H' ⥤ D') (N' : H' ⥤ C')
    (af : F ⊣ G) (ag : J ⊣ I) (ah : L ⊣ N)
    (af' : F' ⊣ G') (ag' : J' ⊣ I') (ah' : L' ⊣ N')
    (a : G ⋙ V ≅ W ⋙ G') (b : I ⋙ W ≅ Z ⋙ I') (c : N ⋙ V ≅ Z ⋙ N'),
    CounitCompatible Bf af af' a → CounitCompatible Bg ag ag' b →
    CounitCompatible Bh ah ah' c →
    ∀ K,
      c.hom.app K ≫
          ((ah'.ofNatIsoLeft n.symm).rightAdjointUniq (af'.comp ag')).hom.app (Z.obj K) =
        V.map (((ah.ofNatIsoLeft e.symm).rightAdjointUniq (af.comp ag)).hom.app K) ≫
          a.hom.app (I.obj K) ≫ G'.map (b.hom.app K)
end CompositorMate

end AlgebraicGeometry.ProEtale.FiniteNativeTensor
