/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactSupportCondensedRealization
public import WeilConjectures.AlgebraicGeometry.CondensedTateRealization
public import WeilConjectures.AlgebraicGeometry.ExceptionalRealizationNormalization
public import WeilConjectures.AlgebraicGeometry.CompactSupportRealizationFactorNormalization
public import WeilConjectures.SixFunctors.IntegralOpenReductionComparison
public import WeilConjectures.AlgebraicGeometry.BoundedConstructiblePushforwardRestriction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-! # Condensed realization of the specified open counit

Source: current blueprint, sec-smooth-purity, sk-thm-purity-transport, proof Steps 2--3;
agent-formulated normalization of the ordinary completed open adjunction
(blueprint: def-pur-condensed-open-counit-comparisons).

## Main definitions

- `integralAdjunction`, `restrictedAdjunction`: the ordinary completed open adjunction.
- `restrictionComparison`: scalar extension and open restriction on K-flat representatives.
- `integralIdentification`, `extensionComparison`: the prescribed integral and condensed maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open WeilConjectures
open CondensedERealization CompactSupportCondensedRealization
namespace WeilConjectures.CondensedOpenCounitRealization

variable (l : ℕ) [Fact l.Prime] (k : Type u) [_root_.Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

open CondensedExceptionalReconstruction

/-- The ambient ordinary completed open extension in the recorded completion coordinates.
Source: blueprint purity transport, Steps 2--3
(blueprint: def-pur-condensed-open-counit-comparisons). -/
abbrev integralExtension {U Y : Base k} (j : U.scheme ⟶ Y.scheme) [IsOpenImmersion j] :=
  (purCoefficientModel l (Field.{u} l) U.scheme).functor ⋙
    IntegralSystemRealization.ringedOpen l (Field.{u} l) j ⋙
      (purCoefficientModel l (Field.{u} l) Y.scheme).inverse

/-- Ordinary restriction, without deriving completion anew.
Source: blueprint purity transport, Steps 2--3
(blueprint: def-pur-condensed-open-counit-comparisons). -/
abbrev integralRestriction {U Y : Base k} (j : U.scheme ⟶ Y.scheme) :=
  (purCoefficientModel l (Field.{u} l) Y.scheme).functor ⋙
    IntegralSystemRealization.ringedPull l (Field.{u} l) j ⋙
      (purCoefficientModel l (Field.{u} l) U.scheme).inverse

/-- Transport of the actual completed-ring open adjunction along coefficient coordinates.
Source: blueprint purity transport, Steps 2--3
(blueprint: def-pur-condensed-open-counit-comparisons). -/
def integralAdjunction {U Y : Base k} (j : U.scheme ⟶ Y.scheme) [IsOpenImmersion j] :
    integralExtension l k j ⊣ integralRestriction l k j :=
  ((purCoefficientModel l (Field.{u} l) U.scheme).toAdjunction.comp
    (IntegralSystemRealization.ringedOpenAdj l (Field.{u} l) j)).comp
      (purCoefficientModel l (Field.{u} l) Y.scheme).symm.toAdjunction

/-- The ambient scalar realization, in the existing completed-ring coordinates.
Source: blueprint purity transport, Steps 2--3
(blueprint: def-pur-condensed-open-counit-comparisons). -/
abbrev scalarRealization (A : CoefficientData l (Field.{u} l) k) (T : Base k) :=
  CompactSupportFactorNormalization.realize l (Field.{u} l) T.scheme
      (A.realization.atObject T) ⋙
    omegaScalar l (Field.{u} l) (embedding l) T.scheme

/-- The fixed scalar-extension comparison with the recorded constructible V.
Source: blueprint purity transport, Steps 2--3
(blueprint: def-pur-condensed-open-counit-comparisons). -/
def scalarLattice (A : CoefficientData l (Field.{u} l) k) (T : Base k)
    (K : Integral l (Field.{u} l) T.scheme) :
    (scalarRealization l k A T).obj
        ((purCoefficientModel l (Field.{u} l) T.scheme).functor.obj K.obj) ≅
      ((realization l k A.realization T).obj K).obj :=
  (omegaScalar l (Field.{u} l) (embedding l) T.scheme).mapIso
    ((CompactSupportFactorNormalization.latticeComparison l (Field.{u} l) T.scheme
      (A.realization.atObject T)).app K)

/-- The restriction/scalar comparison on flat-term K-flat representatives.
Both factors are the published adjoint-conjugate balancing comparisons.
Source: blueprint purity transport, Steps 2--3
(blueprint: def-pur-condensed-open-counit-comparisons). -/
def scalarRestriction (A : CoefficientData l (Field.{u} l) k)
    (U Y : Base k) (j : U.scheme ⟶ Y.scheme) :
    IntegralSystemRealization.ringedPull l (Field.{u} l) j ⋙ scalarRealization l k A U ≅
      scalarRealization l k A Y ⋙
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) j).leftDerivedFunctor :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (CompactSupportFactorNormalization.realizationPull l (Field.{u} l) j
        (A.realization.atObject U) (A.realization.atObject Y)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (CondensedRing.derivedPullIso (omegaMap l (Field.{u} l) (embedding l)) j)

/-- The trivial compactification, including identity and empty-open cases.
Source: blueprint purity transport, Steps 2--3
(blueprint: def-pur-condensed-open-counit-comparisons). -/
def trivialCompactification {U Y : Base k} (j : U.scheme ⟶ Y.scheme)
    [IsOpenImmersion j] : Compactification j where
  Z := Y.scheme
  i := j
  g := 𝟙 Y.scheme
  comm := Category.comp_id j
  isProper := inferInstance
  isOpenImmersion := inferInstance


/-- Preservation by the two ordinary completed open operations.
Source: blueprint purity transport, Step 2
(blueprint: def-pur-condensed-open-counit-comparisons). -/
structure Preserves (U Y : Base k) (j : U.scheme ⟶ Y.scheme) [IsOpenImmersion j] : Prop where
  extension : ∀ K : Integral l (Field.{u} l) U.scheme,
    PbcIsBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l (Field.{u} l))
      ((integralExtension l k j).obj K.obj)
  restriction : ∀ K : Integral l (Field.{u} l) Y.scheme,
    PbcIsBoundedConstructibleComplete U.scheme (pbcIntegralDatum l (Field.{u} l))
      ((integralRestriction l k j).obj K.obj)

/-- Restrict the same ambient extension, retaining all its morphisms.
Source: blueprint purity transport, Step 2
(blueprint: def-pur-condensed-open-counit-comparisons). -/
def extension {U Y : Base k} {j : U.scheme ⟶ Y.scheme} [IsOpenImmersion j]
    (h : Preserves l k U Y j) :
    Integral l (Field.{u} l) U.scheme ⥤ Integral l (Field.{u} l) Y.scheme :=
  ObjectProperty.lift _
    (ObjectProperty.ι
      (PbcIsBoundedConstructibleComplete U.scheme (pbcIntegralDatum l (Field.{u} l))) ⋙
      integralExtension l k j) h.extension

/-- Restrict the same ambient inverse image, retaining all its morphisms.
Source: blueprint purity transport, Step 2
(blueprint: def-pur-condensed-open-counit-comparisons). -/
def restriction {U Y : Base k} {j : U.scheme ⟶ Y.scheme} [IsOpenImmersion j]
    (h : Preserves l k U Y j) :
    Integral l (Field.{u} l) Y.scheme ⥤ Integral l (Field.{u} l) U.scheme :=
  ObjectProperty.lift _
    (ObjectProperty.ι
      (PbcIsBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l (Field.{u} l))) ⋙
      integralRestriction l k j) h.restriction

/-- Restriction of the actual ambient adjunction by its fully faithful inclusions.
Source: blueprint purity transport, Step 2
(blueprint: def-pur-condensed-open-counit-comparisons). -/
def restrictedAdjunction {U Y : Base k} {j : U.scheme ⟶ Y.scheme} [IsOpenImmersion j]
    (h : Preserves l k U Y j) : extension l k h ⊣ restriction l k h :=
  (integralAdjunction l k j).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.liftCompιIso _ _ h.extension).symm
    (ObjectProperty.liftCompιIso _ _ h.restriction).symm

/-- The specified s, conjugating the representative-normalized scalar comparison by
only the recorded coefficient-encoding counit and lattice comparisons.
Source: blueprint purity transport, Steps 2--3
(blueprint: def-pur-condensed-open-counit-comparisons). -/
def restrictionComparison (A : CoefficientData l (Field.{u} l) k)
    (U Y : Base k) (j : U.scheme ⟶ Y.scheme) [IsOpenImmersion j]
    (h : Preserves l k U Y j) (K : Integral l (Field.{u} l) Y.scheme) :
    ((realization l k A.realization U).obj ((restriction l k h).obj K)).obj ≅
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) j).leftDerivedFunctor.obj
        ((realization l k A.realization Y).obj K).obj :=
  (scalarLattice l k A U ((restriction l k h).obj K)).symm ≪≫
    (scalarRealization l k A U).mapIso
      ((purCoefficientModel l (Field.{u} l) U.scheme).counitIso.app _) ≪≫
    (scalarRestriction l k A U Y j).app _ ≪≫
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) j).leftDerivedFunctor.mapIso
      (scalarLattice l k A Y K)

/-- Canonical removal of the derived identity direct-image factor.
Source: blueprint purity transport, trivial compactification
(blueprint: def-pur-condensed-open-counit-comparisons). -/
def removeIdentity (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u}) :
    (CondensedRing.lowerStar Λ (𝟙 Y)).rightDerivedFunctor ≅ 𝟭 _ :=
  Functor.rightDerivedFunctorNatIso (CondensedRing.lowerStarId Λ Y) ≪≫
    (𝟭 _).rightDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _

/-- The integral identity direct-image unitor, fixed on sections.
Source: blueprint purity transport, trivial compactification
(blueprint: def-pur-condensed-open-counit-comparisons). -/
def removeIntegralIdentity (Y : Scheme.{u}) :
    IntegralSystemRealization.ringedPush l (Field.{u} l) (𝟙 Y) ≅ 𝟭 _ :=
  Functor.rightDerivedFunctorNatIso
      (CompactSupportFactorNormalization.ordinaryPushIdentity_existsUnique
        l (Field.{u} l) Y).exists.choose ≪≫
    (𝟭 _).rightDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _


end WeilConjectures.CondensedOpenCounitRealization
