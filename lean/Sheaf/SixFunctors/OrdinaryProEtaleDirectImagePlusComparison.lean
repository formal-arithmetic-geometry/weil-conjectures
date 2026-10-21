/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import Sheaf.AlgebraicGeometry.ComparisonDirectImage
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.CategoryTheory.ModuleInverseImageUnitComparison
import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparisonData
import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparisonDerivedFunctor

/-! # Ordinary intrinsic direct image and its bounded-below comparison

Source: Bhatt--Scholze, Lemma 5.4.3 and Remark 5.4.4; Stacks Tags 070K, 070J and 099R
(blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison).

All categories below are intrinsic constant-ring module categories. The original sites
have object universe u+1 and morphism universe u; modules live in u+1. Thus these sites
are small relative to their module universe, without identifying the two site universes.
The existing AsSmall comparison data is the equivalent small-model presentation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a b c d
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace AlgebraicGeometry
open Scheme

/-- Intrinsic etale modules, using the recorded constant-ring realization.
Source: Stacks 03CV (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
abbrev Etale.intrinsicConstantModules (X : Scheme.{u}) (B : Type u) [CommRing B] :=
  SheafOfModules.{u + 1} (Scheme.etaleConstantModuleRing X (ULift.{u + 1, u} B))

/-- Use the recorded continuity of etale base change at the named small topology.
Source: Stacks 03D6 (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
instance Etale.intrinsicBaseChange_continuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous
      Y.smallEtaleTopology X.smallEtaleTopology :=
  Etale.isContinuous_overPullback f

/-- The actual etale scalar map: extend the identical constant sections by sheafification.
Source: Stacks 03D6 (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
def Etale.intrinsicConstantRingMap {X Y : Scheme.{u}} (f : X ⟶ Y) (B : Type u) [CommRing B] :
    Scheme.etaleConstantModuleRing Y (ULift.{u + 1, u} B) ⟶
      ((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
        RingCat.{u + 1} Y.smallEtaleTopology X.smallEtaleTopology).obj
          (Scheme.etaleConstantModuleRing X (ULift.{u + 1, u} B)) :=
  ((sheafificationAdjunction Y.smallEtaleTopology RingCat.{u + 1}).homEquiv _ _).symm
    (Functor.whiskerLeft (MorphismProperty.Over.pullback @Etale ⊤ f).op
      (toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} B)))))

/-- Intrinsic etale direct image, sectionwise base change and the specified scalar action.
Source: Stacks 03D6 (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
abbrev Etale.intrinsicModuleDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y) (B : Type u) [CommRing B] :
    Etale.intrinsicConstantModules X B ⥤ Etale.intrinsicConstantModules Y B :=
  @SheafOfModules.pushforward.{u + 1} Y.Etale _ X.Etale _
    Y.smallEtaleTopology X.smallEtaleTopology (MorphismProperty.Over.pullback @Etale ⊤ f)
    (Scheme.etaleConstantModuleRing Y (ULift.{u + 1, u} B))
    (Scheme.etaleConstantModuleRing X (ULift.{u + 1, u} B))
    (Etale.intrinsicBaseChange_continuous f) (Etale.intrinsicConstantRingMap f B)

/-- Additivity is the existing sectionwise pushforward construction.
Source: Stacks 03D6 (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
instance Etale.intrinsicModuleDirectImage_additive {X Y : Scheme.{u}} (f : X ⟶ Y)
    (B : Type u) [CommRing B] : (Etale.intrinsicModuleDirectImage f B).Additive where
  map_add := rfl

/-- Use the standard localization of the intrinsic etale module category.
Source: Stacks 05RU (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
instance Etale.intrinsicConstantModules_hasDerivedCategory (X : Scheme.{u})
    (B : Type u) [CommRing B] :
    HasDerivedCategory (Etale.intrinsicConstantModules X B) := HasDerivedCategory.standard _

/-- Enough injectives follows from the published Grothendieck module-sheaf construction.
Source: Stacks 079P (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
instance Etale.intrinsicConstantModules_grothendieck (X : Scheme.{u}) (B : Type u) [CommRing B] :
    IsGrothendieckAbelian.{u + 1} (Etale.intrinsicConstantModules X B) :=
  SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, u + 1}
    X.smallEtaleTopology (Scheme.etaleConstantModuleRing X (ULift.{u + 1, u} B))

/-- The usual bounded-below derived direct image of intrinsic modules; its unit is
intrinsicModuleDirectImage.rightDerivedFunctorPlusUnit. This is the same localization
and injective-resolution construction as in the recorded abelian presentation.
Source: Stacks 071J, 05TI (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
abbrev Etale.intrinsicRightDerivedModuleDirectImagePlus {X Y : Scheme.{u}}
    (f : X ⟶ Y) (B : Type u) [CommRing B] :=
  (Etale.intrinsicModuleDirectImage f B).rightDerivedFunctorPlus

end AlgebraicGeometry

namespace AlgebraicGeometry.SfbOrdinaryComparison
open Scheme

/-- Intrinsic pro-etale modules, with the published commutative constant ring sheaf.
Source: Stacks 03CV (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
abbrev ProEtale.intrinsicConstantModules (X : Scheme.{u}) (B : Type u) [CommRing B] :=
  Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X B)

/-- Enough injectives on the original pro-etale site, in its module universe.
Source: Stacks 079P (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
instance proEtale.intrinsicConstantModules_grothendieck (X : Scheme.{u}) (B : Type u) [CommRing B] :
    IsGrothendieckAbelian.{u + 1} (ProEtale.intrinsicConstantModules X B) :=
  SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, u + 1}
    (ProEt.topology X) ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X B))

/-- The intrinsic constant-section ring map for nu, on the original sites. It is the
original-site version of constructibleComparisonRingMap on the equivalent AsSmall sites.
Source: Stacks 099R, 03D2
(blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
def comparisonRingMap (X : Scheme.{u}) (B : Type u) [CommRing B] :
    Scheme.etaleConstantModuleRing X (ULift.{u + 1, u} B) ⟶
      ((toProEt X).sheafPushforwardContinuous RingCat.{u + 1}
        X.smallEtaleTopology (Scheme.ProEt.topology X)).obj
          ((sheafCompose (Scheme.ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (Scheme.proEtaleConstantRing X B)) :=
  ((sheafificationAdjunction X.smallEtaleTopology RingCat.{u + 1}).homEquiv _ _).symm
    (Functor.whiskerLeft (toProEt X).op (ProEtale.finiteCoefficientIntrinsicScalarMap X B))

/-- The sectionwise intrinsic module direct image nu_*.
Source: Stacks 03D6 (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
abbrev comparisonPushforward (X : Scheme.{u}) (B : Type u) [CommRing B] :=
  SheafOfModules.pushforward.{u + 1} (F := toProEt X)
    (J := X.smallEtaleTopology) (K := ProEt.topology X) (comparisonRingMap X B)

/-- The canonical comparison module pushforward admits its intrinsic left adjoint.
Source: Stacks 03D2--03D3
(blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison).

Proof: transport both sites by their AsSmall equivalences to object and morphism
universe u+1, without changing any ring or module sections. On the models the module
presheaf pushforward has the tensor/Kan-extension left adjoint; follow it by module
sheafification. The sheafification adjunction restricts its hom equivalence to module
sheaves. Transport that adjunction back through the two module-site equivalences.
Its right adjoint is the displayed sectionwise pushforward, by the actual ring map
comparisonRingMap. Thus its left adjoint is determined up to the unique adjunction
isomorphism. This is the original-site transport of lem-pe-coefficient-comparison-data. -/
@[instance]
theorem comparisonPushforward_isRightAdjoint (X : Scheme.{u}) (B : Type u) [CommRing B] :
    (comparisonPushforward X B).IsRightAdjoint := by
  sorry

/-- The intrinsic module inverse image nu^*, with its specified constant-section map.
Source: Stacks 03D2 (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
abbrev comparisonPullback (X : Scheme.{u}) (B : Type u) [CommRing B] :=
  SheafOfModules.pullback.{u + 1} (F := toProEt X)
    (J := X.smallEtaleTopology) (K := ProEt.topology X) (comparisonRingMap X B)

/-- Exactness of the intrinsic comparison inverse image.
Source: Stacks 00YV, 03D2 and 09AL
(blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison).

Proof: step 6 identifies the inverse-image constant ring using constant sections and
lem-pe-constant-left-module-inverse-image. The module inverse-image unit comparison
identifies the underlying abelian functor and unit. Exactness of geometric inverse
image therefore gives finite-limit preservation; the module adjunction gives finite
colimits and additivity. This is lem-pe-coefficient-comparison-derived-functor on the
original sites, transported through their AsSmall equivalences. -/
theorem comparisonPullback_exact (X : Scheme.{u}) (B : Type u) [CommRing B] :
    (comparisonPullback X B).Additive ∧
      PreservesFiniteLimits (comparisonPullback X B) ∧
      PreservesFiniteColimits (comparisonPullback X B) := by
  sorry

/-- Published exactness, for termwise localization.
Source: Stacks 09AL (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
instance comparisonPullback_additive (X : Scheme.{u}) (B : Type u) [CommRing B] :
    (comparisonPullback X B).Additive := (comparisonPullback_exact X B).1

/-- Published left exactness of the canonical inverse image.
Source: Stacks 00YV (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
instance comparisonPullback_limits (X : Scheme.{u}) (B : Type u) [CommRing B] :
    PreservesFiniteLimits (comparisonPullback X B) := (comparisonPullback_exact X B).2.1

/-- Published right exactness of the canonical inverse image.
Source: Stacks 03D3 (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
instance comparisonPullback_colimits (X : Scheme.{u}) (B : Type u) [CommRing B] :
    PreservesFiniteColimits (comparisonPullback X B) := (comparisonPullback_exact X B).2.2

/-- The existing etale realization, without a copied category or scalar action.
Source: Stacks 00YV (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
abbrev etaleRealization (X : Scheme.{u}) (B : Type u) [CommRing B] :=
  Scheme.etaleConstantModuleFunctor X (ULift.{u + 1, u} B)

/-- The existing equivalence theorem supplies the coefficient realization structure.
Source: Stacks 00YV (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
instance etaleRealization_equivalence (X : Scheme.{u}) (B : Type u) [CommRing B] :
    (etaleRealization X B).IsEquivalence :=
  Scheme.etaleConstantModuleFunctor_isEquivalence X (ULift.{u + 1, u} B)

/-- Additivity follows from preservation of binary products by the equivalence.
Source: Stacks 00YV (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
instance etaleRealization_additive (X : Scheme.{u}) (B : Type u) [CommRing B] :
    (etaleRealization X B).Additive := Functor.additive_of_preserves_binary_products _

/-- The inverse of the existing etale coefficient equivalence, with its actual unit.
Source: Stacks 00YV (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
def etaleEquivalence (X : Scheme.{u}) (B : Type u) [CommRing B] :=
  (etaleRealization X B).asEquivalence

/-- Constant-section inverse image in the fixed-scalar presentation, transported through
both published coefficient equivalences.
Source: Stacks 00YV (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
def transportedComparison (X : Scheme.{u}) (B : Type u) [CommRing B] [Finite B] :=
  (etaleEquivalence X B).inverse ⋙
    ProEtale.finiteCoefficientIntrinsicComparison X B

/-- The canonical module-sheafification unit of pro-etale coefficient realization.
Source: Stacks 03CV (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
def proEtaleRealizationUnit (X : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :=
  (PresheafOfModules.sheafificationAdjunction.{u + 1}
    (ProEtale.finiteCoefficientIntrinsicScalarMap X B)).unit.app
      ((ProEtale.finiteCoefficientModulePresheaf X.ProEt (ULift.{u + 1, u} B)).obj M.obj)

/-- All parts of a total-derived/bounded-below identification, including its units.
This is a bundle of the clauses of this node, rather than a new derived category.
Source: Stacks 070K, 070J and 05TI
(blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
structure RightDerivedNormalization {C : Type a} {D : Type b}
    [Category.{c} C] [Category.{d} D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] where
  resolutions : ∀ K : CochainComplex C ℤ,
    ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s
  plusIso : DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctorOfQuasiIsoResolutions resolutions ≅
    F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι
  unit_eq : ∀ K : HomotopyCategory.Plus C,
    (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit resolutions).app K.obj ≫
      plusIso.hom.app (DerivedCategory.Plus.Qh.obj K) =
        DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app K)
  plus_computes : ∀ (K : HomotopyCategory.Plus C),
    (∀ n : ℤ, Injective (K.obj.as.X n)) → IsIso (F.rightDerivedFunctorPlusUnit.app K)

/-- Use exactly the recorded ordinary right derived functor, on arbitrary K-injective
resolutions. Its published unit, universal property and computation are unchanged.
Source: Stacks 070K (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
abbrev RightDerivedNormalization.full {C : Type a} {D : Type b}
    [Category.{c} C] [Category.{d} D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    {F : C ⥤ D} [F.Additive] (r : RightDerivedNormalization F) :=
  F.rightDerivedFunctorOfQuasiIsoResolutions r.resolutions

/-- The canonical value on every quasi-isomorphism to a K-injective, without a mono
hypothesis: use the recorded resolution comparison, RF(Qs) followed by the inverse unit.
Source: Stacks 070K (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
abbrev RightDerivedNormalization.resolutionIso {C : Type a} {D : Type b}
    [Category.{c} C] [Category.{d} D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    {F : C ⥤ D} [F.Additive] (r : RightDerivedNormalization F)
    {M I : CochainComplex C ℤ} (s : M ⟶ I) [QuasiIso s] [I.IsKInjective] :
    r.full.obj (DerivedCategory.Q.obj M) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I) :=
  F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso r.resolutions s

/-- Unit-preserving identification of the two inverse-image presentations, as left
adjoints to exactly the same sectionwise intrinsic module direct image. The unit on
sections is the fixed comparison unit followed by coefficient realization, fixing
the adjunction as well as the isomorphism.
Source: Stacks 03D2--03D3
(blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
structure ComparisonIdentification (X : Scheme.{u}) (B : Type u)
    [CommRing B] [Finite B] where
  adjunction : transportedComparison X B ⊣ comparisonPushforward X B
  unit_sections : ∀ (M : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) (V : X.Etaleᵒᵖ) (x : M.obj.obj V),
    (adjunction.unit.app ((etaleRealization X B).obj M)).val.app V x =
      (proEtaleRealizationUnit X B
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X).obj
          ((etaleEquivalence X B).inverse.obj ((etaleRealization X B).obj M)))).app
        ((toProEt X).op.obj V)
        (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X).map
          ((etaleEquivalence X B).unitIso.hom.app M)).hom.app ((toProEt X).op.obj V)
          (((ProEtale.comparisonAdjunction
            (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X).unit.app M).hom.app V x))
  iso : comparisonPullback X B ≅ transportedComparison X B
  unit_eq : ∀ M : Etale.intrinsicConstantModules X B,
    (SheafOfModules.pullbackPushforwardAdjunction (comparisonRingMap X B)).unit.app M ≫
      (comparisonPushforward X B).map (iso.hom.app M) = adjunction.unit.app M
  unique : ∀ e : comparisonPullback X B ≅ transportedComparison X B,
    (∀ M : Etale.intrinsicConstantModules X B,
      (SheafOfModules.pullbackPushforwardAdjunction (comparisonRingMap X B)).unit.app M ≫
        (comparisonPushforward X B).map (e.hom.app M) = adjunction.unit.app M) → e = iso

/-- Cancel the existing etale realization equivalence in the inverse-image identification.
Source: Stacks 00YV (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
def realizedComparisonIso (X : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (i : ComparisonIdentification X B) :
    etaleRealization X B ⋙ comparisonPullback X B ≅
      ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X ⋙
        ProEtale.finiteCoefficientIntrinsicRealization X B :=
  isoWhiskerLeft (etaleRealization X B) i.iso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (etaleEquivalence X B).unitIso.symm _ ≪≫ Functor.leftUnitor _

/-- Termwise localization of this exact coefficient identification on D+.
Source: Stacks 09AL (blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
def realizedComparisonPlusIso (X : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (i : ComparisonIdentification X B) :
    (etaleRealization X B).mapDerivedCategoryPlus ⋙
        (comparisonPullback X B).mapDerivedCategoryPlus ≅
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X).mapDerivedCategoryPlus ⋙
          (ProEtale.finiteCoefficientIntrinsicRealization X B).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (realizedComparisonIso X B i) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- The direct-image changes of coefficient presentation, normalized on sections, and
exactly their derived base-change transformations, rather than chosen derived isomorphisms.
Source: Stacks 03D6, 05TI, 099R
(blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison). -/
structure CoefficientNormalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (B : Type u) [CommRing B] [Finite B] where
  etale : Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f ⋙
      etaleRealization Y B ≅ etaleRealization X B ⋙ Etale.intrinsicModuleDirectImage f B
  etale_sections : ∀ (M : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) (V : Y.Etaleᵒᵖ)
      (x : M.obj.obj ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj V)),
    (etale.hom.app M).val.app V x = x
  proetale : ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f ⋙
      ProEtale.finiteCoefficientIntrinsicRealization Y B ≅
    ProEtale.finiteCoefficientIntrinsicRealization X B ⋙
      Scheme.proEtaleConstantModuleDirectImage f B
  proetale_sections : ∀ (M : Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) (V : Y.ProEtᵒᵖ)
      (x : M.obj.obj ((Scheme.proEtaleBaseChange f).op.obj V)),
    (proetale.hom.app M).val.app V
      ((proEtaleRealizationUnit Y B
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f).obj M)).app V x) =
      (proEtaleRealizationUnit X B M).app ((Scheme.proEtaleBaseChange f).op.obj V) x
  etalePlus :
    (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f).rightDerivedFunctorPlus ⋙
        (etaleRealization Y B).mapDerivedCategoryPlus ≅
      (etaleRealization X B).mapDerivedCategoryPlus ⋙
        (Etale.intrinsicModuleDirectImage f B).rightDerivedFunctorPlus
  etalePlus_eq : etalePlus.hom = Functor.rightDerivedFunctorPlusBaseChange etale.hom
  proetalePlus :
    (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f).rightDerivedFunctorPlus ⋙
        (ProEtale.finiteCoefficientIntrinsicRealization Y B).mapDerivedCategoryPlus ≅
      (ProEtale.finiteCoefficientIntrinsicRealization X B).mapDerivedCategoryPlus ⋙
        (Scheme.proEtaleConstantModuleDirectImage f B).rightDerivedFunctorPlus
  proetalePlus_eq : proetalePlus.hom = Functor.rightDerivedFunctorPlusBaseChange proetale.hom

/-- Ordinary total derived direct images, their unit-normalized bounded-below restrictions,
and the specified etale/pro-etale comparison after inclusion in the full derived category.
Source: Bhatt--Scholze, Lemma 5.4.3 and Remark 5.4.4; Stacks 070K, 070J, 099R
(blueprint: lem-sfb-ordinary-proetale-direct-image-plus-comparison).

Proof, following all seven steps of the DAG node:
1. Apply prop-pur-kinjective-resolutions-exist to the intrinsic constant-ring module
   categories on the small sites. They are Grothendieck abelian and have K-injective
   resolutions; lem-sp-grothendieck-enough-injectives gives ordinary injectives.
2. Direct image is the actual sectionwise pushforward through
   Etale.intrinsicConstantRingMap, respectively proEtaleCoefficientDirectImageMap.
   Kernels and products are sectionwise, so these
   additive functors are left exact. Their coefficient-presentation isomorphisms carry
   constant scalar sections to themselves; this gives CoefficientNormalization.
3. Apply the functors degreewise and then Qh. Additivity preserves homotopies, cones and
   shifts. Apply lem-weil-pbc-kinjective-total-derived in the sense of
   def-sfb-right-derived-functor: its recorded functor, unit, universal property and
   computation give full. For every
   resolution M -> I, resolutionIso is RF(Qs) followed by the inverse unit at I.
4. By lem-weil-pbc-dplus-injective-representative every bounded-below derived object is
   represented by a bounded-below injective complex, which is K-injective. Both full and
   bounded-below functors therefore compute Q(f_*I), using
   lem-weil-pbc-right-derived-plus-injective. This gives plusIso and plus_computes.
5. Lemma lem-weil-pbc-kinjective-hom-derived identifies all maps between injective models
   with unique homotopy classes. Thus plusIso is natural. On a bounded-below complex use
   lem-sc-bounded-below-injective-resolution-existence to compare with its injective
   resolution; naturality of both units gives exactly unit_eq.
6. The fixed-scalar and intrinsic inverse images are adjoint to the same sectionwise
   module direct image: their ring actions agree on constants, hence after sheafification.
   Use lem-pe-constant-left-module-inverse-image and
   lem-weil-pbc-module-inverse-image-unit-comparison. Adjunction bijections construct the
   unique inverse-image isomorphism carrying one unit to the other. Exactness and
   lem-pe-coefficient-comparison-derived-functor descend it termwise, giving the displayed
   realizedComparisonPlusIso and preserving D+.
7. Apply prop-weil-pbc-comparison-direct-image with u=f, Lambda=ULift B. Conjugate its
   specified rightDerivedFunctorPlusBaseChange by the coefficient identifications to get
   plus, with the explicit component equation below. Conjugate plus by the unit-normalized
   plusIso and exact inverse-image inclusion compatibility to get fullComparison. Every
   factor is a natural isomorphism. No unbounded-below etale comparison is asserted. -/
theorem ordinary_proEtale_direct_image_plus_comparison
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (B : Type u) [CommRing B] [Finite B] :
    ∃ (rE : RightDerivedNormalization (Etale.intrinsicModuleDirectImage f B))
      (rP : RightDerivedNormalization (Scheme.proEtaleConstantModuleDirectImage f B))
      (iX : ComparisonIdentification X B) (iY : ComparisonIdentification Y B)
      (k : CoefficientNormalization f B)
      (plus : (Etale.intrinsicModuleDirectImage f B).rightDerivedFunctorPlus ⋙
          (comparisonPullback Y B).mapDerivedCategoryPlus ≅
        (comparisonPullback X B).mapDerivedCategoryPlus ⋙
          (Scheme.proEtaleConstantModuleDirectImage f B).rightDerivedFunctorPlus),
      (∀ G : DerivedCategory.Plus
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))),
        plus.hom.app ((etaleRealization X B).mapDerivedCategoryPlus.obj G) =
          (comparisonPullback Y B).mapDerivedCategoryPlus.map (k.etalePlus.inv.app G) ≫
          (realizedComparisonPlusIso Y B iY).hom.app
            ((Etale.lowerStar
              (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f).rightDerivedFunctorPlus.obj G) ≫
          (ProEtale.finiteCoefficientIntrinsicRealization Y B).mapDerivedCategoryPlus.map
            ((Functor.rightDerivedFunctorPlusBaseChange
              (ProEtale.lowerStarComparisonUpperStarBaseChange f
                (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))).app G) ≫
          k.proetalePlus.hom.app ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X).mapDerivedCategoryPlus.obj G) ≫
          (Scheme.proEtaleConstantModuleDirectImage f B).rightDerivedFunctorPlus.map
            ((realizedComparisonPlusIso X B iX).inv.app G)) ∧
      ∃ fullComparison : DerivedCategory.Plus.ι ⋙ rE.full ⋙
            (comparisonPullback Y B).mapDerivedCategory ≅
          (comparisonPullback X B).mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι ⋙ rP.full,
        ∀ G : DerivedCategory.Plus (Etale.intrinsicConstantModules X B),
          fullComparison.hom.app G =
            (comparisonPullback Y B).mapDerivedCategory.map (rE.plusIso.hom.app G) ≫
            (comparisonPullback Y B).mapDerivedCategoryPlusCompatibility.inv.app
              ((Etale.intrinsicModuleDirectImage f B).rightDerivedFunctorPlus.obj G) ≫
            DerivedCategory.Plus.ι.map (plus.hom.app G) ≫
            rP.plusIso.inv.app ((comparisonPullback X B).mapDerivedCategoryPlus.obj G) := by
  sorry

end AlgebraicGeometry.SfbOrdinaryComparison
