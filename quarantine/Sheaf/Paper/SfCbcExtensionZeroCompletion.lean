/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.Paper.ConstantCompletionEquivalence
public import Sheaf.Paper.ProEtaleConstantReductionTower
public import Sheaf.Paper.AdicCompletionReduction
public import Sheaf.Paper.CompletionMap
public import Sheaf.Paper.CompletedOpenExchangeTransport
public import Sheaf.Paper.RingedEtaleOriginWitness
public import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import Mathlib.Algebra.Homology.Functor
import Sheaf.CategoryTheory.DiagramSiteRealization
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.Paper.CompletedPullbackAdjunction
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# Strict reduction of completed extension by zero

Source: blueprint fix-lem-exchanges, integral open factor, Steps 1–2;
Stacks Project Tags 099M, 099N and 0941
(blueprint: lem-sf-cbc-extension-zero-completion).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Constant sections uniquely identify the coefficient sheaf on the localized site.
Source: Stacks Tags 098K and 00XZ; Step 1 of the node.
Proof: the concrete slice functor is an equivalence of sites by
lem-weil-proetale-weakly-etale-localization. Restrict the constant presheaf and
apply the sheafification adjunction. Its unit gives the displayed equality;
local generation by constant sections gives uniqueness.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcConstantSliceMap_existsUnique (X : Scheme.{t}) (W : X.ProEt)
    (A : Type t) [CommRing A] :
    ∃! φ : (adicConstantRing X A).over W ⟶
        ((cbcSliceFunctor X W).sheafPushforwardContinuous CommRingCat.{t + 1}
          ((ProEt.topology X).over W) (ProEt.topology W.left)).obj
            (adicConstantRing W.left A),
      ∀ V : Over W,
        (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{t + 1, t} A)))).app (op V.left) ≫
              φ.hom.app (op V) =
        (toSheafify (ProEt.topology W.left)
          ((Functor.const W.left.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{t + 1, t} A)))).app
              (op ((cbcSliceFunctor X W).obj V)) := by
  sorry

/-- The canonical constant coefficient map, fixed by sheafification's unit.
Source: Stacks Tags 098K and 00XZ
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcConstantSliceMap (X : Scheme.{t}) (W : X.ProEt)
    (A : Type t) [CommRing A] :=
  (sfCbcConstantSliceMap_existsUnique X W A).exists.choose

/-- Regard modules on the open scheme as modules on the ambient localized site.
Source: Stacks Tags 098K and 03DI
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcConstantModuleToSlice (X : Scheme.{t}) (W : X.ProEt)
    (A : Type t) [CommRing A] :
    SheafOfModules.{t + 1} (adicModuleRing W.left A) ⥤
      SheafOfModules.{t + 1} ((adicModuleRing X A).over W) :=
  SheafOfModules.pushforward.{t + 1} (F := cbcSliceFunctor X W)
    (J := (ProEt.topology X).over W) (K := ProEt.topology W.left)
    ((sheafCompose ((ProEt.topology X).over W)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
        (sfCbcConstantSliceMap X W A))

/-- Ordinary extension by zero of constant-coefficient module sheaves, for arbitrary A.
It is the direct-sum extension presheaf followed by module sheafification.
Source: Stacks Tags 03DI and 03DJ; Step 1 of the node
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcOpenExtension {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type t) [CommRing A] :
    SheafOfModules.{t + 1} (adicModuleRing U A) ⥤
      SheafOfModules.{t + 1} (adicModuleRing X A) :=
  sfCbcConstantModuleToSlice X (cbcOpenObject j inferInstance) A ⋙
    SheafOfModules.localizedModuleExtension (adicConstantRing X A)
      (cbcOpenObject j inferInstance)

/-- The constant coefficient extension is additive and exact.
Source: Stacks Tags 03DI and 03DJ; Step 1 of the node.
Proof: the ringed-slice transport is an equivalence, by the uniquely specified
constant coefficient comparison and weakly-etale localization. Compose it with
lem-pur-site-restriction-module-adjunction-exact. This requires no quasi-compactness
and applies equally to the empty open and the zero ring.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcOpenExtension_exact {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A] :
    (sfCbcOpenExtension j A).Additive ∧
      PreservesFiniteLimits (sfCbcOpenExtension j A) ∧
      PreservesFiniteColimits (sfCbcOpenExtension j A) := by
  sorry

/-- Additivity supplied by localized extension's exactness. Source: Stacks Tag 03DI
(blueprint: lem-sf-cbc-extension-zero-completion). -/
instance sfCbcOpenExtension_additive {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A] :
    (sfCbcOpenExtension j A).Additive := (sfCbcOpenExtension_exact j A).1

/-- Left exactness supplied by localized extension. Source: Stacks Tag 03DJ
(blueprint: lem-sf-cbc-extension-zero-completion). -/
instance sfCbcOpenExtension_limits {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A] :
    PreservesFiniteLimits (sfCbcOpenExtension j A) := (sfCbcOpenExtension_exact j A).2.1

/-- Right exactness supplied by localized extension. Source: Stacks Tag 03DI
(blueprint: lem-sf-cbc-extension-zero-completion). -/
instance sfCbcOpenExtension_colimits {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A] :
    PreservesFiniteColimits (sfCbcOpenExtension j A) := (sfCbcOpenExtension_exact j A).2.2

/-- The ordinary uncompleted derived extension functor.
Source: Stacks Tag 03DJ; Step 1 of the node
(blueprint: lem-sf-cbc-extension-zero-completion). -/
abbrev sfCbcDerivedExtension {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type t) [CommRing A] :
    proEtaleDerivedCategory U A ⥤ proEtaleDerivedCategory X A :=
  (sfCbcOpenExtension j A).mapDerivedCategory

/-- Constant coefficients on the published small model of the pro-etale site.
Source: Stacks Tags 098K and 00VC
(blueprint: lem-sf-cbc-extension-zero-completion). -/
abbrev sfCbcModelRing (X : Scheme.{t}) (A : Type t) [CommRing A] :=
  ConstantCompletion.constant (proEtaleModelTopology X) (ULift.{t + 1, t} A)

/-- The coefficient transport is fixed on constant sections.
Source: Stacks Tags 00VC and 00XZ.
Proof: precomposition by AsSmall.down is an equivalence of sites. The
sheafification adjunction extends the displayed unit map uniquely, and the
result is invertible because the presheaf equivalence preserves sheafification.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcModelRingMap_existsUnique (X : Scheme.{t}) (A : Type t) [CommRing A] :
    ∃! c : sfCbcModelRing X A ⟶
      ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
        CommRingCat.{t + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj
          (adicConstantRing X A),
      IsIso c ∧ ∀ V : proEtaleSiteModel X,
        (toSheafify (proEtaleModelTopology X)
          ((Functor.const (proEtaleSiteModel X)ᵒᵖ).obj
            (CommRingCat.of (ULift.{t + 1, t} A)))).app (op V) ≫ c.hom.app (op V) =
        (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{t + 1, t} A)))).app (op (AsSmall.down.obj V)) := by
  sorry

/-- Canonical map from the small model's constant ring to the transported ring.
Source: Stacks Tag 00XZ (blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcModelRingMap (X : Scheme.{t}) (A : Type t) [CommRing A] :=
  (sfCbcModelRingMap_existsUnique X A).exists.choose

/-- Exact small-model transport with the canonical constant scalar action.
Source: Stacks Tags 00VC and 03D1
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcModelModules (X : Scheme.{t}) (A : Type t) [CommRing A] :
    SheafOfModules.{t + 1} (adicModuleRing X A) ⥤
      ConstantCompletion.Mod (sfCbcModelRing X A) :=
  proEtaleModuleToModel (adicModuleRing X A) ⋙
    ConstantCompletion.res (sfCbcModelRingMap X A)

/-- Small-model transport is an additive equivalence.
Source: Stacks Tags 00VC and 03D1.
Proof: sectionwise precomposition by AsSmall.down is an equivalence with inverse
precomposition by AsSmall.up. The coefficient map is invertible by
sfCbcModelRingMap_existsUnique. Restriction of scalars along that map is an
additive equivalence as well. Compose these equivalences.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcModelModules_properties (X : Scheme.{t}) (A : Type t) [CommRing A] :
    (sfCbcModelModules X A).IsEquivalence ∧ (sfCbcModelModules X A).Additive := by
  sorry

/-- The canonical model transport is an equivalence. Source: Stacks Tag 00VC
(blueprint: lem-sf-cbc-extension-zero-completion). -/
instance sfCbcModelModules_isEquivalence (X : Scheme.{t}) (A : Type t) [CommRing A] :
    (sfCbcModelModules X A).IsEquivalence := (sfCbcModelModules_properties X A).1

/-- The canonical model transport preserves addition. Source: Stacks Tag 03D1
(blueprint: lem-sf-cbc-extension-zero-completion). -/
instance sfCbcModelModules_additive (X : Scheme.{t}) (A : Type t) [CommRing A] :
    (sfCbcModelModules X A).Additive := (sfCbcModelModules_properties X A).2

/-- Additivity of the forward equivalence in its bundled presentation.
Source: Stacks Tag 03D1 (blueprint: lem-sf-cbc-extension-zero-completion). -/
instance sfCbcModelEquivalence_additive (X : Scheme.{t}) (A : Type t) [CommRing A] :
    (sfCbcModelModules X A).asEquivalence.functor.Additive :=
  inferInstanceAs (sfCbcModelModules X A).Additive

/-- Standard localization size on the equivalent small site. Source: Stacks Tag 05RU
(blueprint: lem-sf-cbc-extension-zero-completion). -/
instance sfCbcModelModules_derived (X : Scheme.{t}) (A : Type t) [CommRing A] :
    HasDerivedCategory (ConstantCompletion.Mod (sfCbcModelRing X A)) :=
  HasDerivedCategory.standard _

/-- Standard localization size for strict towers. Source: Stacks Tag 05RU
(blueprint: lem-sf-cbc-extension-zero-completion). -/
instance sfCbcModelTowers_derived (X : Scheme.{t}) (A : Type t) [CommRing A] :
    HasDerivedCategory (ℕᵒᵖ ⥤ ConstantCompletion.Mod (sfCbcModelRing X A)) :=
  HasDerivedCategory.standard _

/-- The ordinary derived equivalence to the small model.
Source: Stacks Tags 00VC and 05RU
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcModelDerived (X : Scheme.{t}) (A : Type t) [CommRing A] :
    proEtaleDerivedCategory X A ≌ ConstantCompletion.D (sfCbcModelRing X A) :=
  (sfCbcModelModules X A).asEquivalence.mapDerivedCategory

/-- The ideal in the same lifted coefficient ring used by constant sheaves.
Source: Stacks Tag 099M (blueprint: lem-sf-cbc-extension-zero-completion). -/
abbrev sfCbcModelIdeal {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A) :
    Ideal (ULift.{t + 1, t} A) := d.ideal.map ULift.ringEquiv.symm.toRingHom

/-- The derived category of actual strict towers in the small-site presentation.
Source: Stacks Tags 0941 and 00VC
(blueprint: lem-sf-cbc-extension-zero-completion). -/
abbrev sfCbcTowerDerived (X : Scheme.{t}) (A : Type t) [CommRing A] :=
  ConstantCompletion.TD (sfCbcModelRing X A)

/-- Strict reduction uses the universal quotient presentation on one K-flat model.
The small-model transport enlarges only Hom sizes; it does not identify the
original small pro-etale site's object and Hom universes.
Source: Stacks Tags 099M, 06YY and 00VC
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcReduction (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : CompleteCoefficientDatum A) :
    proEtaleDerivedCategory X A ⥤ sfCbcTowerDerived X A :=
  (sfCbcModelDerived X A).functor ⋙
    (ConstantCompletion.quotientPresentation (proEtaleModelTopology X)
      (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false).tower

/-- Completion is total right derived inverse limit of the strict reduction tower.
Source: Stacks Tags 099M and 0941
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcCompletion (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : CompleteCoefficientDatum A) : proEtaleDerivedCategory X A ⥤
      proEtaleDerivedCategory X A :=
  sfCbcReduction X d ⋙ ConstantCompletion.rlim (sfCbcModelRing X A) ⋙
    (sfCbcModelDerived X A).inverse

/-- The prescribed quotient-unit completion map, transported through the equivalence.
Source: Stacks Tags 099M and 00VC
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcCompletionUnit (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : CompleteCoefficientDatum A) : 𝟭 (proEtaleDerivedCategory X A) ⟶
      sfCbcCompletion X d :=
  (sfCbcModelDerived X A).unitIso.hom ≫
    whiskerLeft (sfCbcModelDerived X A).functor
      (whiskerRight
        (ConstantCompletion.completionUnit (proEtaleModelTopology X)
          (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false)
        (sfCbcModelDerived X A).inverse)

/-- The existing local derived-completeness predicate on the equivalent small site.
Source: Stacks Tags 0999 and 099M
(blueprint: lem-sf-cbc-extension-zero-completion). -/
abbrev sfCbcIsComplete (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : CompleteCoefficientDatum A) (K : proEtaleDerivedCategory X A) : Prop :=
  ConstantCompletion.IsComplete
    (ConstantCompletion.quotient (proEtaleModelTopology X)
      (ULift.{t + 1, t} A) (sfCbcModelIdeal d) 0)
    ((sfCbcModelDerived X A).functor.obj K)

/-- The flat K-flat model of extension is the actual termwise extended complex.
Source: Stacks Tags 06YS, 03DI and 0E8I; Step 1 of the node.
Proof: the projection formula identifies tensoring an extended flat module
with exact restriction, tensoring on U, and exact extension. Thus its terms
are flat. Extension is a left adjoint, so it preserves the direct sums in
total tensor complexes. Exact restriction sends acyclic complexes to acyclic
complexes, K-flatness makes their tensor acyclic on U, and exact extension
preserves that acyclicity. Exactness also descends the realization map.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcExtensionModel_existsUnique {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A]
    {K : proEtaleDerivedCategory U A} (M : AdicKFlatModel U A K) :
    ∃! N : AdicKFlatModel X A ((sfCbcDerivedExtension j A).obj K),
      N.complex = ((sfCbcOpenExtension j A).mapHomologicalComplex (.up ℤ)).obj M.complex ∧
      HEq N.realization
        (((sfCbcOpenExtension j A).mapDerivedCategoryFactors.app M.complex).symm ≪≫
          (sfCbcDerivedExtension j A).mapIso M.realization) := by
  sorry

/-- The canonical termwise extended model; its complex and realization determine it.
Source: Step 1 of the node (blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcExtensionModel {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type t) [CommRing A] {K : proEtaleDerivedCategory U A}
    (M : AdicKFlatModel U A K) :=
  (sfCbcExtensionModel_existsUnique j A M).exists.choose

/-- Ordinary extension transported to the equivalent small-site module categories.
Source: Stacks Tags 00VC and 03DI
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcModelExtension {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type t) [CommRing A] :
    ConstantCompletion.Mod (sfCbcModelRing U A) ⥤
      ConstantCompletion.Mod (sfCbcModelRing X A) :=
  (sfCbcModelModules U A).asEquivalence.inverse ⋙ sfCbcOpenExtension j A ⋙
    sfCbcModelModules X A

/-- Additivity is preserved through the two model equivalences.
Source: Stacks Tags 00VC and 03DI
(blueprint: lem-sf-cbc-extension-zero-completion). -/
instance sfCbcModelExtension_additive {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A] :
    (sfCbcModelExtension j A).Additive :=
  inferInstanceAs ((sfCbcModelModules U A).asEquivalence.inverse ⋙
    sfCbcOpenExtension j A ⋙ sfCbcModelModules X A).Additive

/-- Left exactness survives the equivalence transport. Source: Stacks Tag 00VC
(blueprint: lem-sf-cbc-extension-zero-completion). -/
instance sfCbcModelExtension_limits {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A] :
    PreservesFiniteLimits (sfCbcModelExtension j A) :=
  inferInstanceAs (PreservesFiniteLimits ((sfCbcModelModules U A).asEquivalence.inverse ⋙
    sfCbcOpenExtension j A ⋙ sfCbcModelModules X A))

/-- Right exactness survives the equivalence transport. Source: Stacks Tag 00VC
(blueprint: lem-sf-cbc-extension-zero-completion). -/
instance sfCbcModelExtension_colimits {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A] :
    PreservesFiniteColimits (sfCbcModelExtension j A) :=
  inferInstanceAs (PreservesFiniteColimits ((sfCbcModelModules U A).asEquivalence.inverse ⋙
    sfCbcOpenExtension j A ⋙ sfCbcModelModules X A))

/-- Exact termwise extension on the derived small-site presentation.
Source: Stacks Tags 03DJ and 00VC
(blueprint: lem-sf-cbc-extension-zero-completion). -/
abbrev sfCbcModelDerivedExtension {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A] :=
  (sfCbcModelExtension j A).mapDerivedCategory

/-- The termwise ordinary extension functor on actual strict towers.
Source: Stacks Tag 0941 (blueprint: lem-sf-cbc-extension-zero-completion). -/
abbrev sfCbcTowerExtension {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type t) [CommRing A] :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (sfCbcModelExtension j A)

/-- Termwise extension is exact also on strict towers.
Source: Stacks Tags 03DJ and 0941; Step 2 of the node.
Proof: kernels and cokernels of diagrams are computed pointwise. At every
index the functor is the exact ordinary module extension. Evaluations jointly
reflect the finite-limit and finite-colimit universal properties, proving both
preservation clauses. Additivity is checked at the same evaluations.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcTowerExtension_exact {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A] :
    (sfCbcTowerExtension j A).Additive ∧
      PreservesFiniteLimits (sfCbcTowerExtension j A) ∧
      PreservesFiniteColimits (sfCbcTowerExtension j A) := by
  sorry

/-- Additivity of termwise extension. Source: Stacks Tag 0941
(blueprint: lem-sf-cbc-extension-zero-completion). -/
instance sfCbcTowerExtension_additive {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A] :
    (sfCbcTowerExtension j A).Additive := (sfCbcTowerExtension_exact j A).1

/-- Left exactness of termwise extension. Source: Stacks Tag 0941
(blueprint: lem-sf-cbc-extension-zero-completion). -/
instance sfCbcTowerExtension_limits {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A] :
    PreservesFiniteLimits (sfCbcTowerExtension j A) := (sfCbcTowerExtension_exact j A).2.1

/-- Right exactness of termwise extension. Source: Stacks Tag 0941
(blueprint: lem-sf-cbc-extension-zero-completion). -/
instance sfCbcTowerExtension_colimits {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A] :
    PreservesFiniteColimits (sfCbcTowerExtension j A) := (sfCbcTowerExtension_exact j A).2.2

/-- The ordinary exact extension functor on derived strict towers.
Source: Stacks Tag 0941 (blueprint: lem-sf-cbc-extension-zero-completion). -/
abbrev sfCbcDerivedTowerExtension {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A] :
    sfCbcTowerDerived U A ⥤ sfCbcTowerDerived X A :=
  (sfCbcTowerExtension j A).mapDerivedCategory

/-- The published universal K-flat presentation of strict reductions on the small model.
Source: Stacks Tags 099M and 06YY
(blueprint: lem-sf-cbc-extension-zero-completion). -/
abbrev sfCbcQuotientPresentation (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : CompleteCoefficientDatum A) :=
  ConstantCompletion.quotientPresentation (proEtaleModelTopology X)
    (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false

/-- Ordinary tensor projection comparison, as one isomorphism of strict quotient diagrams.
Its equation fixes the map by the actual quotient units, not just its endpoints.
Source: Stacks Tag 0E8I; Step 2 of the node.
Proof: use the ringed-slice tensor projection formula on every quotient.
Both unit composites send m to the extension of 1 tensor m. Quotient units
are epimorphisms, so this equation determines each component uniquely.
Naturality of tensor in the quotient coefficient makes the components commute
with every quotient transition, giving the isomorphism of strict diagrams.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcOrdinaryTensorComparison_existsUnique {U X : Scheme.{t}}
    (j : U ⟶ X) [IsOpenImmersion j] {A : Type t} [CommRing A]
    (d : CompleteCoefficientDatum A) :
    ∃! e : sfCbcModelExtension j A ⋙
        ConstantCompletion.reductionTower (proEtaleModelTopology X)
          (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false ≅
      ConstantCompletion.reductionTower (proEtaleModelTopology U)
        (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false ⋙ sfCbcTowerExtension j A,
      ∀ (M : ConstantCompletion.Mod (sfCbcModelRing U A)) (n : ℕ),
        ((ConstantCompletion.reductionUnit (proEtaleModelTopology X)
            (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false).app
              ((sfCbcModelExtension j A).obj M)).app (op n) ≫
            (e.hom.app M).app (op n) =
          (sfCbcModelExtension j A).map
            (((ConstantCompletion.reductionUnit (proEtaleModelTopology U)
              (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false).app M).app (op n)) := by
  sorry

/-- The unique strict ordinary tensor comparison with the quotient-unit normalization.
Source: Stacks Tag 0E8I (blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcOrdinaryTensorComparison {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A) :=
  (sfCbcOrdinaryTensorComparison_existsUnique j d).exists.choose

/-- Canonical transport of the exact derived extension functor.
Source: Stacks Tags 00VC and 05RU
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcExtensionTransport {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type t) [CommRing A] :
    sfCbcDerivedExtension j A ⋙ (sfCbcModelDerived X A).functor ≅
      (sfCbcModelDerived U A).functor ⋙ sfCbcModelDerivedExtension j A :=
  (Functor.mapDerivedCategoryCompIso (sfCbcOpenExtension j A)
      (sfCbcModelModules X A)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (isoWhiskerRight (sfCbcModelModules U A).asEquivalence.unitIso
        (sfCbcOpenExtension j A ⋙ sfCbcModelModules X A)) ≪≫
    Functor.mapDerivedCategoryCompIso (sfCbcModelModules U A) (sfCbcModelExtension j A)

/-- Zero morphisms on the ordinary extension/reduction route.
Source: Stacks Tags 03DI and 06YY
(blueprint: lem-sf-cbc-extension-zero-completion). -/
instance sfCbcTensorRoute_zero {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A) :
    (sfCbcModelExtension j A ⋙ ConstantCompletion.reductionTower
      (proEtaleModelTopology X) (ULift.{t + 1, t} A) (sfCbcModelIdeal d)
        false).PreservesZeroMorphisms := by
  let := ConstantCompletion.reductionTower_additive (proEtaleModelTopology X)
    (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false
  infer_instance

/-- Zero morphisms on reduction followed by extension. Source: Stacks Tag 03DI
(blueprint: lem-sf-cbc-extension-zero-completion). -/
instance sfCbcTensorRightRoute_zero {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A) :
    (ConstantCompletion.reductionTower (proEtaleModelTopology U)
      (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false ⋙
        sfCbcTowerExtension j A).PreservesZeroMorphisms := by
  let := ConstantCompletion.reductionTower_additive (proEtaleModelTopology U)
    (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false
  infer_instance

/-- Normalization of the derived tensor comparison on every flat-term K-flat complex.
Both sides use the universal quotient counits and the ordinary tensor comparison.
Source: Stacks Tag 06YY; Step 2 of the node
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcTensorComparisonNormalized {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    (e : sfCbcModelDerivedExtension j A ⋙ (sfCbcQuotientPresentation X d).tower ≅
      (sfCbcQuotientPresentation U d).tower ⋙ sfCbcDerivedTowerExtension j A) : Prop := by
  letI := sfCbcTensorRightRoute_zero j d
  letI := sfCbcTensorRoute_zero j d
  exact ∀ P : ConstantCompletion.Cx (sfCbcModelRing U A), P.IsAcyclicTensorKFlat →
    (∀ i : ℤ, SheafOfModules.IsFlat (P.X i)) →
      e.hom.app ((ConstantCompletion.Q (sfCbcModelRing U A)).obj P) ≫
          (sfCbcDerivedTowerExtension j A).map
            ((sfCbcQuotientPresentation U d).comparison.app P) ≫
          (sfCbcTowerExtension j A).mapDerivedCategoryFactors.hom.app
            (ConstantCompletion.reductionComplex (proEtaleModelTopology U)
              (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false P) =
        (sfCbcQuotientPresentation X d).tower.map
            ((sfCbcModelExtension j A).mapDerivedCategoryFactors.hom.app P) ≫
          (sfCbcQuotientPresentation X d).comparison.app
            (((sfCbcModelExtension j A).mapHomologicalComplex (.up ℤ)).obj P) ≫
          (ConstantCompletion.TQ (sfCbcModelRing X A)).map
            ((NatIso.mapHomologicalComplex (sfCbcOrdinaryTensorComparison j d)
              (.up ℤ)).hom.app P)

/-- The tensor projection comparison descends uniquely to derived strict towers.
Source: Stacks Tags 06YY, 0E8I and 0941; Steps 1–2 of the node.
Proof: extension preserves flat K-flat complexes by Step 1. The ordinary
comparison is a strict quotient-diagram isomorphism. Apply it degreewise on
one such complex and localize in the tower category. The universal quotient
counits give the displayed formula. All complexes have flat K-flat resolutions;
localization at quasi-isomorphisms therefore extends the comparison uniquely,
naturally in the input, and preserves its inverse.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcTensorComparison_existsUnique {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A) :
    ∃! e : sfCbcModelDerivedExtension j A ⋙ (sfCbcQuotientPresentation X d).tower ≅
      (sfCbcQuotientPresentation U d).tower ⋙ sfCbcDerivedTowerExtension j A,
      sfCbcTensorComparisonNormalized j d e := by
  sorry

/-- The canonical strict derived tensor comparison, transported back to the named scheme.
Source: Stacks Tags 00VC, 06YY and 0E8I
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcTensorComparison {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A) :
    sfCbcDerivedExtension j A ⋙ sfCbcReduction X d ≅
      sfCbcReduction U d ⋙ sfCbcDerivedTowerExtension j A :=
  isoWhiskerRight (sfCbcExtensionTransport j A) (sfCbcQuotientPresentation X d).tower ≪≫
    isoWhiskerLeft (sfCbcModelDerived U A).functor
      (sfCbcTensorComparison_existsUnique j d).exists.choose

/-- Reduction of the specified completion unit on ordinary extension by zero.
Source: Stacks Tag 099M; Step 3 of the node
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcReducedCompletionUnit {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A) :
    sfCbcDerivedExtension j A ⋙ sfCbcReduction X d ⟶
      sfCbcDerivedExtension j A ⋙ sfCbcCompletion X d ⋙ sfCbcReduction X d :=
  whiskerLeft (sfCbcDerivedExtension j A)
    (whiskerRight (sfCbcCompletionUnit X d) (sfCbcReduction X d))

/-- The reduced unit is invertible in the derived category of strict towers.
Source: Stacks Tag 099M; Step 3 of the node.
Proof: apply lemma-weil-pbc-adic-completion-reduction to J K. At each n the
adjoint of the n-th limit projection is an isomorphism and its composite with
the reduced completion unit is identity. Hence the reduced unit at n is its
inverse. Exact evaluation detects acyclic cones in the tower category, so
the whole strict tower morphism is invertible. No completeness of J K is used.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcReducedCompletionUnit_isIso {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A) :
    IsIso (sfCbcReducedCompletionUnit j d) := by
  sorry

/-- Completed extension is ordinary extension followed by completion.
Source: Stacks Tag 099M; Step 4 of the node
(blueprint: lem-sf-cbc-extension-zero-completion). -/
abbrev sfCbcCompletedExtension {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A) :=
  sfCbcDerivedExtension j A ⋙ sfCbcCompletion X d

/-- The canonical q-map is inverse reduced unit followed by the tensor comparison.
Source: Step 4 of the node (blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcCompletedReductionIso {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A) :
    sfCbcCompletedExtension j d ⋙ sfCbcReduction X d ≅
      sfCbcReduction U d ⋙ sfCbcDerivedTowerExtension j A :=
  (@asIso _ _ _ _ (sfCbcReducedCompletionUnit j d)
    (sfCbcReducedCompletionUnit_isIso j d)).symm ≪≫ sfCbcTensorComparison j d

/-- The completion presentation, obtained by applying Rlim to the strict tensor comparison.
Source: Stacks Tags 099M and 0941; Step 6 of the node
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcCompletedExtensionPresentation {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A) :
    sfCbcCompletedExtension j d ≅
      sfCbcReduction U d ⋙ sfCbcDerivedTowerExtension j A ⋙
        ConstantCompletion.rlim (sfCbcModelRing X A) ⋙ (sfCbcModelDerived X A).inverse :=
  isoWhiskerRight (sfCbcTensorComparison j d)
    (ConstantCompletion.rlim (sfCbcModelRing X A) ⋙ (sfCbcModelDerived X A).inverse)

open Classical in
/-- Insert a section into its factorization summand of the extension presheaf,
then apply module sheafification. This is the actual extension generator.
Source: Stacks Tag 03DI (blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcExtensionSection {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type t) [CommRing A] (M : SheafOfModules.{t + 1} (adicModuleRing U A))
    (V : X.ProEt) (a : V ⟶ cbcOpenObject j inferInstance)
    (m : M.val.obj (op ((cbcSliceFunctor X (cbcOpenObject j inferInstance)).obj
      (Over.mk a)))) : ((sfCbcOpenExtension j A).obj M).val.obj (op V) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (adicModuleRing X A).obj)).unit.app
    ((SheafOfModules.extensionByZeroPresheaf.{t + 1} (adicModuleRing X A)
      (cbcOpenObject j inferInstance)).obj
        ((sfCbcConstantModuleToSlice X (cbcOpenObject j inferInstance) A).obj M))).app
          (op V)
            (DirectSum.lof ((adicConstantRing X A).obj.obj (op V))
              (V ⟶ cbcOpenObject j inferInstance)
              (fun b ↦ ((sfCbcConstantModuleToSlice X (cbcOpenObject j inferInstance) A).obj
                M).val.obj (op (Over.mk b))) a m)

/-- Ordinary scalar restriction commutes with extension by zero by the same summands.
The equality on extension generators fixes the comparison uniquely.
Source: Stacks Tags 03DI and 03D3; Step 5 of the node.
Proof: restriction changes only the scalar action. In each factorization summand
its underlying group is unchanged, and its maps keep the same section.
The identity on these summands respects restrictions and the scalar homomorphism.
Sheafify, using exactness of restriction, and apply the inverse identity on summands.
Local generation gives the two inverse identities and uniqueness, naturally in M.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcRestrictExtensionIso_existsUnique {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A B : Type t} [CommRing A] [CommRing B] (φ : A →+* B) :
    ∃! e : SheafOfModules.restrictScalars (adicModuleMap U φ) ⋙ sfCbcOpenExtension j A ≅
      sfCbcOpenExtension j B ⋙ SheafOfModules.restrictScalars (adicModuleMap X φ),
      ∀ (M : SheafOfModules.{t + 1} (adicModuleRing U B)) (V : X.ProEt)
        (a : V ⟶ cbcOpenObject j inferInstance)
        (m : M.val.obj (op ((cbcSliceFunctor X (cbcOpenObject j inferInstance)).obj
          (Over.mk a)))),
        (e.hom.app M).val.app (op V)
            (sfCbcExtensionSection j A
              ((SheafOfModules.restrictScalars (adicModuleMap U φ)).obj M) V a m) =
          sfCbcExtensionSection j B M V a m := by
  sorry

/-- Canonical restriction/extension comparison, fixed by extension generators.
Source: Stacks Tag 03DI (blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcRestrictExtensionIso {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A B : Type t} [CommRing A] [CommRing B] (φ : A →+* B) :=
  (sfCbcRestrictExtensionIso_existsUnique j φ).exists.choose

/-- Exact derived scalar restriction commutes with extension by zero, retaining its
ordinary generator normalization.
Source: Stacks Tags 03DI, 03D3 and 05RU
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcDerivedRestrictExtensionIso {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A B : Type t} [CommRing A] [CommRing B] (φ : A →+* B) :
    adicDerivedRestrict U φ ⋙ sfCbcDerivedExtension j A ≅
      sfCbcDerivedExtension j B ⋙ adicDerivedRestrict X φ := by
  letI := (adicRestrictScalars_exact U φ).1
  letI := (adicRestrictScalars_exact U φ).2
  letI := (adicRestrictScalars_exact X φ).1
  letI := (adicRestrictScalars_exact X φ).2
  exact (Functor.mapDerivedCategoryCompIso
      (SheafOfModules.restrictScalars (adicModuleMap U φ))
      (sfCbcOpenExtension j A)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (sfCbcRestrictExtensionIso j φ) ≪≫
    Functor.mapDerivedCategoryCompIso (sfCbcOpenExtension j B)
      (SheafOfModules.restrictScalars (adicModuleMap X φ))

/-- The finite tensor comparison is the adjoint of the extended quotient unit.
Its target retains the actual quotient coefficient action.
Source: Stacks Tags 03DI, 0E8I and 06YY; Steps 1–2 and 5 of the node
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcFiniteTensorHom {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    {K : proEtaleDerivedCategory U A} (M : AdicKFlatModel U A K) (n : ℕ) :
    adicReduction X d (sfCbcExtensionModel j A M) ⟨n + 1, Nat.succ_pos n⟩ ⟶
      (sfCbcDerivedExtension j (A ⧸ d.ideal ^ (n + 1))).obj
        (adicReduction U d M ⟨n + 1, Nat.succ_pos n⟩) :=
  (adicReductionHomEquiv X d (sfCbcExtensionModel j A M) n _).symm
    ((sfCbcDerivedExtension j A).map (adicReductionDerivedUnit U d M n) ≫
      (sfCbcDerivedRestrictExtensionIso j
        (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).hom.app
          (adicReduction U d M ⟨n + 1, Nat.succ_pos n⟩))

/-- The finite tensor comparison is an isomorphism over P_n, with its prescribed action.
Source: Stacks Tags 0E8I and 06YY; Steps 1–2 and 5 of the node.
Proof: compute on the flat K-flat model and its termwise extension. The ringed-slice
tensor formula is P_n-linear by naturality in the quotient coefficient module.
Its unit inserts 1 tensor m, exactly the adjunction formula defining the map above.
The derived scalar adjunction identifies it with that invertible model comparison.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcFiniteTensorHom_isIso {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    {K : proEtaleDerivedCategory U A} (M : AdicKFlatModel U A K) (n : ℕ) :
    IsIso (sfCbcFiniteTensorHom j d M n) := by
  sorry

/-- The completion presentation agrees with the recorded Roos model and its unit.
The unit equation determines the isomorphism by the reflector universal property.
Source: Stacks Tags 099M and 0941; Steps 3 and 6 of the node.
Proof: both objects are the total derived limit of the same strict quotient tower
on M. The quotient-unit normalization of the universal reduction counit and the
right-derived-limit comparison identifies their units. Both are derived complete
by lem-sp-completed-pullback-adjunction. Its Hom bijection makes the comparison
unique, and the reverse comparison shows it is an isomorphism.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcCompletionModelIso_existsUnique (X : Scheme.{t}) {A : Type t}
    [CommRing A] (d : CompleteCoefficientDatum A) {K : proEtaleDerivedCategory X A}
    (M : AdicKFlatModel X A K) :
    ∃! c : (sfCbcCompletion X d).obj K ≅ adicCompletionObject X d M,
      (sfCbcCompletionUnit X d).app K ≫ c.hom = adicCompletionMap X d M := by
  sorry

/-- Canonical unit-preserving comparison with the recorded Roos model.
Source: Stacks Tags 099M and 0941
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcCompletionModelIso (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : CompleteCoefficientDatum A) {K : proEtaleDerivedCategory X A}
    (M : AdicKFlatModel X A K) :=
  (sfCbcCompletionModelIso_existsUnique X d M).exists.choose

/-- The finite forward comparison is the adjoint of the actual n-th limit projection,
followed by the tensor comparison. No completeness of the input is assumed.
Source: Stacks Tag 099M; Steps 3–4 of the node
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcFiniteCompletedHom {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    {K : proEtaleDerivedCategory U A} (M : AdicKFlatModel U A K)
    (N : AdicKFlatModel X A ((sfCbcCompletedExtension j d).obj K)) (n : ℕ) :
    adicReduction X d N ⟨n + 1, Nat.succ_pos n⟩ ⟶
      (sfCbcDerivedExtension j (A ⧸ d.ideal ^ (n + 1))).obj
        (adicReduction U d M ⟨n + 1, Nat.succ_pos n⟩) :=
  (adicReductionHomEquiv X d N n _).symm
    ((sfCbcCompletionModelIso X d (sfCbcExtensionModel j A M)).hom ≫
      adicCompletionEvaluation X d (sfCbcExtensionModel j A M) n ≫
      (adicDerivedRestrictFactors X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
        (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
          (sfCbcExtensionModel j A M).complex)).inv) ≫ sfCbcFiniteTensorHom j d M n

/-- Finite completion comparison and its inverse reduced-unit formula, over P_n itself.
Source: Stacks Tag 099M; Steps 3–5 of the node.
Proof: the adjoint of projection is invertible by
lemma-weil-pbc-adic-completion-reduction. Its composite with the reduced completion
unit is identity by the projection identity of that unit and scalar-unit naturality.
Compose with the tensor comparison. The displayed inverse is forced by these two
identities. Every map is P_n-linear, before restriction to A coefficients.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcFiniteCompletedHom_inverse {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    {K : proEtaleDerivedCategory U A} (M : AdicKFlatModel U A K)
    (N : AdicKFlatModel X A ((sfCbcCompletedExtension j d).obj K)) (n : ℕ) :
    ∃ h : IsIso (sfCbcFiniteCompletedHom j d M N n),
      (@asIso _ _ _ _ (sfCbcFiniteCompletedHom j d M N n) h).inv =
        (@asIso _ _ _ _ (sfCbcFiniteTensorHom j d M n)
          (sfCbcFiniteTensorHom_isIso j d M n)).inv ≫
          adicReductionMap X d (sfCbcExtensionModel j A M) N n
            ((sfCbcCompletionUnit X d).app ((sfCbcDerivedExtension j A).obj K)) := by
  sorry

/-- The finite comparison with its specified inverse, as an isomorphism.
Source: Stacks Tag 099M (blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcFiniteCompletedIso {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    {K : proEtaleDerivedCategory U A} (M : AdicKFlatModel U A K)
    (N : AdicKFlatModel X A ((sfCbcCompletedExtension j d).obj K)) (n : ℕ) :=
  @asIso _ _ _ _ (sfCbcFiniteCompletedHom j d M N n)
    (sfCbcFiniteCompletedHom_inverse j d M N n).choose

/-- The A-linear version of the same finite comparison, using the recorded
restriction-of-scalars factorization and no change of quotient maps.
Source: Stacks Tags 03DI and 099M
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcFiniteUnderlyingHom {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    {K : proEtaleDerivedCategory U A} (M : AdicKFlatModel U A K)
    (N : AdicKFlatModel X A ((sfCbcCompletedExtension j d).obj K)) (n : ℕ) :
    adicReductionUnderlying X d N ⟨n + 1, Nat.succ_pos n⟩ ⟶
      (sfCbcDerivedExtension j A).obj
        (adicReductionUnderlying U d M ⟨n + 1, Nat.succ_pos n⟩) :=
  (adicDerivedRestrictFactors X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
    (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) N.complex)).inv ≫
    (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).map
      (sfCbcFiniteCompletedHom j d M N n) ≫
    (sfCbcDerivedRestrictExtensionIso j (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).inv.app
      (adicReduction U d M ⟨n + 1, Nat.succ_pos n⟩) ≫
    (sfCbcDerivedExtension j A).map
      (adicDerivedRestrictFactors U (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
        (adicChange U (Ideal.Quotient.mk (d.ideal ^ (n + 1))) M.complex)).hom

/-- Every quotient transition commutes with the specified finite comparison.
Source: Stacks Tags 0941 and 099M; Step 5 of the node.
Proof: the tensor comparisons commute with all quotient algebra homomorphisms,
by their common 1-tensor-section normalization. Limit projections commute with
those same transitions by the limit cone identity. Transpose these equalities
under the scalar adjunction; its unit is natural. Composing the resulting
squares gives the displayed equality, before any derived limit is applied.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcFiniteUnderlyingHom_transition {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    {K : proEtaleDerivedCategory U A} (M : AdicKFlatModel U A K)
    (N : AdicKFlatModel X A ((sfCbcCompletedExtension j d).obj K))
    (m n : ℕ) (h : n ≤ m) :
    adicTransition X d N ⟨m + 1, Nat.succ_pos m⟩ ⟨n + 1, Nat.succ_pos n⟩
        (Nat.succ_le_succ h) ≫ sfCbcFiniteUnderlyingHom j d M N n =
      sfCbcFiniteUnderlyingHom j d M N m ≫
        (sfCbcDerivedExtension j A).map
          (adicTransition U d M ⟨m + 1, Nat.succ_pos m⟩ ⟨n + 1, Nat.succ_pos n⟩
            (Nat.succ_le_succ h)) := by
  sorry

/-- Finite comparisons are natural in arbitrary input maps and model choices.
Source: Stacks Tags 06YY and 099M; Step 5 of the node.
Proof: the reduced completion unit and its inverse are natural, as is the tensor
comparison. Equivalently, naturality of the limit projections and the scalar
adjunction gives this equation directly from the definition of the finite map.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcFiniteCompletedHom_naturality {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    {K L : proEtaleDerivedCategory U A} (M : AdicKFlatModel U A K)
    (M' : AdicKFlatModel U A L)
    (N : AdicKFlatModel X A ((sfCbcCompletedExtension j d).obj K))
    (N' : AdicKFlatModel X A ((sfCbcCompletedExtension j d).obj L))
    (f : K ⟶ L) (n : ℕ) :
    adicReductionMap X d N N' n ((sfCbcCompletedExtension j d).map f) ≫
        sfCbcFiniteCompletedHom j d M' N' n =
      sfCbcFiniteCompletedHom j d M N n ≫
        (sfCbcDerivedExtension j (A ⧸ d.ideal ^ (n + 1))).map
          (adicReductionMap U d M M' n f) := by
  sorry

/-- Exact evaluation in the actual strict diagram category on the small model.
Source: Stacks Tag 0941 (blueprint: lem-sf-cbc-extension-zero-completion). -/
abbrev sfCbcEvaluateModule (X : Scheme.{t}) (A : Type t) [CommRing A] (n : ℕ) :=
  (CategoryTheory.evaluation ℕᵒᵖ (ConstantCompletion.Mod (sfCbcModelRing X A))).obj (op n)

/-- Evaluation is derived after forming the strict diagram category.
Source: Stacks Tag 0941 (blueprint: lem-sf-cbc-extension-zero-completion). -/
abbrev sfCbcEvaluate (X : Scheme.{t}) (A : Type t) [CommRing A] (n : ℕ) :=
  (sfCbcEvaluateModule X A n).mapDerivedCategory

/-- The canonical site-model transport preserves flat-term K-flat representatives.
Source: Stacks Tags 00VC and 06YY.
Proof: transport the tensor unit and tensor product along the ringed-site equivalence.
It is exact and preserves direct sums. It therefore transports total tensor products
and acyclic complexes, which proves K-flatness and termwise flatness.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcModelComplex_kflat (X : Scheme.{t}) {A : Type t} [CommRing A]
    {K : proEtaleDerivedCategory X A} (M : AdicKFlatModel X A K) :
    CochainComplex.IsAcyclicTensorKFlat (R := sfCbcModelRing X A)
      (((sfCbcModelModules X A).mapHomologicalComplex (.up ℤ)).obj M.complex) ∧
      ∀ i : ℤ, SheafOfModules.IsFlat
        ((((sfCbcModelModules X A).mapHomologicalComplex (.up ℤ)).obj M.complex).X i) := by
  sorry

/-- Ordinary finite reductions commute with the fixed ringed-site equivalence.
The quotient-unit equation in each degree uniquely fixes the tensor comparison.
Source: Stacks Tags 00VC, 03EK and 06YY.
Proof: on constant scalar sections both maps send m to 1 tensor m. Sheafification
and the quotient scalar map give the comparison and its inverse. The augmentation
is an epimorphism in every degree, so the equation determines the chain map uniquely.
Compatibility with differentials is naturality of the scalar unit.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcFiniteModelIso_existsUnique (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : CompleteCoefficientDatum A) {K : proEtaleDerivedCategory X A}
    (M : AdicKFlatModel X A K) (n : ℕ) :
    ∃! e : ((sfCbcEvaluateModule X A n).mapHomologicalComplex (.up ℤ)).obj
        (ConstantCompletion.reductionComplex (proEtaleModelTopology X)
          (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false
          (((sfCbcModelModules X A).mapHomologicalComplex (.up ℤ)).obj M.complex)) ≅
      ((sfCbcModelModules X A).mapHomologicalComplex (.up ℤ)).obj
        (adicReductionComplex X d M n),
      ∀ i : ℤ,
        ((ConstantCompletion.reductionUnit (proEtaleModelTopology X)
          (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false).app
            ((sfCbcModelModules X A).obj (M.complex.X i))).app (op n) ≫ e.hom.f i =
          (sfCbcModelModules X A).map ((adicReductionAugmentation X d M n).f i) := by
  sorry

/-- Canonical evaluation of the strict reduction at finite level. The formula uses
one model, the universal quotient counit, and the unit-normalized ordinary comparison.
Source: Stacks Tags 0941 and 06YY
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcFiniteEvaluationIso (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : CompleteCoefficientDatum A) {K : proEtaleDerivedCategory X A}
    (M : AdicKFlatModel X A K) (n : ℕ) :
    (sfCbcEvaluate X A n).obj ((sfCbcReduction X d).obj K) ≅
      (sfCbcModelDerived X A).functor.obj
        (adicReductionUnderlying X d M ⟨n + 1, Nat.succ_pos n⟩) :=
  (sfCbcEvaluate X A n).mapIso
    ((sfCbcQuotientPresentation X d).tower.mapIso
      ((sfCbcModelDerived X A).functor.mapIso M.realization.symm ≪≫
        (sfCbcModelModules X A).mapDerivedCategoryFactors.app M.complex) ≪≫
      @asIso _ _ _ _ ((sfCbcQuotientPresentation X d).comparison.app
        (((sfCbcModelModules X A).mapHomologicalComplex (.up ℤ)).obj M.complex))
        ((sfCbcQuotientPresentation X d).laws.2.1 _
          (sfCbcModelComplex_kflat X M).1 (sfCbcModelComplex_kflat X M).2)) ≪≫
    (sfCbcEvaluateModule X A n).mapDerivedCategoryFactors.app
      (ConstantCompletion.reductionComplex (proEtaleModelTopology X)
        (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false
          (((sfCbcModelModules X A).mapHomologicalComplex (.up ℤ)).obj M.complex)) ≪≫
    (ConstantCompletion.Q (sfCbcModelRing X A)).mapIso
      (sfCbcFiniteModelIso_existsUnique X d M n).exists.choose ≪≫
    ((sfCbcModelModules X A).mapDerivedCategoryFactors.app
      (adicReductionComplex X d M n)).symm

/-- Evaluation commutes with termwise extension by the identity natural isomorphism.
Source: Stacks Tag 0941 (blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcEvaluateExtensionIso {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type t) [CommRing A] (n : ℕ) :
    sfCbcDerivedTowerExtension j A ⋙ sfCbcEvaluate X A n ≅
      sfCbcEvaluate U A n ⋙ sfCbcModelDerivedExtension j A :=
  (Functor.mapDerivedCategoryCompIso (sfCbcTowerExtension j A)
    (sfCbcEvaluateModule X A n)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (Iso.refl _) ≪≫
      Functor.mapDerivedCategoryCompIso (sfCbcEvaluateModule U A n)
        (sfCbcModelExtension j A)

/-- Evaluating the actual strict q-map gives exactly the prescribed finite
P_n-linear map after scalar restriction, with all comparisons fixed above.
Source: Stacks Tags 0941 and 099M; Steps 3–5 of the node.
Proof: on a flat K-flat model, evaluation of the universal quotient counit is the
ordinary finite quotient complex. The normalized tensor comparison evaluates to
sfCbcFiniteTensorHom, by its scalar-unit characterization. The limit-unit equation
identifies inverse reduced unit with the adjoint of projection. Compose these
identities, using sfCbcFiniteModelIso's quotient-unit equation and exact-derived
factorizations. This gives the displayed square in D(X,A), with no derived limit.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcCompletedReductionIso_evaluation {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    {K : proEtaleDerivedCategory U A} (M : AdicKFlatModel U A K)
    (N : AdicKFlatModel X A ((sfCbcCompletedExtension j d).obj K)) (n : ℕ) :
    (sfCbcEvaluate X A n).map ((sfCbcCompletedReductionIso j d).hom.app K) ≫
        (sfCbcEvaluateExtensionIso j A n).hom.app ((sfCbcReduction U d).obj K) ≫
        (sfCbcModelDerivedExtension j A).map (sfCbcFiniteEvaluationIso U d M n).hom ≫
        (sfCbcExtensionTransport j A).inv.app
          (adicReductionUnderlying U d M ⟨n + 1, Nat.succ_pos n⟩) =
      (sfCbcFiniteEvaluationIso X d N n).hom ≫
        (sfCbcModelDerived X A).functor.map (sfCbcFiniteUnderlyingHom j d M N n) := by
  sorry

/-- The geometric localization functor, retaining the underlying schemes and maps.
Source: Stacks Tag 098K (blueprint: lem-sf-cbc-extension-zero-completion). -/
abbrev sfCbcOpenLocalization {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j] :
    U.ProEt ⥤ X.ProEt :=
  MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)

/-- A fixed-scalar section in the canonical associated module sheaf.
Source: Stacks Tag 00YV (blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcRealizationSection (T : Scheme.{t}) (B : Type t) [CommRing B]
    (F : Sheaf (ProEt.topology T) (ModuleCat.{t + 1} (ULift.{t + 1, t} B)))
    (V : T.ProEt) (m : F.obj.obj (op V)) :
    ((etaleOriginRealization T (ULift.{t + 1, t} B)).obj F).val.obj (op V) :=
  ((PresheafOfModules.sheafificationAdjunction
    (etaleOriginScalars T (ULift.{t + 1, t} B))).unit.app
      ((ProEtale.finiteCoefficientModulePresheaf T.ProEt
        (ULift.{t + 1, t} B)).obj F.obj)).app (op V) m

/-- Realization identifies the fixed-coefficient extension with the localized
module extension, with the identity on every extension generator. The HEq only
transports the identical underlying scheme between its two displayed structure maps.
Source: Stacks Tags 03DI and 00YV; Step 7 of the node.
Proof: on a factorization V through U, the Kan-extension unit inserts the section
in its summand. The module extension inserts the same section by DirectSum.lof.
The canonical constant scalar map identifies their scalar actions. Sheafify these
maps; the inverse uses the same summands. Local generation proves the inverse
identities and uniqueness. This is the identity restriction-square conjugate,
not a choice of an unnormalized natural isomorphism.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcRealizationExtensionIso_existsUnique {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (B : Type t) [CommRing B] [Finite B] :
    ∃! e : ProEtale.openImmersionLowerShriek
        (ModuleCat.{t + 1} (ULift.{t + 1, t} B)) j ⋙
          etaleOriginRealization X (ULift.{t + 1, t} B) ≅
      etaleOriginRealization U (ULift.{t + 1, t} B) ⋙ sfCbcOpenExtension j B,
      ∀ (F : Sheaf (ProEt.topology U) (ModuleCat.{t + 1} (ULift.{t + 1, t} B)))
        (V : X.ProEt) (a : V ⟶ cbcOpenObject j inferInstance)
        (m : F.obj.obj (op ((cbcSliceFunctor X (cbcOpenObject j inferInstance)).obj
          (Over.mk a)))),
        HEq
          ((e.hom.app F).val.app
            (op ((sfCbcOpenLocalization j).obj
              ((cbcSliceFunctor X (cbcOpenObject j inferInstance)).obj (Over.mk a))))
            (sfCbcRealizationSection X B
              ((ProEtale.openImmersionLowerShriek
                (ModuleCat.{t + 1} (ULift.{t + 1, t} B)) j).obj F) _
              (((ProEtale.openImmersionLowerShriekAdjunction
                (ModuleCat.{t + 1} (ULift.{t + 1, t} B)) j).unit.app F).hom.app
                  (op ((cbcSliceFunctor X (cbcOpenObject j inferInstance)).obj
                    (Over.mk a))) m)))
          (sfCbcExtensionSection j B
            ((etaleOriginRealization U (ULift.{t + 1, t} B)).obj F) V a
              (sfCbcRealizationSection U B F _ m)) := by
  sorry

/-- The generator-normalized realization/extension isomorphism.
Source: Stacks Tag 03DI (blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcRealizationExtensionIso {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (B : Type t) [CommRing B] [Finite B] :=
  (sfCbcRealizationExtensionIso_existsUnique j B).exists.choose

/-- The canonical nu/j! comparison with constant-module realization. It is the
published identity-square conjugate followed by the normalized realization comparison.
Source: Stacks Tag 099R (blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcEtaleExtensionComparison {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (B : Type t) [CommRing B] [Finite B] :
    (Functor.mapDerivedCategory
      (Etale.openImmersionLowerShriek (ModuleCat.{t + 1} (ULift.{t + 1, t} B)) j)) ⋙
        etaleOriginComparison X (ULift.{t + 1, t} B) ≅
    etaleOriginComparison U (ULift.{t + 1, t} B) ⋙ sfCbcDerivedExtension j B :=
  (Functor.mapDerivedCategoryCompIso
    (Etale.openImmersionLowerShriek (ModuleCat.{t + 1} (ULift.{t + 1, t} B)) j)
    (ProEtale.comparisonUpperStar (ModuleCat.{t + 1} (ULift.{t + 1, t} B)) X ⋙
      etaleOriginRealization X (ULift.{t + 1, t} B))).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (isoWhiskerRight
          (ProEtale.openImmersionLowerShriekComparisonUpperStarIso
            (ModuleCat.{t + 1} (ULift.{t + 1, t} B)) j)
          (etaleOriginRealization X (ULift.{t + 1, t} B)) ≪≫
        isoWhiskerLeft (ProEtale.comparisonUpperStar
          (ModuleCat.{t + 1} (ULift.{t + 1, t} B)) U)
          (sfCbcRealizationExtensionIso j B)) ≪≫
    Functor.mapDerivedCategoryNatIso
      (Functor.associator
        (ProEtale.comparisonUpperStar (ModuleCat.{t + 1} (ULift.{t + 1, t} B)) U)
        (etaleOriginRealization U (ULift.{t + 1, t} B)) (sfCbcOpenExtension j B)).symm ≪≫
    Functor.mapDerivedCategoryCompIso
      (ProEtale.comparisonUpperStar (ModuleCat.{t + 1} (ULift.{t + 1, t} B)) U ⋙
        etaleOriginRealization U (ULift.{t + 1, t} B)) (sfCbcOpenExtension j B)

/-- Exact etale extension retains bounded-below antecedents.
Source: Stacks Tag 03DI; Step 7 of the node.
Proof: the exact functor acts termwise, so cohomology in every degree is the
extension of the input cohomology. A lower vanishing bound is therefore preserved.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcEtaleExtension_boundedBelow {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (B : Type t) [CommRing B]
    (L : DerivedCategory.Plus
      (Sheaf U.smallEtaleTopology (ModuleCat.{t + 1} (ULift.{t + 1, t} B)))) :
    DerivedCategory.TStructure.t.plus
      ((Etale.openImmersionLowerShriek
        (ModuleCat.{t + 1} (ULift.{t + 1, t} B)) j).mapDerivedCategory.obj L.obj) := by
  sorry

/-- The transported etale antecedent is the actual termwise j! of the input.
Source: Stacks Tag 03DI (blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcEtaleExtensionPlus {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    (B : Type t) [CommRing B]
    (L : DerivedCategory.Plus
      (Sheaf U.smallEtaleTopology (ModuleCat.{t + 1} (ULift.{t + 1, t} B)))) :
    DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{t + 1} (ULift.{t + 1, t} B))) :=
  ⟨(Etale.openImmersionLowerShriek
    (ModuleCat.{t + 1} (ULift.{t + 1, t} B)) j).mapDerivedCategory.obj L.obj,
    sfCbcEtaleExtension_boundedBelow j B L⟩

/-- Transport the specified witness isomorphism, retaining the actual antecedent
j! L. The composite is nu_X^* j! L -> J nu_U^* L -> J(K tensor P_n)
-> (Jc K) tensor P_n. The witness is supplied as its two components, without
introducing another definition of etale origin.
Source: Stacks Tags 03DI and 099R; Step 7 of the node
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcTransportEtaleWitnessIso {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    [∀ n : ℕ, Finite (A ⧸ d.ideal ^ (n + 1))]
    {K : proEtaleDerivedCategory U A} (M : AdicKFlatModel U A K)
    (N : AdicKFlatModel X A ((sfCbcCompletedExtension j d).obj K)) (n : ℕ)
    (L : DerivedCategory.Plus (Sheaf U.smallEtaleTopology
      (ModuleCat.{t + 1} (ULift.{t + 1, t} (A ⧸ d.ideal ^ (n + 1))))))
    (α : (etaleOriginComparison U (ULift.{t + 1, t} (A ⧸ d.ideal ^ (n + 1)))).obj
      L.obj ≅ adicReduction U d M ⟨n + 1, Nat.succ_pos n⟩) :
    (etaleOriginComparison X (ULift.{t + 1, t} (A ⧸ d.ideal ^ (n + 1)))).obj
      (sfCbcEtaleExtensionPlus j (A ⧸ d.ideal ^ (n + 1)) L).obj ≅
        adicReduction X d N ⟨n + 1, Nat.succ_pos n⟩ :=
  (sfCbcEtaleExtensionComparison j (A ⧸ d.ideal ^ (n + 1))).app L.obj ≪≫
    (sfCbcDerivedExtension j (A ⧸ d.ideal ^ (n + 1))).mapIso α ≪≫
      (sfCbcFiniteCompletedIso j d M N n).symm

/-- Strict reduction of completed extension by zero: the unit normalization,
completeness of the output, and the specified natural derived-limit presentation.
Source: blueprint fix-lem-exchanges, integral open factor; Stacks Tags 099M and 0941.
Proof:
1. Extend a flat-term K-flat model termwise using the exact localized-site extension.
The tensor projection formula proves flatness and K-flatness, as in
sfCbcExtensionModel_existsUnique.
2. Quotient-natural tensor comparison is the strict tower isomorphism
sfCbcTensorComparison, fixed by the ordinary quotient-unit formula and universal counits.
3. Finite reduction of completion identifies each reduced unit with the inverse
of the adjoint of the corresponding limit projection; cones are acyclic levelwise,
so sfCbcReducedCompletionUnit_isIso applies in the derived tower category.
4. The definition of q cancels the reduced unit and gives the displayed equality.
5. Completion is the reflector of lem-sp-completed-pullback-adjunction, so its
output is complete. Apply functorial Rlim to the tensor comparison to obtain exactly
sfCbcCompletedExtensionPresentation. This never commutes ordinary extension with Rlim.
6. A retained witness (L, alpha) is sent by sfCbcTransportEtaleWitnessIso to
(j! L, the specified comparison followed by J alpha and the inverse finite map).
Exactness preserves the lower cohomological bound, so this is a bounded-below
witness with exactly the prescribed antecedent, for each n independently.
7. Every constituent is a natural transformation or a natural isomorphism before
Rlim. Thus all conclusions respect input maps and every quotient transition,
including the identity open, empty open, and zero complex.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcExtensionZeroCompletion {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    [∀ n : ℕ, Finite (A ⧸ d.ideal ^ (n + 1))] :
    IsIso (sfCbcReducedCompletionUnit j d) ∧
    (∀ K : proEtaleDerivedCategory U A,
      (sfCbcReduction X d).map
          ((sfCbcCompletionUnit X d).app ((sfCbcDerivedExtension j A).obj K)) ≫
        (sfCbcCompletedReductionIso j d).hom.app K =
          (sfCbcTensorComparison j d).hom.app K) ∧
    (∀ K : proEtaleDerivedCategory U A,
      sfCbcIsComplete X d ((sfCbcCompletedExtension j d).obj K)) ∧
    (∀ (K : proEtaleDerivedCategory U A) (M : AdicKFlatModel U A K)
      (N : AdicKFlatModel X A ((sfCbcCompletedExtension j d).obj K)) (n : ℕ),
      IsIso (sfCbcFiniteCompletedHom j d M N n) ∧
        ∀ (L : DerivedCategory.Plus (Sheaf U.smallEtaleTopology
          (ModuleCat.{t + 1} (ULift.{t + 1, t} (A ⧸ d.ideal ^ (n + 1))))))
          (α : (etaleOriginComparison U
            (ULift.{t + 1, t} (A ⧸ d.ideal ^ (n + 1)))).obj L.obj ≅
              adicReduction U d M ⟨n + 1, Nat.succ_pos n⟩),
          Nonempty ((etaleOriginComparison X
            (ULift.{t + 1, t} (A ⧸ d.ideal ^ (n + 1)))).obj
              (sfCbcEtaleExtensionPlus j (A ⧸ d.ideal ^ (n + 1)) L).obj ≅
                adicReduction X d N ⟨n + 1, Nat.succ_pos n⟩)) := by
  sorry

end AlgebraicGeometry.Scheme
