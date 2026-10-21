/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.SixFunctors.EtaleLocallyClosedExtensionComparison
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedAmbient
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
public import Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.CategoryTheory.ExactDerivedAdjunctionBounds
import Sheaf.AlgebraicGeometry.ComparisonDirectImage

/-! # Closure realization of a locally closed exceptional adjoint

Source: blueprint main-20261015, smooth-purity, site-comparison proof, paragraph 2
(blueprint: lem-sf-locally-closed-closure-adjoint-realization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe c₁ c₂ v₁ v₂ d₁ d₂

namespace AlgebraicGeometry

/-- The exactness, normalized comparison and lower bounds for one of the two sites.
This bundles conclusions, rather than introducing new sheaves or new extension functors.
Source: blueprint site-comparison proof, paragraph 2; Stacks Tags 015F, 0GJ1 and 09BN
(blueprint: lem-sf-locally-closed-closure-adjoint-realization). -/
class SfClosureExtensionComparison
    {C : Type c₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{d₁} C]
    {D : Type c₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{d₂} D]
    (F E : C ⥤ D) [F.Additive] [E.Additive] (R : D ⥤ C)
    (α : F ⋙ R ≅ 𝟭 C) (β : E ⋙ R ≅ 𝟭 C) where
  [limitsF : PreservesFiniteLimits F]
  [colimitsF : PreservesFiniteColimits F]
  [limitsE : PreservesFiniteLimits E]
  [colimitsE : PreservesFiniteColimits E]
  sheafIso : F ≅ E
  normalization : Functor.isoWhiskerRight sheafIso R ≪≫ β = α
  lowerF : ∀ (K : DerivedCategory C) (a : ℤ), K.IsGE a →
    (F.mapDerivedCategory.obj K).IsGE a
  lowerE : ∀ (K : DerivedCategory C) (a : ℤ), K.IsGE a →
    (E.mapDerivedCategory.obj K).IsGE a

attribute [instance] SfClosureExtensionComparison.limitsF SfClosureExtensionComparison.colimitsF
  SfClosureExtensionComparison.limitsE SfClosureExtensionComparison.colimitsE

/-- Localization of the degreewise normalized sheaf comparison on unbounded categories.
Source: Stacks Tags 015F and 05RU
(blueprint: lem-sf-locally-closed-closure-adjoint-realization). -/
def SfClosureExtensionComparison.derivedIso
    {C : Type c₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{d₁} C]
    {D : Type c₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{d₂} D]
    (F E : C ⥤ D) [F.Additive] [E.Additive] (R : D ⥤ C)
    (α : F ⋙ R ≅ 𝟭 C) (β : E ⋙ R ≅ 𝟭 C)
    [B : SfClosureExtensionComparison F E R α β] :
    F.mapDerivedCategory ≅ E.mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso B.sheafIso

/-- The canonical closure compactification uses the scheme-theoretic image, including
its nilpotent structure, and its actual canonical factor map.
Source: Stacks Tags 01R6--01R8 and 01RG
(blueprint: lem-sf-locally-closed-closure-adjoint-realization). -/
def sfClosureCompactification {S T : Scheme.{u}} (s : S ⟶ T)
    [IsOpenImmersion s.toImage] : Compactification s where
  Z := s.image
  g := s.imageι
  i := s.toImage
  comm := (Scheme.Hom.toImage_imageι s).symm
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- Restriction of a pro-etale closed-then-open extension to its source: inverse open
unit, followed by the closed counit, with the canonical pullback composition comparison.
Source: Stacks Tags 09AA, 09BM and 09BN
(blueprint: lem-sf-locally-closed-closure-adjoint-realization). -/
def sfProEtaleClosedOpenRestrictionIso
    (A : Type (u + 1)) [CommRing A] {S V T : Scheme.{u}}
    (s : S ⟶ T) (c : S ⟶ V) (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v] (hs : c ≫ v = s) :
    (ProEtale.lowerStar (ModuleCat.{u + 1} A) c ⋙
      ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v) ⋙
      ProEtale.upperStar (ModuleCat.{u + 1} A) s ≅ 𝟭 _ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (
      Functor.isoWhiskerLeft _ (ProEtale.upperStarCongr (ModuleCat.{u + 1} A) hs.symm ≪≫
        ProEtale.upperStarComp (ModuleCat.{u + 1} A) c v) ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (asIso (ProEtale.openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) v).unit).symm _ ≪≫ Functor.leftUnitor _) ≪≫
    asIso (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c).counit

/-- Restriction of the pro-etale closure extension: inverse open unit, followed by
closed counit, using the canonical image factorization.
Source: Stacks Tags 09AA, 09BM and 09BN
(blueprint: lem-sf-locally-closed-closure-adjoint-realization). -/
def sfProEtaleClosureRestrictionIso
    (A : Type (u + 1)) [CommRing A] {S T : Scheme.{u}}
    (s : S ⟶ T) [IsOpenImmersion s.toImage] :
    (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) s.toImage ⋙
      ProEtale.lowerStar (ModuleCat.{u + 1} A) s.imageι) ⋙
      ProEtale.upperStar (ModuleCat.{u + 1} A) s ≅ 𝟭 _ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (
      Functor.isoWhiskerLeft _ (ProEtale.upperStarCongr (ModuleCat.{u + 1} A)
        (Scheme.Hom.toImage_imageι s).symm ≪≫
        ProEtale.upperStarComp (ModuleCat.{u + 1} A) s.toImage s.imageι) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (asIso (ProEtale.upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} A) s.imageι).counit) _ ≪≫ Functor.leftUnitor _) ≪≫
    (asIso (ProEtale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) s.toImage).unit).symm

/-- All geometric conclusions needed to realize the closure compactification.
The source and target structure morphisms are related by the given k-morphism.
Source: Stacks Tags 01T6, 01RG, 01W5, 01T2; blueprint finite-type dimension lemma
(blueprint: lem-sf-locally-closed-closure-adjoint-realization). -/
class SfLocallyClosedClosureGeometry
    {k : Type u} [Field k] {S V T : Scheme.{u}}
    (s : S ⟶ T) (c : S ⟶ V) (v : V ⟶ T) (aT : T ⟶ Spec (.of k)) where
  [noetherianT : IsNoetherian T]
  [noetherianS : IsNoetherian S]
  [noetherianV : IsNoetherian V]
  [noetherianClosure : IsNoetherian s.image]
  [qcS : QuasiCompact s]
  [separatedMorph : IsSeparated s]
  [finiteTypeMorph : LocallyOfFiniteType s]
  [qcC : QuasiCompact c]
  [qcV : QuasiCompact v]
  [openImage : IsOpenImmersion s.toImage]
  [qcImage : QuasiCompact s.toImage]
  [separatedV : IsSeparated (v ≫ aT)]
  [finiteTypeV : LocallyOfFiniteType (v ≫ aT)]
  [qcOverV : QuasiCompact (v ≫ aT)]
  [separatedClosure : IsSeparated (s.imageι ≫ aT)]
  [finiteTypeClosure : LocallyOfFiniteType (s.imageι ≫ aT)]
  [qcOverClosure : QuasiCompact (s.imageι ≫ aT)]
  compactComplementsV : ∀ (Z : Scheme.{u}) (i : Z ⟶ V) [IsClosedImmersion i],
    IsCompact (Set.range i)ᶜ
  compactComplementsClosure : ∀ (Z : Scheme.{u}) (i : Z ⟶ s.image) [IsClosedImmersion i],
    IsCompact (Set.range i)ᶜ
  dimensionBound : ∃ D : ℕ, topologicalKrullDim s.image ≤ (D : WithBot ℕ∞)
  imageKernel : ∀ U : T.affineOpens, s.ker.ideal U = RingHom.ker (s.app U).hom

attribute [instance] SfLocallyClosedClosureGeometry.noetherianT
  SfLocallyClosedClosureGeometry.noetherianS SfLocallyClosedClosureGeometry.noetherianV
  SfLocallyClosedClosureGeometry.noetherianClosure SfLocallyClosedClosureGeometry.qcS
  SfLocallyClosedClosureGeometry.separatedMorph SfLocallyClosedClosureGeometry.finiteTypeMorph
  SfLocallyClosedClosureGeometry.qcC SfLocallyClosedClosureGeometry.qcV
  SfLocallyClosedClosureGeometry.openImage SfLocallyClosedClosureGeometry.qcImage
  SfLocallyClosedClosureGeometry.separatedV SfLocallyClosedClosureGeometry.finiteTypeV
  SfLocallyClosedClosureGeometry.qcOverV SfLocallyClosedClosureGeometry.separatedClosure
  SfLocallyClosedClosureGeometry.finiteTypeClosure SfLocallyClosedClosureGeometry.qcOverClosure

/-- Additivity of the existing closure-defined functor, by its two actual factors.
Source: Stacks Tag 0GJ1
(blueprint: lem-sf-locally-closed-closure-adjoint-realization). -/
instance sfEtaleClosure_additive
    (A : Type (u + 1)) [CommRing A] {S T : Scheme.{u}} (s : S ⟶ T)
    [IsImmersion s] [QuasiCompact s] :
    (etaleLocallyClosedExtension (A := A) s inferInstance).Additive :=
  inferInstanceAs ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) s.toImage ⋙
    Etale.lowerStar (ModuleCat.{u + 1} A) s.imageι).Additive)

/-- Left exactness of the existing closure extension, through its actual factors.
Source: Stacks Tag 0GJ1
(blueprint: lem-sf-locally-closed-closure-adjoint-realization). -/
instance sfEtaleClosure_preservesFiniteLimits
    (A : Type (u + 1)) [CommRing A] {S T : Scheme.{u}} (s : S ⟶ T)
    [IsImmersion s] [QuasiCompact s] :
    PreservesFiniteLimits (etaleLocallyClosedExtension (A := A) s inferInstance) :=
  inferInstanceAs (PreservesFiniteLimits
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) s.toImage ⋙
      Etale.lowerStar (ModuleCat.{u + 1} A) s.imageι))

/-- Right exactness of the existing closure extension, from exact closed pushforward.
Source: Stacks Tags 0GJ1 and 015F
(blueprint: lem-sf-locally-closed-closure-adjoint-realization). -/
instance sfEtaleClosure_preservesFiniteColimits
    (A : Type (u + 1)) [CommRing A] {S T : Scheme.{u}} (s : S ⟶ T)
    [IsImmersion s] [QuasiCompact s]
    [PreservesFiniteColimits (Etale.lowerStar (ModuleCat.{u + 1} A) s.imageι)] :
    PreservesFiniteColimits (etaleLocallyClosedExtension (A := A) s inferInstance) :=
  inferInstanceAs (PreservesFiniteColimits
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) s.toImage ⋙
      Etale.lowerStar (ModuleCat.{u + 1} A) s.imageι))

/-- The two normalized comparisons on the ordinary constant-module sites. Fixed-scalar
pro-etale sheaves are the canonical realization presentation of intrinsic constant-ring
modules, through `Scheme.sfIntrinsicModuleEquivalence`, not completed coefficients.
Source: blueprint site-comparison proof, paragraph 2; Stacks Tags 0GJ1 and 09BN
(blueprint: lem-sf-locally-closed-closure-adjoint-realization). -/
class SfLocallyClosedClosureSites
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V T : Scheme.{u}} (s : S ⟶ T) [IsImmersion s] [QuasiCompact s]
    [IsOpenImmersion s.toImage] (c : S ⟶ V) (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v] (hs : c ≫ v = s) where
  [etale : SfClosureExtensionComparison
    (Etale.lowerStar (ModuleCat.{u + 1} A) c ⋙
      Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v)
    (etaleLocallyClosedExtension (A := A) s inferInstance)
    (Etale.upperStar (ModuleCat.{u + 1} A) s)
    (etaleFactorizationRestrictionIso (A := A) s c v hs)
    (etaleLocallyClosedExtensionRestrictionIso (A := A) s inferInstance)]
  [proetale : SfClosureExtensionComparison
    (ProEtale.lowerStar (ModuleCat.{u + 1} A) c ⋙
      ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v)
    (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) s.toImage ⋙
      ProEtale.lowerStar (ModuleCat.{u + 1} A) s.imageι)
    (ProEtale.upperStar (ModuleCat.{u + 1} A) s)
    (sfProEtaleClosedOpenRestrictionIso A s c v hs)
    (sfProEtaleClosureRestrictionIso A s)]
  [closedEtaleExact : PreservesFiniteColimits (Etale.lowerStar (ModuleCat.{u + 1} A) c)]
  [imageEtaleExact : PreservesFiniteColimits
    (Etale.lowerStar (ModuleCat.{u + 1} A) s.imageι)]
  [closedProEtaleExact : PreservesFiniteColimits
    (ProEtale.lowerStar (ModuleCat.{u + 1} A) c)]
  [imageProEtaleExact : PreservesFiniteColimits
    (ProEtale.lowerStar (ModuleCat.{u + 1} A) s.imageι)]

attribute [instance_reducible] SfLocallyClosedClosureSites.etale
  SfLocallyClosedClosureSites.proetale
attribute [instance] SfLocallyClosedClosureSites.etale SfLocallyClosedClosureSites.proetale

attribute [instance]
  SfLocallyClosedClosureSites.closedEtaleExact
  SfLocallyClosedClosureSites.imageEtaleExact SfLocallyClosedClosureSites.closedProEtaleExact
  SfLocallyClosedClosureSites.imageProEtaleExact

/-- `J_e = v_e^* Rc_e^!`, with `Rc_e^!` the adjoint fixed by its universal property.
Source: blueprint site-comparison proof, paragraph 2
(blueprint: lem-sf-locally-closed-closure-adjoint-realization). -/
def sfClosureEtaleJ
    (A : Type (u + 1)) [CommRing A] {S V T : Scheme.{u}}
    (c : S ⟶ V) (v : V ⟶ T)
    [(Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor.IsLeftAdjoint] :=
  (Etale.upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory ⋙
    (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor.rightAdjoint

/-- The pasted closed-support/open adjunction, transported by the canonical exact
closed-direct-image and composition identifications.
Source: blueprint site-comparison proof, paragraph 2; Stacks Tag 015F
(blueprint: lem-sf-locally-closed-closure-adjoint-realization). -/
def sfClosureEtalePastedAdjunction
    (A : Type (u + 1)) [CommRing A] {S V T : Scheme.{u}}
    (c : S ⟶ V) (v : V ⟶ T) [IsClosedImmersion c] [IsOpenImmersion v]
    [PreservesFiniteColimits (Etale.lowerStar (ModuleCat.{u + 1} A) c)]
    [(Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor.IsLeftAdjoint] :
    (Etale.lowerStar (ModuleCat.{u + 1} A) c ⋙
      Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory ⊣
      sfClosureEtaleJ A c v :=
  ((Adjunction.ofIsLeftAdjoint
    (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor).comp
      (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v))
    |>.ofNatIsoLeft
      ((Functor.isoWhiskerRight
        (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctorIsoMapDerivedCategory
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm)

/-- `J_p = v_p^* Rc_p^!`, with `Rc_p^!` the adjoint fixed by its universal property.
Source: blueprint site-comparison proof, paragraph 2
(blueprint: lem-sf-locally-closed-closure-adjoint-realization). -/
def sfClosureProEtaleJ
    (A : Type (u + 1)) [CommRing A] {S V T : Scheme.{u}}
    (c : S ⟶ V) (v : V ⟶ T)
    [(ProEtale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor.IsLeftAdjoint] :=
  (ProEtale.upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory ⋙
    (ProEtale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor.rightAdjoint

/-- The pasted closed-support/open adjunction, transported by the canonical exact
closed-direct-image and composition identifications.
Source: blueprint site-comparison proof, paragraph 2; Stacks Tag 015F
(blueprint: lem-sf-locally-closed-closure-adjoint-realization). -/
def sfClosureProEtalePastedAdjunction
    (A : Type (u + 1)) [CommRing A] {S V T : Scheme.{u}}
    (c : S ⟶ V) (v : V ⟶ T) [IsClosedImmersion c] [IsOpenImmersion v]
    [PreservesFiniteColimits (ProEtale.lowerStar (ModuleCat.{u + 1} A) c)]
    [(ProEtale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor.IsLeftAdjoint] :
    (ProEtale.lowerStar (ModuleCat.{u + 1} A) c ⋙
      ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory ⊣
      sfClosureProEtaleJ A c v :=
  ((Adjunction.ofIsLeftAdjoint
    (ProEtale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor).comp
      (ProEtale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) v).mapDerivedCategoryAdjunction)
    |>.ofNatIsoLeft
      ((Functor.isoWhiskerRight
        (ProEtale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctorIsoMapDerivedCategory
        (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm)

/-- The canonical identification of ordinary compact support at the closure with `E_e`.
Source: blueprint site-comparison proof, paragraph 2; Stacks Tag 015F
(blueprint: lem-sf-locally-closed-closure-adjoint-realization). -/
def sfClosureEtaleCompactSupportIso
    (A : Type (u + 1)) [CommRing A] {S T : Scheme.{u}}
    (s : S ⟶ T) [IsImmersion s] [QuasiCompact s] [IsOpenImmersion s.toImage]
    [PreservesFiniteColimits (Etale.lowerStar (ModuleCat.{u + 1} A) s.imageι)] :
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (sfClosureCompactification s) ≅
        (etaleLocallyClosedExtension (A := A) s inferInstance).mapDerivedCategory :=
  Functor.isoWhiskerLeft _
    (Etale.lowerStar (ModuleCat.{u + 1} A) s.imageι).rightDerivedFunctorIsoMapDerivedCategory ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

/-- Remaining adjoint and bounded-input conclusions. Both adjoints are supplied with
existence, not assumed; `adjF` is the pasted adjunction and `adjE` is the ordinary
compact-support adjunction transported by `sfClosureEtaleCompactSupportIso`.
Source: blueprint site-comparison proof, paragraph 2; Mathlib Adjunction/Mates
(blueprint: lem-sf-locally-closed-closure-adjoint-realization). -/
class SfLocallyClosedClosureAdjoints
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V T : Scheme.{u}} (s : S ⟶ T) [IsImmersion s] [QuasiCompact s]
    [IsOpenImmersion s.toImage] (c : S ⟶ V) (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v] (hs : c ≫ v = s)
    [B : SfLocallyClosedClosureSites A s c v hs] where
  [closedAdjoint : (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor.IsLeftAdjoint]
  [closedProEtaleAdjoint :
    (ProEtale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor.IsLeftAdjoint]
  [ambientAdjoint : (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
    (sfClosureCompactification s)).IsLeftAdjoint]
  boundedRestriction : ∀ M : Etale.DerivedCategoryModule A T,
    Etale.DerivedCategory.isBoundedConstructible A T M →
      Etale.DerivedCategory.isBoundedConstructible A V
        ((Etale.upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj M)
  boundedAdjoint : ∀ M : Etale.DerivedCategoryModule A T,
    Etale.DerivedCategory.isBoundedConstructible A T M →
      ∃ a : ℤ, ((sfClosureEtaleJ A c v).obj M).IsGE a
  comparisonDomain : ∀ (L : Etale.DerivedCategoryModule A S) (a : ℤ), L.IsGE a →
    ((Etale.lowerStar (ModuleCat.{u + 1} A) c).mapDerivedCategory.obj L).IsGE a ∧
    ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A)
      s.toImage).mapDerivedCategory.obj L).IsGE a

attribute [instance] SfLocallyClosedClosureAdjoints.closedAdjoint
  SfLocallyClosedClosureAdjoints.ambientAdjoint
  SfLocallyClosedClosureAdjoints.closedProEtaleAdjoint

/-- The canonical adjunction-conjugate identification `J_e ≅ s^×`.
Its direction uses `q_e.symm`; no uncharacterized natural isomorphism is chosen.
Source: Mathlib CategoryTheory/Adjunction/Mates, conjugateIsoEquiv; blueprint paragraph 2
(blueprint: lem-sf-locally-closed-closure-adjoint-realization). -/
def sfClosureEtaleAdjointIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V T : Scheme.{u}} (s : S ⟶ T) [IsImmersion s] [QuasiCompact s]
    [IsOpenImmersion s.toImage] (c : S ⟶ V) (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v] (hs : c ≫ v = s)
    [B : SfLocallyClosedClosureSites A s c v hs]
    [C : SfLocallyClosedClosureAdjoints A s c v hs] :
    sfClosureEtaleJ A c v ≅
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (sfClosureCompactification s)).rightAdjoint :=
  conjugateIsoEquiv (sfClosureEtalePastedAdjunction A c v)
    ((Adjunction.ofIsLeftAdjoint
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (sfClosureCompactification s))).ofNatIsoLeft (sfClosureEtaleCompactSupportIso A s))
    (Functor.mapDerivedCategoryNatIso B.etale.sheafIso).symm

/-- The ambient ordinary compact-support adjunction, identified with the closure functor.
Source: blueprint site-comparison proof, paragraph 2; Mathlib Adjunction.Basic
(blueprint: lem-sf-locally-closed-closure-adjoint-realization). -/
def sfClosureEtaleAmbientAdjunction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V T : Scheme.{u}} (s : S ⟶ T) [IsImmersion s] [QuasiCompact s]
    [IsOpenImmersion s.toImage] (c : S ⟶ V) (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v] (hs : c ≫ v = s)
    [B : SfLocallyClosedClosureSites A s c v hs]
    [C : SfLocallyClosedClosureAdjoints A s c v hs] :
    (etaleLocallyClosedExtension (A := A) s inferInstance).mapDerivedCategory ⊣
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (sfClosureCompactification s)).rightAdjoint :=
  (Adjunction.ofIsLeftAdjoint
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (sfClosureCompactification s))).ofNatIsoLeft (sfClosureEtaleCompactSupportIso A s)

/-- Explicit unit and counit preservation by the canonical conjugate of `q_e.symm`.
Source: blueprint site-comparison proof, paragraph 2; Mathlib Adjunction.Mates
(blueprint: lem-sf-locally-closed-closure-adjoint-realization). -/
def SfClosureEtaleConjugationCompatibility
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V T : Scheme.{u}} (s : S ⟶ T) [IsImmersion s] [QuasiCompact s]
    [IsOpenImmersion s.toImage] (c : S ⟶ V) (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v] (hs : c ≫ v = s)
    [B : SfLocallyClosedClosureSites A s c v hs]
    [C : SfLocallyClosedClosureAdjoints A s c v hs] : Prop :=
  (∀ L : Etale.DerivedCategoryModule A S,
    (sfClosureEtalePastedAdjunction A c v).unit.app L ≫
      (sfClosureEtaleJ A c v).map
        ((Functor.mapDerivedCategoryNatIso B.etale.sheafIso).hom.app L) ≫
      (sfClosureEtaleAdjointIso A s c v hs).hom.app
        ((etaleLocallyClosedExtension (A := A) s inferInstance).mapDerivedCategory.obj L) =
      (sfClosureEtaleAmbientAdjunction A s c v hs).unit.app L) ∧
  (∀ M : Etale.DerivedCategoryModule A T,
    (Functor.mapDerivedCategoryNatIso B.etale.sheafIso).hom.app
        ((sfClosureEtaleJ A c v).obj M) ≫
      (etaleLocallyClosedExtension (A := A) s inferInstance).mapDerivedCategory.map
        ((sfClosureEtaleAdjointIso A s c v hs).hom.app M) ≫
      (sfClosureEtaleAmbientAdjunction A s c v hs).counit.app M =
      (sfClosureEtalePastedAdjunction A c v).counit.app M)

/-- The same normalized pro-etale sheaf comparison in the recorded intrinsic
constant-ring module categories. The two sides use the canonical realization transport;
the comparison is transported from the specified identity-normalized comparison.
Source: Stacks Tags 00YV, 09AA and 09BN; blueprint site-comparison proof, paragraph 2
(blueprint: lem-sf-locally-closed-closure-adjoint-realization). -/
def sfClosureIntrinsicProEtaleIso
    (A : Type u) [CommRing A] [Finite A]
    {S V T : Scheme.{u}} (s : S ⟶ T) [IsImmersion s] [QuasiCompact s]
    [IsOpenImmersion s.toImage] (c : S ⟶ V) (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v] (hs : c ≫ v = s)
    [B : SfLocallyClosedClosureSites (ULift.{u + 1} A) s c v hs] :
    sfIntrinsicTransport A
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) c ⋙
        ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) v) ≅
      sfIntrinsicTransport A
        (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) s.toImage ⋙
          ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) s.imageι) :=
  sfIntrinsicTransportIso A B.proetale.sheafIso

/-- The conclusion bundle at the specified finite coefficient level. Finiteness and
all geometric, exactness and adjoint properties are conclusions, not extra assumptions.
Source: blueprint site-comparison proof, paragraph 2
(blueprint: lem-sf-locally-closed-closure-adjoint-realization). -/
class SfLocallyClosedClosureRealization
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) {S V T : Scheme.{u}} [T.Over (Spec (.of D.k))]
    (s : S ⟶ T) [IsImmersion s] (c : S ⟶ V) (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v] (hs : c ≫ v = s) where
  [finiteCoefficient : Finite (Padic.coefficientExtensionRing l E n)]
  [geometry : SfLocallyClosedClosureGeometry s c v (T ↘ Spec (.of D.k))]
  [sites : SfLocallyClosedClosureSites
    (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) s c v hs]
  [adjoints : SfLocallyClosedClosureAdjoints
    (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) s c v hs]
  conjugation : SfClosureEtaleConjugationCompatibility
    (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) s c v hs

/-- The closure compactification realizes the locally closed functor and its adjoint.

Source: blueprint main-20261015, site-comparison proof, second paragraph; component
Stacks Tags 01T6, 01RG, 01W5, 0GJ1, 09BM, 09BN, 015F, 05TC and 099R
(blueprint: lem-sf-locally-closed-closure-adjoint-realization).

Proof plan (the eleven DAG steps).
1. Finite type over a field makes S and T Noetherian; open restriction gives V Noetherian.
2. Quasi-compactness identifies the scheme-image ideal with the actual kernel; Tag 01RG
makes the canonical factor to the image a quasi-compact open immersion.
3. Closed immersions are proper and quasi-compact open immersions are finite type.
Composition gives separated finite type V and closure over k and the compactification.
4. The closure is Noetherian; its open complements are quasi-compact. Finite type over
k gives the finite dimension bound, with D=0 for the empty closure.
5. Closed direct images and open extensions are exact on both ordinary sites, so their
termwise derived functors preserve every lower cohomological bound.
6. The normalized closed/open interchange comparisons give the sheaf isomorphisms;
localization of the degreewise isomorphisms gives q_e and q_p on unbounded categories.
7. Exactness of the closed image identifies ordinary compact support with E_e; ambient
exceptional-adjoint existence applies to this same compactification and finite ring.
8. Conjugate q_e inverse under the pasted and ambient adjunctions. The mate identities
are precisely preservation of units and counits.
9. Open restriction preserves a finite constructible stratification and the cohomology
bounds of M, so v* M is bounded constructible.
10. The right adjoint to the exact termwise closed pushforward preserves every lower
bound (lem-pur-exact-derived-adjunction-bounds), hence J_e M is bounded below.
11. Exact open/closed extensions retain this lower bound; the closed maps are qcqs, so
the bounded-below direct-image comparison applies to H and to every bounded-below L.
-/
theorem locallyClosedClosureAdjointRealization
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (_hn : 1 ≤ n)
    {S V T : Scheme.{u}}
    [S.Over (Spec (.of D.k))] [T.Over (Spec (.of D.k))]
    [IsSeparated (S ↘ Spec (.of D.k))] [LocallyOfFiniteType (S ↘ Spec (.of D.k))]
    [QuasiCompact (S ↘ Spec (.of D.k))]
    [IsSeparated (T ↘ Spec (.of D.k))] [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))]
    (s : S ⟶ T) [IsImmersion s] [s.IsOver (Spec (.of D.k))]
    (c : S ⟶ V) (v : V ⟶ T) [IsClosedImmersion c] [IsOpenImmersion v]
    (hs : c ≫ v = s) :
    Nonempty (SfLocallyClosedClosureRealization D l E n s c v hs) := by
  sorry

end AlgebraicGeometry
