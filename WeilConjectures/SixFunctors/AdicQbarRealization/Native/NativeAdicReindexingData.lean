/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Native.NativeAdicFiniteNormalization

/-! # Canonical native adic reindexing comparisons

Source: BS Remark 6.8.15; HRS Lemma 7.9; Stacks 07A4 and 0GMX
(blueprint: def-sf-native-adic-reindexing-data).

## Main definitions

- `RingReindex`, `modulePull`, `derivedPull`: function-normalized ordinary inverse image.
- `IntegralReindex`: balanced scalar base change and its derived representative equation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option cleanup.letToHave false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option linter.all false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

/-- Coefficient reindexing fixed on the actual finite-extension-valued functions.
Source: BS 6.8.1 and 6.8.15
(blueprint: def-sf-native-adic-reindexing-data). -/
structure RingReindex {Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y) where
  iso : (isoSectionwiseInverseImage g CommRingCat.{u + 1}).obj (ring l Y S) ≅ ring l X R
  functions : ∀ (U : X.ProEtᵒᵖ)
      (s : ((isoSectionwiseInverseImage g CommRingCat.{u + 1}).obj (ring l Y S)).obj.obj U)
      (x : U.unop.left),
    (iso.hom.hom.app U s).down.1 x = s.down.1 x

/-- The ordinary module inverse image, using the fixed function-valued coefficient map.
Source: BS 6.8.15 (blueprint: def-sf-native-adic-reindexing-data). -/
def modulePull {Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    {R : LocallyFiniteAdicRealization.Realization l X}
    {S : LocallyFiniteAdicRealization.Realization l Y} (B : RingReindex l X g R S) :=
  isoSectionwiseModuleInverseImage.{u, u} g
    (RY := (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring l Y S))
    (RX := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring l X R))
    (((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso B.iso).hom)

/-- Exactness of the recorded ordinary module inverse image, inherited from site
reindexing and transport of the action through a ring isomorphism.
Source: BS 6.8.15 (blueprint: def-sf-native-adic-reindexing-data). -/
def modulePullExact {Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    {R : LocallyFiniteAdicRealization.Realization l X}
    {S : LocallyFiniteAdicRealization.Realization l Y} (B : RingReindex l X g R S) :
    (modulePull l X g B).Additive ∧ PreservesFiniteLimits (modulePull l X g B) ∧
      PreservesFiniteColimits (modulePull l X g B) :=
  isoSectionwiseModuleInverseImage_exact.{u, u} g
    (RY := (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring l Y S))
    (RX := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring l X R))
    (((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso B.iso).hom)

/-- Additivity inherited from sectionwise reindexing.
Source: BS 6.8.15 (blueprint: def-sf-native-adic-reindexing-data). -/
instance modulePullAdditive {Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    {R : LocallyFiniteAdicRealization.Realization l X}
    {S : LocallyFiniteAdicRealization.Realization l Y} (B : RingReindex l X g R S) :
    (modulePull l X g B).Additive := (modulePullExact l X g B).1

/-- Preservation of kernels inherited from sectionwise reindexing.
Source: BS 6.8.15 (blueprint: def-sf-native-adic-reindexing-data). -/
instance modulePullLimits {Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    {R : LocallyFiniteAdicRealization.Realization l X}
    {S : LocallyFiniteAdicRealization.Realization l Y} (B : RingReindex l X g R S) :
    PreservesFiniteLimits (modulePull l X g B) := (modulePullExact l X g B).2.1

/-- Preservation of cokernels inherited from sectionwise reindexing.
Source: BS 6.8.15 (blueprint: def-sf-native-adic-reindexing-data). -/
instance modulePullColimits {Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    {R : LocallyFiniteAdicRealization.Realization l X}
    {S : LocallyFiniteAdicRealization.Realization l Y} (B : RingReindex l X g R S) :
    PreservesFiniteColimits (modulePull l X g B) := (modulePullExact l X g B).2.2

/-- The specified exact-derived inverse image, without a derived-functor choice.
Source: BS 6.8.15 (blueprint: def-sf-native-adic-reindexing-data). -/
def derivedPull {Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    {R : LocallyFiniteAdicRealization.Realization l X}
    {S : LocallyFiniteAdicRealization.Realization l Y} (B : RingReindex l X g R S) :
    DerivedCategory (modules l Y S) ⥤ DerivedCategory (modules l X R) := by
  letI := (modulePullExact l X g B).1
  letI := (modulePullExact l X g B).2.1
  letI := (modulePullExact l X g B).2.2
  exact (modulePull l X g B).mapDerivedCategory

/-- The scalar reindexing representative equation through the universal cochain
counits and exact factorizations.
Source: BS 6.8.15 (blueprint: def-sf-native-adic-reindexing-data). -/
def integralReindexRepresentative {Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    {R : LocallyFiniteAdicRealization.Realization l X}
    {S : LocallyFiniteAdicRealization.Realization l Y} (B : RingReindex l X g R S)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (balance : pbcExtend (coefficientMap l Y S E) ⋙ modulePull l X g B ≅
      podCompletedModuleInverseImage l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g ⋙
        pbcExtend (coefficientMap l X R E))
    (derived : pbcDerivedExtend (coefficientMap l Y S E) ⋙ derivedPull l X g B ≅
    podCompletedDerivedInverseImage l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g ⋙
      pbcDerivedExtend (coefficientMap l X R E)) : Prop :=
  ∀ P : CochainComplex (integralTowerModules l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y) ℤ,
    derived.hom.app (DerivedCategory.Q.obj P) ≫
      (pbcDerivedExtend (coefficientMap l X R E)).map
        ((podCompletedModuleInverseImage l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)
          g).mapDerivedCategoryFactors.hom.app P) ≫
      pbcComplexCounit (coefficientMap l X R E)
        (((podCompletedModuleInverseImage l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)
          g).mapHomologicalComplex (.up ℤ)).obj P) =
    (derivedPull l X g B).map (pbcComplexCounit (coefficientMap l Y S E) P) ≫
      (modulePull l X g B).mapDerivedCategoryFactors.hom.app
        (((pbcExtend (coefficientMap l Y S E)).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex balance (.up ℤ)).hom.app P)

/-- The pure-section normalization of integral scalar reindexing.
Source: BS 6.8.15 (blueprint: def-sf-native-adic-reindexing-data). -/
def integralReindexSections {Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    {R : LocallyFiniteAdicRealization.Realization l X}
    {S : LocallyFiniteAdicRealization.Realization l Y} (B : RingReindex l X g R S)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (balance : pbcExtend (coefficientMap l Y S E) ⋙ modulePull l X g B ≅
      podCompletedModuleInverseImage l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g ⋙
        pbcExtend (coefficientMap l X R E)) : Prop :=
  ∀ (M : integralTowerModules l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y)
      (U : X.ProEtᵒᵖ) (a : (ring l Y S).obj.obj ((proEtaleIsoPostcompose g).op.obj U))
      (x : M.val.obj ((proEtaleIsoPostcompose g).op.obj U)),
    (balance.hom.app M).val.app U
      (pbcTensorSection (coefficientMap l Y S E) M
        ((proEtaleIsoPostcompose g).op.obj U) a x) =
    pbcTensorSection (coefficientMap l X R E)
      ((podCompletedModuleInverseImage l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g).obj M)
      U (B.iso.hom.hom.app U a) x

/-- Balanced scalar base change under an arbitrary scheme isomorphism, fixed on
pure sections and then on derived representatives by the universal cochain counits.
Source: BS 6.8.14--6.8.15; HRS 7.9
(blueprint: def-sf-native-adic-reindexing-data). -/
structure IntegralReindex {Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    {R : LocallyFiniteAdicRealization.Realization l X}
    {S : LocallyFiniteAdicRealization.Realization l Y} (B : RingReindex l X g R S)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) where
  balance : pbcExtend (coefficientMap l Y S E) ⋙ modulePull l X g B ≅
    podCompletedModuleInverseImage l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g ⋙
      pbcExtend (coefficientMap l X R E)
  sections : integralReindexSections l X g B E balance
  derived : pbcDerivedExtend (coefficientMap l Y S E) ⋙ derivedPull l X g B ≅
    podCompletedDerivedInverseImage l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g ⋙
      pbcDerivedExtend (coefficientMap l X R E)
  representative : integralReindexRepresentative l X g B E balance derived

end WeilConjectures.AdicQbarRealization
