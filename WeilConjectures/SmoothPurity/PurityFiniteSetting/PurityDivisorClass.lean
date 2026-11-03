/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCohomologyHom
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SmoothPurity.PurityConventions.PurityConventions
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFrameClass
public import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeTorsorCohomology
public import WeilConjectures.CategoryTheory.Sites.WithSection.TorsorWithSection
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologySequence
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctoriality
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import WeilConjectures.RingTheory.SmoothFibreRegularLocal
import WeilConjectures.RingTheory.RegularLocalQuotientKernelParameters
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.ProperBaseChange.SmoothOverFieldRegularLocal
import Mathlib.RingTheory.Smooth.Flat
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Regular
import WeilConjectures.AlgebraicGeometry.EffectiveCartierSum
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctoriality
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFrameClass
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.NormalizedCartierForget

/-!
# The canonical Kummer class of a Cartier divisor

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
lem-pur-divisor-class (blueprint: lem-pur-divisor-class).

The relative normalization is the published torsor-extension specification, including
its specified section off the divisor. Classes are represented by Ext, then transported
by the published supported-Hom site comparison. Heterogeneous equalities identify
the identical representations without asking the kernel to renormalize the full
localization data. The singleton range in the frame clause is equal to {f} by
Set.range_const; HEq therefore also expresses that exact support-index transport.
This is the supported cohomology of
`def-pur-support-cohomology`, via `supported_cohomology_hom`. No module structure on
G_m is used. The coefficient exponent is ell^n for every positive coefficient level n.

## Main definitions and statement

* `DivisorEtaleClasses` and `DivisorEtaleNormalized` record the relative construction.
* `DivisorLocalEquations`, `DivisorAdditive`, and `DivisorChern` spell out its compatibilities.
* `divisor_class` asserts that construction and every compatibility.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe u vH vK

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

set_option allowUnsafeReducibility true in
attribute [local reducible] functorialCupHasDerived functorialCupAbelian functorialCupCategory
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors Abelian.Ext.homEquiv
  functorialCupOrdinaryCompare functorialCupCompare functorialCupForget
  functorialCupChangeSupport functorialCupPullback

/-- The etale representatives of divisor classes on T, indexed by actual Cartier
immersions. Source: blueprint lem-pur-divisor-class, global relative construction
(blueprint: lem-pur-divisor-class). -/
structure DivisorEtaleClasses (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) where
  /-- The etale class of each Cartier immersion. Source: blueprint relative construction
  (blueprint: lem-pur-divisor-class). -/
  classOf : ∀ {D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i],
    i.ker.IsInvertible → Abelian.Ext
      ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constantEtale D))
      (P.frameTwistEtale T 1) 2
  /-- The same class in the published supported-Hom interface. Source: blueprint comparison
  (blueprint: lem-pur-divisor-class). -/
  homClassOf : ∀ {D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i],
    i.ker.IsInvertible → P.FunctorialCupH false i 2 1
  /-- Exact identity of the two realizations. Source: Mathlib Ext.hom and blueprint comparison
  (blueprint: lem-pur-divisor-class). -/
  realizes : ∀ {D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible), HEq (classOf i hI).hom (homClassOf i hI)

/-- The relative torsor Kummer normalization, in the existing extension model.
In particular the divisor section, rather than an arbitrary lift of the Picard class,
is retained. Source: blueprint lem-pur-divisor-class, second sentence
(blueprint: lem-pur-divisor-class). -/
def DivisorEtaleNormalized (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (a : T ⟶ Spec (.of P.field.k)) (C : P.DivisorEtaleClasses T) : Prop :=
  ∀ {D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible),
    Etale.SupportedKummerBoundary P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates i hI (P.diagonalExponent_isUnit a) (C.classOf i hI)

/-- The actual site-comparison image of a supported etale Hom representative.
Source: blueprint lem-pur-divisor-class, coefficient map
(blueprint: lem-pur-divisor-class). -/
def divisorProEtale (P : PurityFiniteSetting.{u}) {D T : Scheme.{u}}
    (i : D ⟶ T) [IsClosedImmersion i] (c : P.FunctorialCupH false i 2 1) :
    P.FunctorialCupH true i 2 1 := P.functorialCupCompare i 2 1 c

/-- Both local descriptions of the fixed global relative class, for every etale
principal presentation of its support, with minus the frame boundary in the Yoneda
normalization of SupportedKummerBoundary. Source: blueprint lem-pur-divisor-class,
clause (a) and frame comparison (blueprint: lem-pur-divisor-class). -/
def DivisorLocalEquations (P : PurityFiniteSetting.{u}) {T D : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) (C : P.DivisorEtaleClasses T)
    (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible) : Prop :=
  ∀ (U : Scheme.{u}) (e : U ⟶ T) [Etale e] (f : Γ(U, ⊤))
  (t : U.zeroLocusSubscheme {f} ⟶ D)
  (sq : ChosenCartesianSquare t (U.zeroLocusSubschemeι {f}) i e),
  HEq (P.functorialCupPullback true i (U.zeroLocusSubschemeι {f}) e t sq
      a 2 1 (P.divisorProEtale i (C.homClassOf i hI)))
    (-(P.frameBoundary U (e ≫ a) f)) ∧
  HEq (P.functorialCupPullback true i (U.zeroLocusSubschemeι {f}) e t sq
      a 2 1 (P.divisorProEtale i (C.homClassOf i hI)))
    (-(P.frameBoundaryProduct U (e ≫ a) 1 (fun _ : Fin 1 ↦ f)))

/-- Product-ideal addition in the common union support. The quantified support
inclusions are unique because s is monic. Source: blueprint lem-pur-divisor-class,
clause (b) (blueprint: lem-pur-divisor-class). -/
def DivisorAdditive (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (C : P.DivisorEtaleClasses T) : Prop :=
  ∀ {D₁ D₂ Z : Scheme.{u}} (i₁ : D₁ ⟶ T) (i₂ : D₂ ⟶ T) (s : Z ⟶ T)
  [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion s]
  (h₁ : i₁.ker.IsInvertible) (h₂ : i₂.ker.IsInvertible)
  (_hs : s.ker = i₁.ker * i₂.ker),
  ∃ (hsum : s.ker.IsInvertible) (a₁ : D₁ ⟶ Z) (a₂ : D₂ ⟶ Z)
    (ha₁ : a₁ ≫ s = i₁) (ha₂ : a₂ ≫ s = i₂),
    P.divisorProEtale s (C.homClassOf s hsum) =
      P.functorialCupChangeSupport true s i₁ a₁ ha₁ 2 1
          (P.divisorProEtale i₁ (C.homClassOf i₁ h₁)) +
        P.functorialCupChangeSupport true s i₂ a₂ ha₂ 2 1
          (P.divisorProEtale i₂ (C.homClassOf i₂ h₂))

/-- Ordinary Kummer normalization and its equality with forgetting the supported
class, through the identical site comparison. Source: blueprint lem-pur-divisor-class,
final paragraph (blueprint: lem-pur-divisor-class). -/
def DivisorChern (P : PurityFiniteSetting.{u}) {T D : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) (C : P.DivisorEtaleClasses T)
    (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible) : Prop :=
  divisorChernSpecification
    (P.divisorOrdinaryHom T)
    (P.divisorOrdinaryRealization T)
    (Etale.supportedKummerChern P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates i hI (P.diagonalExponent_isUnit a))
    (P.functorialCupForget true i 2 1 (P.divisorProEtale i (C.homClassOf i hI)))
    (P.functorialCupOrdinaryCompare T 2 1)

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] DivisorChern DivisorLocalEquations DivisorAdditive


end WeilConjectures.PurityFiniteSetting
