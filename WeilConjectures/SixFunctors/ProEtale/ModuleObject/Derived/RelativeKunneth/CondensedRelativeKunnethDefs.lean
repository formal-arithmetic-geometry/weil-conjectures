/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkThmSfCompComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportCompositionData
public import WeilConjectures.ZetaWeil.PodCtfAdjunctionData.PodCtfAdjunctions
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.AlgebraicGeometry.LocallyConstantPerfectComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CtfLocallyClosedPerfectGeneration
public import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetPropSfCbc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixFiniteGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixNonfiniteGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixPerfectExtension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientProjectionSquare
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.QlbarDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteScalarProjectionCase
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarMateProjection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolution
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixCtf
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ScalarOpenCompositorCoherence
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OperationComparisons.CondensedOperationComparisons

public import Mathlib.Tactic.IrreducibleDef

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackCoherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperProductTranspose
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportProjectionFormula
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProjectionAdjunctionNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportComposition
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Relative Künneth for ordinary condensed coefficients

Source: latest blueprint, sec-six-functors/sk-thm-sf-kunneth-relative/_section.md,
the six-arrow comparison and its coherence and closed-product paragraphs
(blueprint: sk-thm-sf-kunneth-relative).

The forward product arrow is the reverse of the displayed word: symmetry, projection,
symmetry, exchange, projection, composition. Its inverse characterizes the relative
Künneth comparison uniquely, with no choice of an unspecified endpoint isomorphism.

## Main definitions

* `RelativeKunneth.forward`: the specified reverse six-factor word.
* `RelativeKunneth.IsoFamily`: its uniquely normalized inverse isomorphisms.
* `RelativeKunneth.ProductTheorem`: those isomorphisms and all coherence clauses.

(blueprint: def-sf-relative-kunneth-formula).

The theorem is assembled in `Sheaf.SixFunctors.CondensedRelativeKunneth`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.RelativeKunneth

open CompactSupportComposition

variable {k : Type u} [Field k]

/-- The standing inputs of Q76's composition theorem: the prime, the field and the admissible
coefficient. There are no comparison maps or coherence laws among these fields.
Source: sk-thm-sf-comp-composition, standing setting (blueprint: sk-thm-sf-kunneth-relative). -/
structure CanonicalCompositionData
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] where
  ell : ℕ
  prime : ell.Prime
  char_prime : (ringChar k).Prime
  char_ne : ringChar k ≠ ell
  field_kind : Finite k ∨ IsAlgClosed k
  coefficient : @IsLocalizingAdmissibleCoefficient ell ⟨prime⟩ Λ _

namespace CanonicalCompositionData

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]

/-- The compactification comparison `sfCompComparison` of sk-thm-sf-comp-composition at these
standing inputs. Source: sk-thm-sf-comp-composition (blueprint: sk-thm-sf-kunneth-relative).
The constant is kernel-opaque; `comparison_def` identifies it with `sfCompComparison`, so
unfolding is explicit and the kernel never expands the construction inside the product proofs. -/
irreducible_def comparison (H : CanonicalCompositionData Λ k) :
    ∀ {X Y : SepFinType k} (f : X ⟶ Y) (c d : Compactification f.hom.left),
      (localizingClosureProEtale Λ X.obj.left).ι ⋙
          rightDerivedLowerShriekOfCompactification Λ c ≅
        (localizingClosureProEtale Λ X.obj.left).ι ⋙
          rightDerivedLowerShriekOfCompactification Λ d :=
  @sfCompComparison H.ell ⟨H.prime⟩ k _ ⟨H.char_prime⟩ ⟨H.char_ne⟩ Λ _ _ H.coefficient

/-- Alpha, the composition isomorphism `sfCompComposition` of sk-thm-sf-comp-composition at
these standing inputs. The constant is kernel-opaque; `comp_def` identifies it with
`sfCompComposition`.
Source: sk-thm-sf-comp-composition, clause (1) (blueprint: sk-thm-sf-kunneth-relative). -/
irreducible_def comp (H : CanonicalCompositionData Λ k) :
    ∀ {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
      (c : Compactification f.hom.left) (d : Compactification g.hom.left)
      (e : Compactification (f.hom.left ≫ g.hom.left)),
      (localizingClosureProEtale Λ X.obj.left).ι ⋙
          (rightDerivedLowerShriekOfCompactification Λ c ⋙
            rightDerivedLowerShriekOfCompactification Λ d) ≅
        (localizingClosureProEtale Λ X.obj.left).ι ⋙
          rightDerivedLowerShriekOfCompactification Λ e :=
  @sfCompComposition H.ell ⟨H.prime⟩ k _ ⟨H.char_prime⟩ ⟨H.char_ne⟩ Λ _ _ H.coefficient

/-- Pullback preservation along standing morphisms, `sfComp_pullback_preserves`.
Source: sk-thm-sf-comp-composition, clause (2) (blueprint: sk-thm-sf-kunneth-relative). -/
abbrev pullback_preserves (H : CanonicalCompositionData Λ k) :=
  @sfComp_pullback_preserves k _ ⟨H.char_prime⟩ Λ _ _

/-- Compact-support preservation of the localizing closure and of Dctf, `sfComp_preserves`,
at these standing inputs.
Source: sk-thm-sf-comp-composition, proof step 3 (blueprint: sk-thm-sf-kunneth-relative). -/
abbrev preserves (H : CanonicalCompositionData Λ k) :=
  @sfComp_preserves H.ell ⟨H.prime⟩ k _ ⟨H.char_prime⟩ ⟨H.char_ne⟩ Λ _ _ H.coefficient

end CanonicalCompositionData

variable (Λ : ScalarSixRing.{u})

/-- Pullback restricted to the ambient localizing closures, with its membership
proof supplied by the recorded Q76 theorem.
Source: sk-thm-sf-comp-composition (blueprint: sk-thm-sf-kunneth-relative). -/
def localizingPullback (H : CanonicalCompositionData Λ.X k)
    (X Y : SepFinType k) (f : X ⟶ Y) :
    (localizingClosureProEtale Λ.X Y.obj.left).FullSubcategory ⥤
      (localizingClosureProEtale Λ.X X.obj.left).FullSubcategory :=
  (localizingClosureProEtale Λ.X X.obj.left).lift
    ((localizingClosureProEtale Λ.X Y.obj.left).ι ⋙
      CompactificationReindexing.P Λ.X f.hom.left)
    (fun K ↦ (H.pullback_preserves X Y f).1 K.obj K.property)

/-- Native compactification exchange on a Cartesian realization, followed only by
Q76's normalized comparison to the requested target compactification. The first
factor is the very `squareExchange` used by `CompactificationReindexing.exchange`
on a literal pullback: proper mate followed by inverse open mate. This definition
never extracts Q76's existential exchange witness.
Source: det-def-sf-exchanges and sk-thm-sf-comp-composition, clause (2)
(blueprint: sk-thm-sf-kunneth-relative). -/
irreducible_def canonicalExchangeOnLocalizing
    (Λ : ScalarSixRing.{u}) (H : CanonicalCompositionData Λ.X k)
    {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a : X' ⟶ X} {v : Y' ⟶ Y}
    (sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left)
    (c : Compactification f.hom.left) (d : Compactification f'.hom.left) :
    (localizingClosureProEtale Λ.X X.obj.left).ι ⋙
        (CompactificationReindexing.F Λ.X c ⋙ CompactificationReindexing.P Λ.X v.hom.left) ⟶
      (localizingClosureProEtale Λ.X X.obj.left).ι ⋙
        (CompactificationReindexing.P Λ.X a.hom.left ⋙ CompactificationReindexing.F Λ.X d) :=
  Functor.whiskerLeft (localizingClosureProEtale Λ.X X.obj.left).ι
    (CompactificationReindexing.squareExchange Λ.X
      (c := c) (c' := c.ofIsPullback sq) (w := a.hom.left) (v := v.hom.left)
      { middle := pullback.fst c.g v.hom.left
        openSquare := c.isPullback_i_ofIsPullback sq
        properSquare := (c.isPullback_g_ofIsPullback sq).flip.toCommSq }) ≫
    Functor.whiskerLeft (localizingPullback Λ H X' X a)
      (H.comparison f' (c.ofIsPullback sq) d).hom

/-- The canonical alpha extracted from the recorded Q76 theorem.
Source: sk-thm-sf-comp-composition (blueprint: sk-thm-sf-kunneth-relative). -/
def canonicalComposition
    (Λ : ScalarSixRing.{u}) (H : CanonicalCompositionData Λ.X k)
    {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : Compactification f.hom.left) (d : Compactification g.hom.left)
    (e : Compactification (f.hom.left ≫ g.hom.left)) :=
  H.comp f g c d e

/-- Base change between realizations of two product squares. All maps belong to the standing
category of schemes over k, including the base map and its pullbacks.
Source: coherence (iii) (blueprint: sk-thm-sf-kunneth-relative). -/
structure BaseChange (d d' : Diagram k) where
  b : d'.B ⟶ d.B
  x : d'.X ⟶ d.X
  y : d'.Y ⟶ d.Y
  t : d'.T ⟶ d.T
  sf : IsPullback x.hom.left d'.f.hom.left d.f.hom.left b.hom.left
  sg : IsPullback y.hom.left d'.g.hom.left d.g.hom.left b.hom.left
  sp : CommSq t.hom.left d'.p.hom.left d.p.hom.left x.hom.left
  sq : CommSq t.hom.left d'.q.hom.left d.q.hom.left y.hom.left
  st : IsPullback t.hom.left (d'.q.hom.left ≫ d'.g.hom.left)
    (d.q.hom.left ≫ d.g.hom.left) b.hom.left

/-- The exterior-product identification in the base-change square, including its two
canonical pullback-composition comparisons. Source: (iii)
(blueprint: sk-thm-sf-kunneth-relative). -/
def exteriorBaseChange {d d' : Diagram k} (s : BaseChange d d')
    (K : CompactificationReindexing.D Λ.X d.X.obj.left)
    (L : CompactificationReindexing.D Λ.X d.Y.obj.left) :
    (CompactificationReindexing.P Λ.X s.t.hom.left).obj (exterior Λ d K L) ≅
      exterior Λ d' ((CompactificationReindexing.P Λ.X s.x.hom.left).obj K)
        ((CompactificationReindexing.P Λ.X s.y.hom.left).obj L) :=
  pullTensor Λ s.t.hom.left _ _ ≪≫
    tensorIso ((pullbackSquareComparison Λ.X s.sp).app K).symm
      ((pullbackSquareComparison Λ.X s.sq).app L).symm

/-- The two inverse pullback images as actual Dctf objects. The membership is the
recorded composition dependency's preservation along k-morphisms.
Source: (iii), typing of the new inputs (blueprint: sk-thm-sf-kunneth-relative). -/
def pullObject (H : CanonicalCompositionData Λ.X k)
    (X Y : SepFinType k) (f : X ⟶ Y)
    (K : ConstantModelConstructibleFiniteTor Λ.X Y.obj.left) :
    ConstantModelConstructibleFiniteTor Λ.X X.obj.left :=
  ⟨(CompactificationReindexing.P Λ.X f.hom.left).obj K.obj,
    (H.pullback_preserves X Y f).2 K.obj K.property⟩

/-- Standing field hypotheses; this structure contains no functors or arrows.
Source: sk-def-sfb-dc-setting (blueprint: sk-thm-sf-kunneth-relative). -/
structure BaseParameters (ell : ℕ) (k : Type u) [Field k] where
  char_prime : (ringChar k).Prime
  char_ne : ringChar k ≠ ell
  field_kind : Finite k ∨ IsAlgClosed k

/-- The coefficient-specific inputs to the canonical Q76 construction.
Source: sk-thm-sf-comp-composition (blueprint: sk-thm-sf-kunneth-relative). -/
def BaseParameters.coefficients {ell : ℕ} [Fact ell.Prime] (P : BaseParameters ell k)
    (Γ : ScalarSixRing.{u}) (hΓ : IsLocalizingAdmissibleCoefficient ell Γ.X) :
    CanonicalCompositionData Γ.X k :=
  ⟨ell, Fact.out, P.char_prime, P.char_ne, P.field_kind, hΓ⟩

set_option linter.defProp false in
/-- The standing field parameters supplied by the finite-field datum and its algebraic
closure.  They introduce no additional hypotheses.
Source: sk-def-sfb-dc-setting (blueprint: sk-thm-sf-kunneth-relative). -/
def finiteFieldParameters (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ)
    (hne : ringChar D.k ≠ ell) : BaseParameters ell D.k :=
  ⟨(Algebra.ringChar_eq D.k₀ D.k) ▸ CharP.char_is_prime D.k₀ (ringChar D.k₀),
    hne, Or.inr (IsAlgClosure.isAlgClosed D.k₀)⟩

end AlgebraicGeometry.ProEtale.CondensedRing.RelativeKunneth
