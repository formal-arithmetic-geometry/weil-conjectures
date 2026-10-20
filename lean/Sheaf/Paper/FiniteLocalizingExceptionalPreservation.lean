/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.Paper.LocalizingExceptionalAdjoint
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Paper.ProEtaleConstructibleSheaf
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

public import Sheaf.Paper.CondensedConstantConstructibility

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution
import Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.ComparisonTorInterval
import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
import Sheaf.AlgebraicGeometry.CompactifiableOverField
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
import Sheaf.AlgebraicGeometry.EtaleClosedSupportAmplitude
import Sheaf.AlgebraicGeometry.EtaleClosedSupportTorBound
import Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle
import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.EtaleProEtaleExceptionalTransport
import Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula
import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
import Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
import Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension
import Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import Sheaf.AlgebraicGeometry.SmoothTensorDuality
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.Paper.OpenTorBoundArbitraryField
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.SfAffineChartFactorizationGluing
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
import Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence
import Sheaf.Paper.FiniteProperLocalizing

/-!
# Finite-coefficient exceptional inverse image on the localizing closure

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-sf-rf-shriek-preservation, statement and proof
(blueprint: sk-prop-sf-rf-shriek-preservation).

The small categories are the inverse images of the recorded Dctf object property under
inclusion of the localizing closures. The smooth formula is stated after trivializing the
actual comparison-pulled-back Tate line on one common etale cover, independently of the input
complex. This is the local coordinate form of tensoring with that line and shifting by 2d.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Pull back the existing Dctf object property along the localizing inclusion. This changes
only its ambient category: boundedness, constant-model constructibility and the Tor test are
exactly those of `ConstantModelConstructibleFiniteTor`.
Source: blueprint sk-prop-sf-rf-shriek-preservation, first two displays
(blueprint: sk-prop-sf-rf-shriek-preservation). -/
abbrev localizingDctfProperty
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u}) :
    ObjectProperty (localizingClosureProEtale Λ T).FullSubcategory :=
  fun K ↦ (constantModelBoundedConstructible Λ T ⊓
    fun L ↦ DerivedCategory.finiteTorAmplitude _ L) K.obj

/-- The specified nonnegative pro-etale Tate line, in fixed-scalar coordinates: apply the
exact site-comparison inverse image to the recorded ordinary etale Tate twist. `ULift`
places A in the sheaf coefficient universe and changes no scalar or module.
Source: blueprint sk-prop-sf-rf-shriek-preservation, final paragraph
(blueprint: sk-prop-sf-rf-shriek-preservation). -/
def finiteShriekProEtaleTateLine (T : Scheme.{u}) (A : Type u) [CommRing A]
    (N : ℕ) (hA : (N : ULift.{u + 1} A) = 0) (d : ℕ) :
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)) :=
  (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).obj
    (finiteEtaleTateTwist T N (ULift.{u + 1} A) hA d)

/-- The finite-coefficient right adjoint preserves Dctf, its given adjunction restricts to
Dctf, and for a smooth map of dimension d it is etale locally the twisted shifted pullback.
The last clause chooses one cover trivializing the actual pro-etale Tate line, then states
the natural isomorphism in those coordinates. Tensoring with the chosen trivialization and
the tensor unitors recovers exactly `f^*(-)(d)[2d]`; conversely the stated local twist formula
can be untwisted on a common refinement. No canonical global orientation is asserted.
Source: blueprint main-20261015, sk-prop-sf-rf-shriek-preservation, entire statement
(blueprint: sk-prop-sf-rf-shriek-preservation).

Proof:
1. Work first with ordinary etale modules. Finite-type schemes over k are Noetherian and
quasi-separated; all open restrictions are quasi-compact, separated and finite type.
Nagata and thm-amb-etale-exceptional-adjoint give ordinary ambient adjoints. Exact conservative
geometric stalks and lem-weil-pbc-ringed-topoi-derived-tensor-pullback test Tor intervals and
show that every inverse image preserves them, including for the zero ring and empty scheme.
2. For a closed immersion with complementary open j, lem-kun-0f10 gives a nonnegative
relative bound e on j. The forgetful comparison gives vanishing of module R^q j_* for q>e.
General-field finite-type constructibility and lem-exc-closed-amplitude give bounded
constructibility of the closed exceptional image in [r,s+e+1]. Finite proper exactness and
adjoint uniqueness identify this with the ordinary closed right adjoint.
3. For input Tor interval [a,b], lem-sf-projection-finite-constant applies because finite A
is Noetherian and its finite modules are finitely presented. Then
lem-sf-open-tor-bound-arbitrary-field gives [a,b+e] for Rj_*j^*K. The support triangle,
lem-sf-closed-support-tor-bound, exactness of the closed direct image and its fully faithful
counit give [a,b+e+1] for the closed exceptional image.
4. thm-asd-smooth-tensor expresses the ordinary smooth right adjoint as pullback tensor a
fixed locally free rank-one line shifted by 2m. Exactness, constructible pullback, and stalkwise
freeness give cohomological and Tor intervals shifted by -2m, without assuming preservation.
5. For an affine chart fs=vpi with i closed and p an affine-space projection, the open
extension adjunction and lem-amb-etale-compact-comparisons give natural Hom bijections on
bounded-below H between s^*f^times K and i^times p^times v^*K. All compact-support composition
inputs remain bounded below by exact open extension and bounded-below injective resolutions.
Evaluate the inverse bijection at the latter representing object to construct its map to
the former. Naturality makes all its bounded-below shifted Hom tests bijective.
6. The cone vanishes: its brutal lower tails are bounded below and their telescope is the
whole complex by lem-kun-complex-colimit-hocolim. Hom from each shifted tail to the cone
vanishes, hence Hom from their sums vanishes. The telescope triangle forces the cone's
identity to vanish. Hom exactness follows from TR3 and rotations of distinguished triangles.
7. lem-sf-affine-chart-factorization-gluing supplies finitely many such charts and glues
bounded constructibility and finite Tor bounds from the closed and smooth calculations.
8. lem-sf-module-object-ordinary-coefficient-equivalence identifies internal finite discrete
coefficients, tensor tests and closures with ordinary modules, using the section-action
equivalence. lem-sf-etale-proetale-exceptional-transport transports the bounded etale origin
and ordinary right adjoint through the same compactification. The Tor-interval comparison
shows its image H_K is pro-etale Dctf and transports the ordinary counit.
9. Transpose that counit under the given localizing adjunction to H_K -> G K. Fully faithful
bounded comparisons identify its Hom tests on every shifted Dctf object with the ordinary
etale adjunction. For its cone C, the objects T with Hom(T[n],C)=0 for every n form a replete
triangulated coproduct-closed subcategory containing Dctf. They contain its localizing closure
and thus C itself, so id_C=0. This proves preservation and natural identification with G.
10. det-ctf-finite-proper-localizing gives lower-shriek preservation. Restrict the given Hom
bijections to the two full Dctf subcategories; their unchanged units and counits give the
restricted adjunction.
11. In the smooth case the ordinary tensor theorem is natural in all inputs with one fixed
rank-one line. lem-asd-finite-etale-twist-line also trivializes the actual A(d). Choose one
common etale refinement trivializing both. Pull its local formula through comparison and
step 9; compatibility of tensor and inverse images gives the displayed natural untwisted
formula in these chosen Tate coordinates. This constructs no canonical global orientation.
-/
theorem localizingExceptionalAdjoint_preserves_finiteConstructible
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (A : Type u) [CommRing A] [Finite A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A]
    (_hA : ∃ r : ℕ, ((ℓ ^ r : ℕ) : ULift.{u + 1} A) = 0)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, localizingClosureProEtale (Profinite.continuousCoefficientRingObj A) X K →
      localizingClosureProEtale (Profinite.continuousCoefficientRingObj A) Y
        ((rightDerivedLowerShriekOfCompactification
          (Profinite.continuousCoefficientRingObj A) c.obj.obj).obj K))
    (G : (localizingClosureProEtale (Profinite.continuousCoefficientRingObj A) Y).FullSubcategory
      ⥤ (localizingClosureProEtale (Profinite.continuousCoefficientRingObj A) X).FullSubcategory)
    (adj : localizingLowerShriek (Profinite.continuousCoefficientRingObj A) c.obj.obj h ⊣ G) :
    ∃ (hF : ∀ M : (localizingDctfProperty (Profinite.continuousCoefficientRingObj A)
          X).FullSubcategory,
        localizingDctfProperty (Profinite.continuousCoefficientRingObj A) Y
          ((localizingLowerShriek (Profinite.continuousCoefficientRingObj A) c.obj.obj h).obj
            M.obj))
      (hG : ∀ K : (localizingDctfProperty (Profinite.continuousCoefficientRingObj A)
          Y).FullSubcategory,
        localizingDctfProperty (Profinite.continuousCoefficientRingObj A) X (G.obj K.obj)),
      (∃ adjSmall :
        (localizingDctfProperty (Profinite.continuousCoefficientRingObj A) Y).lift
            ((localizingDctfProperty (Profinite.continuousCoefficientRingObj A) X).ι ⋙
              localizingLowerShriek (Profinite.continuousCoefficientRingObj A) c.obj.obj h) hF ⊣
          (localizingDctfProperty (Profinite.continuousCoefficientRingObj A) X).lift
            ((localizingDctfProperty (Profinite.continuousCoefficientRingObj A) Y).ι ⋙ G) hG,
        ∀ (M : (localizingDctfProperty (Profinite.continuousCoefficientRingObj A)
              X).FullSubcategory)
          (K : (localizingDctfProperty (Profinite.continuousCoefficientRingObj A)
              Y).FullSubcategory)
          (a : (localizingLowerShriek (Profinite.continuousCoefficientRingObj A)
            c.obj.obj h).obj M.obj ⟶ K.obj),
          (adjSmall.homEquiv M K (ObjectProperty.homMk a)).hom =
            adj.homEquiv M.obj K.obj a) ∧
      ∀ (d : ℕ) [SmoothOfRelativeDimension d f]
        (r : ℕ) (hAr : ((ℓ ^ r : ℕ) : ULift.{u + 1} A) = 0),
        ∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage X, ∀ i : 𝒰.I₀,
          Nonempty
            ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (𝒰.f i)).obj
                (finiteShriekProEtaleTateLine X A (ℓ ^ r) hAr d) ≅
              (constantSheaf (Scheme.ProEt.topology (𝒰.X i))
                (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj
                  (ModuleCat.of (ULift.{u + 1} A) (ULift.{u + 1} A))) ∧
          Nonempty
            ((localizingDctfProperty (Profinite.continuousCoefficientRingObj A) Y).ι ⋙
                G ⋙ (localizingClosureProEtale (Profinite.continuousCoefficientRingObj A) X).ι ⋙
                (upperStar (Profinite.continuousCoefficientRingObj A) (𝒰.f i)).mapDerivedCategory ≅
              (localizingDctfProperty (Profinite.continuousCoefficientRingObj A) Y).ι ⋙
                (localizingClosureProEtale (Profinite.continuousCoefficientRingObj A) Y).ι ⋙
                (upperStar (Profinite.continuousCoefficientRingObj A) f).mapDerivedCategory ⋙
                (upperStar (Profinite.continuousCoefficientRingObj A) (𝒰.f i)).mapDerivedCategory ⋙
                shiftFunctor _ (2 * (d : ℤ))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
