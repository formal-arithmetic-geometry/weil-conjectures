/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module


public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.SmoothPurity.ExceptionalInverseImage
public import WeilConjectures.ZetaWeil.PodCtfAdjunctionData.PodCtfAdjunctions
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence

import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Mathlib.Data.Finset.Max
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# The six operations on constructible finite-Tor condensed complexes

Source: latest blueprint, `sk-thm-sf-ctf-stability`; current six-coefficient
statement (blueprint: `sk-thm-sf-ctf-stability`).

This module states preservation of the six operations and the three restricted
adjunction compatibilities over a finite or algebraically closed base field. Finite
`ℓ`-cohomological dimension is not a hypothesis: the chosen localizing exceptional adjunction
receives it from `WeilConjectures.exceptionalCurrentFieldCD` (sk-lem-base-field-cd).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Opposite

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The six operations `f^*`, `Rf_*`, `Rf_!`, `f^!`, `⊗ᴸ` and `cHom` preserve
`D^b_ctf(-, Λ)` for every admissible condensed coefficient ring `Λ` and every `k`-morphism
`f : X ⟶ Y` of separated finite-type `k`-schemes over a finite or algebraically closed
field `k` (finite `cd_ℓ k` derived from `hk`, not assumed), and their adjunctions on
`D^b_ctf` are the restrictions
of `f^* ⊣ Rf_*`, of `- ⊗ᴸ K ⊣ cHom(K, -)` (right-factor convention, via the tensor symmetry)
and of `Rf_! ⊣ f^!` on the localizing closures.

Source: literature/blueprint/latest, part-six-operations/sec-six-functors/
sec-the-remaining-operations/sk-thm-sf-ctf-stability, Proposition sk-thm-sf-ctf-stability
and its four-paragraph proof (blueprint: sk-thm-sf-ctf-stability).

Proof (node sk-thm-sf-ctf-stability):
1. Since `a_Y f = a_X`, separated and locally-finite-type cancellation make `f` separated and
   locally of finite type; the source is quasi-compact and the target quasi-separated, so `f`
   is quasi-compact, hence of finite type.
2. Clauses (1), (2) of det-thm-sf-ctf-stability-direct-images: pullback and tensor preserve
   `D^b_ctf`, as does extension by zero along a locally closed immersion (flat-model and
   integral/rational local-model cases of paragraph 1).
3. Clause (3) of det-thm-sf-ctf-stability-direct-images gives ordinary and compact-support
   direct images by the proper/open compactification route; sk-prop-sf-comp-coherence
   identifies the compact-support functor with `Rp_* j_!`; clauses (2)–(4) of sk-thm-existence
   give the chosen localizing adjunction and preservation by `f^!` (finite CD from `hk`).
4. By det-thm-sf-ctf-stability-internal-hom every first argument is a finite iterated cone of
   shifts of `a_! P` with `P` locally constant perfect, and
   `cHom(a_! P, L) ≃ Ra_*(P^∨ ⊗ᴸ a^! L)`, which lies in `D^b_ctf` by Steps 2–3; the
   contravariant internal Hom is triangulated and `D^b_ctf` is closed under shifts and cones,
   so finite-cone induction gives internal-Hom preservation.
5. With the right-factor tensor convention of det-thm-sf-ctf-stability-adjunctions, all
   images lie in `D^b_ctf` by Steps 2–4; fullness identifies the Hom sets with the ambient
   ones, so the ambient natural bijections, units and counits restrict unchanged
   (def-sp-compatible-adjunction-restriction). -/
theorem condensedCtfSixFunctorStabilityCurrent
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hk : Finite k ∨ IsAlgClosed k)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    let hcd := WeilConjectures.exceptionalCurrentFieldCD ℓ k hk
    (∀ K : ConstantModelConstructibleFiniteTor Λ Y.left,
      (constantModelBoundedConstructible Λ X.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
        ((upperStar Λ f.left).leftDerivedFunctor.obj K.obj)) ∧
    (∀ K : ConstantModelConstructibleFiniteTor Λ X.left,
      (constantModelBoundedConstructible Λ Y.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
        ((lowerStar Λ f.left).rightDerivedFunctor.obj K.obj)) ∧
    (∀ K : ConstantModelConstructibleFiniteTor Λ X.left,
      (constantModelBoundedConstructible Λ Y.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
        ((rightDerivedLowerShriekOfCompactification Λ (compactificationOverField f)).obj K.obj)) ∧
    (∀ K : (localizingClosureProEtale Λ Y.left).FullSubcategory,
      (constantModelBoundedConstructible Λ Y.left ⊓
        _root_.DerivedCategory.finiteTorAmplitude _) K.obj →
      (constantModelBoundedConstructible Λ X.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
        (((sixOperationsLocalizingAdjunction Λ ℓ k hcd f hΛ).right).obj K).obj) ∧
    (∀ K L : ConstantModelConstructibleFiniteTor Λ X.left,
      (constantModelBoundedConstructible Λ X.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
        (((derivedTensor Λ X.left).obj K.obj).obj L.obj) ∧
      (constantModelBoundedConstructible Λ X.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
        (((derivedHom Λ X.left).obj (op K.obj)).obj L.obj)) ∧
    WeilConjectures.podCompatibleRestriction (derivedUpperStarLowerStarAdjunction Λ f.left)
      (constantModelBoundedConstructible Λ Y.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _).ι
      (constantModelBoundedConstructible Λ X.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _).ι ∧
    (∀ K : ConstantModelConstructibleFiniteTor Λ X.left,
      WeilConjectures.podCompatibleRestriction
        ((derivedTensorHomAdjunction Λ K.obj).ofNatIsoLeft
          (@BraidedCategory.tensorLeftIsoTensorRight _ _ _
            (_root_.DerivedCategory.braidedCategory' _) K.obj))
        (constantModelBoundedConstructible Λ X.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _).ι
        (constantModelBoundedConstructible Λ X.left ⊓
          _root_.DerivedCategory.finiteTorAmplitude _).ι) ∧
    WeilConjectures.podCompatibleRestriction
      (sixOperationsLocalizingAdjunction Λ ℓ k hcd f hΛ).adjunction
      (ObjectProperty.ιOfLE
        (sixOperationsLocalizingAdjunction Λ ℓ k hcd f hΛ).source_mem)
      (ObjectProperty.ιOfLE
        (sixOperationsLocalizingAdjunction Λ ℓ k hcd f hΛ).target_mem)
 := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
