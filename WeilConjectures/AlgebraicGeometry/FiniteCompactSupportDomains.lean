/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude

/-! # Finite compact-support domains with current coefficient extension

Source: Stacks Project, Tags 0GL6, 0E8I, 099R and 09AF; blueprint
sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional,
Charts and Locality (blueprint: lem-sp-finite-compact-support-domains).

The constant-ring module-sheaf presentation is identified with modules over the
pulled-back discrete condensed ring by the recorded finite-discrete ordinary
coefficient equivalence. Scalar extension here is the current K-flat derived
extension, with its target-ring action, on each actual small site.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- All finite compact-support and scalar/site outputs have their required domains.
Source: Stacks 0GL6 and 0E8I; blueprint Charts and Locality of
`det-sp-reduction-exceptional` (blueprint: lem-sp-finite-compact-support-domains).

Proof:
1. Finite type over the field makes U and V Noetherian and h quasi-compact.
   The characteristic calculation using hchar makes each finite primary coefficient
   ring have invertible exponent on V, including the zero ring and empty schemes.
2. Choose a bounded flat constructible model for L. Apply the ordinary etale
   compact-support Tor-window theorem at this compactification: open extension
   preserves flatness and proper direct image supplies a uniform fibre bound.
   This gives bounded constructible finite Tor amplitude for F_A L. The same
   argument over B will apply to L_B after step 3.
3. Apply the finite-coefficient input-model theorem to L and F_A L. Its ordinary
   coefficient transport gives bounded constructibility and the uniform Tor
   interval for site pullback, actual derived scalar extension, and actual
   pro-etale scalar extension. Apply it over B with the identity map to each
   B-output to obtain its intrinsic site-pullback properties. These are universal
   degree-zero module tests and finite-stratification constructibility.
4. Apply step 2 over B to L_B, then step 3 to this output. All listed etale
   outputs and their site pullbacks are bounded, hence bounded below. Exact
   pro-etale open extension and left t-exact derived direct image supply lower
   bounds for the actual pro-etale compact-support outputs. Step 3 supplies the
   bounds for both actual pro-etale scalar outputs. Assemble the finite lists.
No flatness or finite projective dimension of B over A is used. -/
theorem finiteCompactSupportDomains_current
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    (hchar : ringChar k ≠ ℓ)
    {U V : Scheme.{u}} [U.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))]
    (h : U ⟶ V) [h.IsOver (Spec (.of k))] (c : Compactification h)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B)
    (L : Etale.DerivedCategoryModule A U)
    (hb : _root_.DerivedCategory.TStructure.t.bounded L)
    (hc : ∀ q : ℤ, IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ q).obj L))
    (ht : ∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn A U a b L) :
    (∀ (K : Etale.DerivedCategoryModule A V),
      K ∈ [(Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) c).obj L] →
      _root_.DerivedCategory.TStructure.t.bounded K ∧
      (∀ q : ℤ, IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) ∧
      (∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn A V a b K) ∧
      (∃ a : ℤ, K.IsGE a) ∧
      _root_.DerivedCategory.TStructure.t.bounded
        ((comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategory.obj K) ∧
      (∀ q : ℤ, IsConstructibleProEtaleFixedModuleSheaf V A
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategory.obj K))) ∧
      (∃ a b : ℤ, a ≤ b ∧ _root_.DerivedCategory.torAmplitudeIn
        (Sheaf (ProEt.topology V) (ModuleCat.{u + 1} A)) a b
        ((comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategory.obj K)) ∧
      (∃ a : ℤ,
        ((comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategory.obj K).IsGE a)) ∧
    (∀ P : Σ T : Scheme.{u}, Etale.DerivedCategoryModule B T,
      P ∈ [⟨U, (Sheaf.fixedCoefficientDerivedScalarExtension U.smallEtaleTopology φ).obj L⟩,
        ⟨V, (Sheaf.fixedCoefficientDerivedScalarExtension V.smallEtaleTopology φ).obj
          ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj L)⟩,
        ⟨V, (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).obj
          ((Sheaf.fixedCoefficientDerivedScalarExtension U.smallEtaleTopology φ).obj L)⟩] →
      _root_.DerivedCategory.TStructure.t.bounded P.2 ∧
      (∀ q : ℤ, IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ q).obj P.2)) ∧
      (∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn B P.1 a b P.2) ∧
      (∃ a : ℤ, P.2.IsGE a) ∧
      _root_.DerivedCategory.TStructure.t.bounded
        ((comparisonUpperStar (ModuleCat.{u + 1} B) P.1).mapDerivedCategory.obj P.2) ∧
      (∀ q : ℤ, IsConstructibleProEtaleFixedModuleSheaf P.1 B
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} B) P.1).mapDerivedCategory.obj P.2))) ∧
      (∃ a b : ℤ, a ≤ b ∧ _root_.DerivedCategory.torAmplitudeIn
        (Sheaf (ProEt.topology P.1) (ModuleCat.{u + 1} B)) a b
        ((comparisonUpperStar (ModuleCat.{u + 1} B) P.1).mapDerivedCategory.obj P.2)) ∧
      (∃ a : ℤ,
        ((comparisonUpperStar (ModuleCat.{u + 1} B) P.1).mapDerivedCategory.obj P.2).IsGE a)) ∧
    (∃ a : ℤ,
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.obj L)).IsGE a) ∧
    (∃ a : ℤ,
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} B) U).mapDerivedCategory.obj
          ((Sheaf.fixedCoefficientDerivedScalarExtension U.smallEtaleTopology φ).obj L))).IsGE a) ∧
    (∀ P : Σ T : Scheme.{u}, Etale.DerivedCategoryModule A T,
      P ∈ [⟨U, L⟩,
        ⟨V, (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj L⟩] →
      ∃ a : ℤ, ((Sheaf.fixedCoefficientDerivedScalarExtension (ProEt.topology P.1) φ).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) P.1).mapDerivedCategory.obj P.2)).IsGE a) := by
  sorry

/-- The specified compact-support comparison is invertible for every D+ input.
Source: Stacks 099R and 09AF; blueprint Charts and Locality of
`det-sp-reduction-exceptional` (blueprint: lem-sp-finite-compact-support-domains).

Proof: the proper map c.g is qcqs. Exact open extension puts j_!E in D+.
Apply the recorded invertibility theorem to the named proper counit mate at
j_!E. The second factor is the proper derived image of the canonical open
comparison isomorphism, so is invertible as well. Their composite is invertible.
The standard D+ compatibility identifies the displayed endpoints with the
restrictions of the unbounded compact-support functors in the preceding theorem.
Both arrows are the specified comparisons, with no independently chosen map. -/
theorem finiteCompactSupportDomains_current_comparison_isIso
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    (hchar : ringChar k ≠ ℓ)
    {U V : Scheme.{u}} [U.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))]
    (h : U ⟶ V) [h.IsOver (Spec (.of k))] (c : Compactification h)
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (hR : ∃ n : ℕ, ∀ x : R, (ℓ ^ n) • x = 0)
    (E : _root_.DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    IsIso
      ((fixedComparisonDirectImageMatePlus R c.g).app
          ((Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} R) c.i).mapDerivedCategoryPlus.obj E) ≫
        (lowerStar (ModuleCat.{u + 1} R) c.g).rightDerivedFunctorPlus.map
          (((Functor.mapDerivedCategoryPlusCompIso
              (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i)
              (comparisonUpperStar (ModuleCat.{u + 1} R) c.Z)).symm ≪≫
            Functor.mapDerivedCategoryPlusNatIso
              (openImmersionLowerShriekComparisonUpperStarIso
                (ModuleCat.{u + 1} R) c.i) ≪≫
            Functor.mapDerivedCategoryPlusCompIso
              (comparisonUpperStar (ModuleCat.{u + 1} R) U)
              (openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i)).hom.app E)) := by
  sorry

end AlgebraicGeometry.ProEtale
