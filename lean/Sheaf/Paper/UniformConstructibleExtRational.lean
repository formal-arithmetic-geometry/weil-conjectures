/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module
public import Sheaf.Paper.UniformConstructibleExtTorsion
public import Sheaf.Paper.FiniteCoefficientDescentTwoColimit
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.CoefficientHeartCommonStratification
public import Sheaf.Paper.StratifiedLattice
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Sheaf.Paper.UniformConstructibleExtIntegral
import Sheaf.Paper.ConstructibleExtContinuity
import Sheaf.Paper.CoefficientHeartFiltration
import Sheaf.Paper.PadicIntegersInvertEll
import Sheaf.Paper.CartesianCoefficientsFiniteFree
import WeilConjectures.Algebra.Homology.FilteredColimitsTensor
import Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf
import Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import Sheaf.SixFunctors.ScalarSixPullback

/-!
# Uniform Ext vanishing with rational coefficients

Source: blueprint main-20261015, sec-six-functors-basics,
sk-lem-uniform-constructible-ext/sk-lem-uniform-constructible-ext-rational.md and proof,
with the refined source cutoff recorded in the DAG
(blueprint: det-uniform-constructible-ext-rational).

The finite coefficient model, its adapted ordered stratification, and the integral
lattices are fixed before any target. A global integral lattice gives the original
source cutoff, without identifying it with the maximum of the refined cutoffs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The actual condensed inclusion of the recorded valuation ring in its finite field.
Source: blueprint rational Ext proof, coefficients E, and sk-lem-stratified-lattice
(blueprint: det-uniform-constructible-ext-rational). -/
def rationalExtIntegralInclusion (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    Profinite.continuousMapRingObj.{u} (Padic.coefficientExtensionIntegers ℓ E) ⟶
      Profinite.continuousMapRingObj.{u} E :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMap
        (Padic.coefficientExtensionIntegers ℓ E).subtype continuous_subtype_val)

/-- The coefficient inclusion is a morphism of ring objects because it is the
underlying morphism of a condensed ring map. Source: blueprint rational Ext proof,
coefficients E (blueprint: det-uniform-constructible-ext-rational). -/
instance rationalExtIntegralInclusion_isMonHom (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    IsMonHom (rationalExtIntegralInclusion.{u} ℓ E) :=
  inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMap
        (Padic.coefficientExtensionIntegers ℓ E).subtype continuous_subtype_val)))

/-- An integral lattice triple, bundled to keep the stratification interface small.
The monomorphism and rationalization refer to the same integral inclusion.
Source: blueprint rational Ext proof, coefficients E; sk-lem-stratified-lattice
(blueprint: det-uniform-constructible-ext-rational). -/
structure RationalExtIntegralLattice {T : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}} [MonObj A] [MonObj B]
    [IsCommMonObj A] (α : A ⟶ B) [IsMonHom α]
    (LT : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) B) where
  /-- The integral module; A is the pulled O_E in both uses below. -/
  module_ : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) A
  locallyFree : CondensedRing.LocallyFree A module_
  inclusion : module_ ⟶ (Mod.comap α).obj LT
  mono_inclusion : Mono inclusion
  isIso_adjoint : IsIso (((Mod.extendRestrictAdjunction α).homEquiv
    module_ LT).symm inclusion)

/-- Refined source stratum data and its cohomological cutoffs. Source: blueprint
`det-uniform-constructible-ext-rational` (blueprint: det-uniform-constructible-ext-rational). -/
structure RationalUniformExtStrata (ℓ : ℕ) [Fact ℓ.Prime] (X S : Scheme.{u})
    (a : S ⟶ X) where
  stratification : X.FiniteLocallyClosedStratification
  /-- Empty strata are discarded, including for the empty-source convention. -/
  stratum_nonempty : ∀ r, (stratification.stratum r).Nonempty
  /-- Which strata lie in the locally closed source. -/
  sourceStratum : Fin stratification.n → Prop
  source_subset : ∀ r, sourceStratum r →
    stratification.stratum r ⊆ Set.range a
  complement_subset : ∀ r, ¬ sourceStratum r →
    stratification.stratum r ⊆ (Set.range a)ᶜ
  /-- The chosen order has open successive unions. -/
  successive_unions_open : ∀ m : Fin (stratification.n + 1),
    IsOpen (⋃ r : {r : Fin stratification.n // (r : ℕ) < (m : ℕ)},
      stratification.stratum r.1)
  closureScheme : Fin stratification.n → Scheme.{u}
  complement : Fin stratification.n → Scheme.{u}
  openFactor : ∀ r, stratification.domain r ⟶ closureScheme r
  closedFactor : ∀ r, closureScheme r ⟶ X
  complementMap : ∀ r, complement r ⟶ X
  openFactor_isOpen : ∀ r, IsOpenImmersion (openFactor r)
  closedFactor_isClosed : ∀ r, IsClosedImmersion (closedFactor r)
  complement_isOpen : ∀ r, IsOpenImmersion (complementMap r)
  complement_qc : ∀ r, QuasiCompact (complementMap r)
  complement_qs : ∀ r, QuasiSeparated (complementMap r)
  stratum_compact : ∀ r, CompactSpace (stratification.domain r)
  stratum_qsep : ∀ r, QuasiSeparatedSpace (stratification.domain r)
  factorization : ∀ r, openFactor r ≫ closedFactor r = stratification.immersion r
  hclosure : ∀ r, Set.range (closedFactor r) = closure (stratification.stratum r)
  hcomplement : ∀ r, Set.range (closedFactor r) = (Set.range (complementMap r))ᶜ
  cutoff : Fin stratification.n → WithTop ℕ
  cutoff_eq : ∀ r, cutoff r =
    @relativeCohomologicalDimension ℓ (Fact.out : Nat.Prime ℓ) _ _
        (complementMap r) (complement_qc r) (complement_qs r) +
      @cohomologicalDimension ℓ (Fact.out : Nat.Prime ℓ) (stratification.domain r)
        (stratum_compact r) (stratum_qsep r) + 2

/-- Uniform rational Ext vanishing, with a fixed finite model and source lattice partition.
Source: blueprint main-20261015, rational stratum bound, statement and proof, with the
source-cutoff correction recorded in the DAG
(blueprint: det-uniform-constructible-ext-rational).

Proof plan (the ten steps of the DAG node):
1. Finite type over k makes the schemes Noetherian. Open/closed extension by zero
restricts to the original lisse module on its source and to zero on its complement,
so it is constructible, as are all the finite-field models used below.
2. Over E choose a finite lattice partition and an ordered adapted refinement on X.
The coefficient-heart filtration expresses a_!L as extensions of its source-stratum
pieces. Prepare the target in the same way, without changing the source partition.
With a global source lattice omit the source filtration.
3. Flat localization O_E -> E and scalar/lower-shriek comparison identify the Ext
of two pieces with derived Hom over O_E into the localized integral target.
4. Tensor the coefficient telescope with that target. Tensor preserves its filtered
colimit, giving localization as colim of multiplication by ell on the integral target.
5. Integral-source Ext continuity passes through this telescope. The integral stratum
bound kills every term above cd_ell(j_k) + cd_ell(S_k) + 2.
6. Covariant Ext exactness inducts over the target filtration, then contravariant
exactness over the source filtration. The latter uses the maximum of the source
cutoffs. With a global source lattice the original cutoff c_a suffices.
7. Over Qbar descend L once to a finite E0, fixing its lattice partition and cutoff.
Descend each target to a common finite extension; the two-colimit theorem computes
shifted Hom as a colimit over further finite extensions.
8. The canonical restriction/lower-star and restriction/open-shriek isomorphisms
identify the restricted target with lower shriek of its restriction of scalars.
9. Restriction along a finite field extension preserves lissity: on finite free local
models multiply ranks by the extension degree, using the cartesian comparison.
10. Scalar adjunction identifies every Hom-colimit term with Ext over E0 against a
lisse target. The fixed E0 bound kills each term and hence the colimit. The same
argument keeps c_a when the fixed model has a global integral lattice. Empty source
has cutoff zero; an infinite cutoff gives an empty asserted degree range. -/
theorem uniformConstructibleExtRational
    (k : Type u) [Field k] (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] [CharP k p]
    (hpℓ : p ≠ ℓ)
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (S Z U : Scheme.{u}) (u₀ : S ⟶ Z) (i₀ : Z ⟶ X) (j₀ : U ⟶ X)
    [IsOpenImmersion u₀] [IsClosedImmersion i₀] [IsOpenImmersion j₀]
    [CompactSpace S] [QuasiSeparatedSpace S] [QuasiCompact j₀]
    (hij : Set.range i₀ = (Set.range j₀)ᶜ)
    (L : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj Λ) S))
    (hL : IsLisseCoefficientModule (coefficientHeartRingObj Λ) L) :
    ∃ (E₀ : PadicAlgCl.FiniteIntermediateField ℓ)
      (f : Profinite.continuousMapRingSheaf.{u} E₀ ⟶ Λ),
      ((∃ h : Profinite.continuousMapRingSheaf.{u} E₀ = Λ, f = eqToHom h) ∨
        ∃ h : Profinite.padicAlgClCondensedRing.{u} ℓ = Λ,
          f = Profinite.padicSubfieldCondensedRingToPadicAlgCl ℓ E₀ ≫ eqToHom h) ∧
      ∃ Lmodel : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj E₀) S),
      IsLisseCoefficientModule (Profinite.continuousMapRingObj E₀) Lmodel ∧
      Nonempty ((Mod.extendScalars ((upperStarFromPoint S).map
        ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map f))).obj Lmodel ≅ L) ∧
      ∃ (W : RationalUniformExtStrata ℓ X S (u₀ ≫ i₀)) (d : WithTop ℕ),
      (∀ r : Fin W.stratification.n,
        IsLisseCoefficientModule (Profinite.continuousMapRingObj E₀)
          ((CondensedRing.upperStar (Profinite.continuousMapRingObj E₀)
            (W.stratification.immersion r)).obj
            ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E₀) i₀).obj
              ((CondensedRing.openImmersionLowerShriek
                (Profinite.continuousMapRingObj E₀) u₀).obj Lmodel)))) ∧
      (∀ r : Fin W.stratification.n, W.sourceStratum r →
        Nonempty (RationalExtIntegralLattice
          ((upperStarFromPoint (W.stratification.domain r)).map
            (rationalExtIntegralInclusion ℓ E₀))
          ((CondensedRing.upperStar (Profinite.continuousMapRingObj E₀)
            (W.stratification.immersion r)).obj
            ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E₀) i₀).obj
              ((CondensedRing.openImmersionLowerShriek
                (Profinite.continuousMapRingObj E₀) u₀).obj Lmodel))))) ∧
      d = max 0 (sSup (Set.range (fun r :
        {r : Fin W.stratification.n //
          W.stratification.stratum r ⊆ Set.range (u₀ ≫ i₀)} => W.cutoff r))) ∧
      IsConstantModelConstructible (coefficientHeartRingObj Λ) X
        ((CondensedRing.lowerStar (coefficientHeartRingObj Λ) i₀).obj
          ((CondensedRing.openImmersionLowerShriek (coefficientHeartRingObj Λ) u₀).obj L)) ∧
      (∀ r : Fin W.stratification.n, W.sourceStratum r →
        IsLisseCoefficientModule (coefficientHeartRingObj Λ)
          ((CondensedRing.upperStar (coefficientHeartRingObj Λ)
            (W.stratification.immersion r)).obj
            ((CondensedRing.lowerStar (coefficientHeartRingObj Λ) i₀).obj
              ((CondensedRing.openImmersionLowerShriek (coefficientHeartRingObj Λ) u₀).obj L)))) ∧
      (∀ (T B V : Scheme.{u}) (v : T ⟶ B) (kb : B ⟶ X) (j : V ⟶ X)
      [IsOpenImmersion v] [IsClosedImmersion kb] [IsOpenImmersion j]
      [QuasiCompact j] [QuasiSeparated j]
      (hjb : Set.range kb = (Set.range j)ᶜ)
      (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (coefficientHeartRingObj Λ) T))
      (hM : IsLisseCoefficientModule (coefficientHeartRingObj Λ) M)
      (q : ℕ), (q : WithTop ℕ) > d →
      Subsingleton (Abelian.Ext
        ((CondensedRing.lowerStar (coefficientHeartRingObj Λ) i₀).obj
          ((CondensedRing.openImmersionLowerShriek (coefficientHeartRingObj Λ) u₀).obj L))
        ((CondensedRing.lowerStar (coefficientHeartRingObj Λ) kb).obj
          ((CondensedRing.openImmersionLowerShriek (coefficientHeartRingObj Λ) v).obj M)) q)) ∧
      (Nonempty (RationalExtIntegralLattice
        ((upperStarFromPoint S).map (rationalExtIntegralInclusion ℓ E₀)) Lmodel) →
        ∀ (T B V : Scheme.{u}) (v : T ⟶ B) (kb : B ⟶ X) (j : V ⟶ X)
          [IsOpenImmersion v] [IsClosedImmersion kb] [IsOpenImmersion j]
          [QuasiCompact j] [QuasiSeparated j]
          (hjb : Set.range kb = (Set.range j)ᶜ)
          (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
            (condensedRingObj (coefficientHeartRingObj Λ) T))
          (hM : IsLisseCoefficientModule (coefficientHeartRingObj Λ) M)
          (q : ℕ),
          (q : WithTop ℕ) >
            (@relativeCohomologicalDimension ℓ (Fact.out : Nat.Prime ℓ) _ _
              j₀ inferInstance inferInstance +
              (@cohomologicalDimension ℓ (Fact.out : Nat.Prime ℓ) S
                inferInstance inferInstance + 2)) →
          Subsingleton (Abelian.Ext
            ((CondensedRing.lowerStar (coefficientHeartRingObj Λ) i₀).obj
              ((CondensedRing.openImmersionLowerShriek
                (coefficientHeartRingObj Λ) u₀).obj L))
            ((CondensedRing.lowerStar (coefficientHeartRingObj Λ) kb).obj
              ((CondensedRing.openImmersionLowerShriek
                (coefficientHeartRingObj Λ) v).obj M)) q)) := by
  sorry
end AlgebraicGeometry.ProEtale
