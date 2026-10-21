/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Paper.PurTwistCoefficientRings
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Sheaf.Paper.CompletedIntegralCoefficients
public import Sheaf.Paper.DerivedCompleteIntegralDetailed
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree


public import Sheaf.Paper.PurTwistSheaves
import Sheaf.Paper.PurTwistRootLocalModels
import Sheaf.Paper.PurTwistRootTransitions
import Sheaf.Paper.PurTwistIntegralLocalModels
import Sheaf.Paper.CompletedLineDerived
import Sheaf.Paper.PurTwistIntegralBasis
import Sheaf.Paper.PurTwistCoefficientComparison
import Sheaf.Paper.ConstructibleSingleSupport
import Sheaf.Paper.FiniteLocallyFreeLineModels

/-! # Local freeness and derived completeness of the Tate line

Source: coefficient-twist blueprint, order 1505
(blueprint: lem-pur-twist-sheaf-locally-free).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings TensorProduct
namespace AlgebraicGeometry.Scheme

private theorem rank_one_of_cover
    {S : Scheme.{u}} {R : Sheaf (ProEt.topology S) RingCat.{u + 1}}
    (M : SheafOfModules.{u + 1} R)
    (hM : ∃ (I : Type (u + 1)) (U : I → S.ProEt)
      (f : ∀ i, U i ⟶ ProEt.mk (𝟙 S)),
      Presieve.ofArrows U f ∈ (ProEt.precoverage S).coverings _ ∧
      ∀ i, Nonempty (M.over (U i) ≅ (SheafOfModules.unit R).over (U i))) :
    M.IsFiniteLocallyFreeOfRank 1 := by
  obtain ⟨I, U, f, hc, ht⟩ := hM
  have hU : (ProEt.topology S).CoversTop U := by
    let hT : IsTerminal (ProEt.mk (𝟙 S)) := MorphismProperty.Over.mkIdTerminal _ _
    rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ _ hT]
    rw [← Sieve.ofArrows_eq_ofObjects hT U f]
    exact Precoverage.generate_mem_toGrothendieck hc
  exact (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one M).mp
    (SheafOfModules.isInvertible_of_forall_over_unit (M := M) U hU ht)

/-- All four properties of the concrete Tate lines, including the empty-scheme case.
Source: Stacks Project, Tag 03PK and Lemma 03RV; coefficient-twist blueprint, order 1505
(blueprint: lem-pur-twist-sheaf-locally-free).
Proof:
1. On affine opens the finite root scheme is etale, by
   lem-sbc-root-split-away-cover-etale. Use lem-asd-finite-etale-twist-line and the
   representable calculation for def-weil-pbc-site-comparison-morphism to transfer its
   trivializations to the pro-etale root sheaf. The comparison of constant finite
   coefficients in lem-sf-comparison-pullback-exact respects the scalar action.
2. Apply lem-amb-kummer-any-base on each test scheme to lift roots through the power
   transitions locally. The sheaf local-surjectivity criterion makes them epimorphisms.
3. Refine the level-one etale cover by
   lem-weil-pbc-proetale-affine-wcontractible-covering-family. On each weakly contractible
   member lift primitive roots recursively. Every lift stays primitive: its coefficient
   modulo l is a unit, hence its coefficient modulo every l-power is a unit. Constant
   sections and their equality can be checked locally by
   lem-weil-pbc-site-sheafification-sections-local and the constant-sheaf stalk theorem.
4. Take the compatible root trivializations to the inverse limit. Slice restriction
   commutes with sectionwise limits, by lem-weil-proetale-weakly-etale-localization.
   The coordinate action gives a completed coefficient line. The quotient clause of
   lem-weil-pbc-constant-completion-equivalence and the tensor-quotient formula identify
   its finite reductions with the roots sheaves.
5. The valuation-ring DVR theorem writes l as a unit times a positive uniformizer power.
   Lift a finite residue basis and use successive l-adic digit expansions and completeness
   to obtain finite generation over Z_l. Torsion freeness and
   lem-sc-dvr-fg-torsionfree-free give a finite basis.
6. Reduce that basis modulo l-powers and take limits. Uniformizer powers and l-powers are
   cofinal, so the canonical ring-sheaf tensor comparison is an isomorphism, including its
   multiplicative and unit structure. Its pure-tensor formula gives the completed action
   on the prescribed integral tensor sheaf, which is locally a line.
7. Both ordinary reductions are quotient by the same uniformizer power, hence coincide.
   Choose a finite l-power annihilating each coefficient quotient; its finite root
   trivialization is an etale trivialization of the finite Tate line. The geometric-point
   lifting and constant-stalk lemmas make its stalks finite.
8. The integral line placed in degree zero is K-flat: on its trivializing cover its tensor
   with any acyclic complex is that complex, and slice restriction is exact by
   lem-pur-site-restriction-module-adjunction-exact. Compute derived reduction on this
   representative using def-weil-integral-derived-reduction, obtaining the ordinary
   finite line in degree zero with the same quotient transition and augmentation maps.
9. The single stratum S witnesses constructibility of each finite reduction. Its support
   is contained in {0}; on a nonempty S a geometric stalk is the nonzero coefficient ring,
   so the support equals {0}. On the empty scheme every sheaf is zero and support is empty.
10. A rank-one locally free line in degree zero is locally strictly perfect: take
    the regular module in degree zero and zero elsewhere on each trivializing chart.
    Perfect duality identifies it with its double dual into the regular coefficient
    object. The existing constant-coefficient theorem makes that object complete,
    and ambient internal Hom into a complete object is complete. Transport the
    augmented reduction triangle through the bidual isomorphism and the proved
    intrinsic/legacy completeness comparison.
11. All reductions are constructible with uniform amplitude [0,0], so the integral line
    belongs to def-weil-derived-complete-integral-detailed. -/
theorem pur_twist_sheaf_locally_free
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [∀ x : S, Invertible (l : S.residueField x)] :
    (∀ n : ℕ,
      (∃ (I : Type (u + 1)) (U : I → S.ProEt)
        (f : ∀ i : I, U i ⟶ ProEt.mk (𝟙 S)),
        Presieve.ofArrows U f ∈ (ProEt.precoverage S).coverings _ ∧
        (∀ i : I, Etale (U i).hom) ∧
        ∀ i : I, Nonempty ((purTwistRootsModule S l n).over (U i) ≅
          (SheafOfModules.unit (purTwistRing S (purTwistFiniteRing S l n))).over (U i))) ∧
      (purTwistRootsModule S l n).IsFiniteLocallyFreeOfRank 1 ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
        Finite ((proEtaleGeometricStalk (C := AddCommGrpCat.{u + 1}) s
          (proEtaleRootsOfUnitySheaf S (l ^ (n + 1)))) : Type (u + 1))) ∧
      Epi (proEtaleRootsOfUnityTransition S (l ^ (n + 1)) (l ^ (n + 2))
        (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
        (pow_dvd_pow l (Nat.le_succ (n + 1))))) ∧
    ((∃ (I : Type (u + 1)) (U : I → S.ProEt)
        (f : ∀ i : I, U i ⟶ ProEt.mk (𝟙 S)),
        Presieve.ofArrows U f ∈ (ProEt.precoverage S).coverings _ ∧
        ∀ i : I, Nonempty ((purTwistZlModule S l).over (U i) ≅
          (SheafOfModules.unit (purTwistRing S (purTwistZlCompletion S l))).over (U i))) ∧
      (purTwistZlModule S l).IsFiniteLocallyFreeOfRank 1 ∧
      ∀ n : ℕ, Nonempty
        (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
          (purTwistZlProjection S l n)
          (purTwistZlModule S l) ≅ purTwistRootsModule S l n)) ∧
    ((∃ k : ℕ, Nonempty (@Module.Basis (Fin k) ℤ_[l]
        (Padic.coefficientExtensionIntegers l E) _ _
        (Module.compHom (Padic.coefficientExtensionIntegers l E) (purTwistIntegersMap l E)))) ∧
      IsIso (purTwistCoefficientComparison S l E) ∧
      (purTwistIntegralModule S l E).IsFiniteLocallyFreeOfRank 1 ∧
      ∀ n : ℕ,
        Nonempty (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
          (WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S n)
            (purTwistIntegralModule S l E) ≅ purTwistFiniteOne S l E n) ∧
        (purTwistFiniteOne S l E n).IsFiniteLocallyFreeOfRank 1 ∧
        IsLocallyConstantProEtaleModuleSheaf S (Padic.coefficientExtensionRing l E (n + 1))
          (purTwistFiniteOne S l E n) ∧
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
          Finite (proEtaleGeometricModuleStalk s
            (WeilConjectures.integralCoefficientCommRingSheaf l E S n)
            (purTwistFiniteOne S l E n))) ∧
    (∀ (D : WeilConjectures.FiniteFieldDatum.{d}) (hl : l ≠ D.p),
      (∀ n : ℕ,
        Nonempty ((WeilConjectures.integralDerivedReduction l E S D hl n).obj
          ((DerivedCategory.singleFunctor _ 0).obj (purTwistIntegralModule S l E)) ≅
            (DerivedCategory.singleFunctor _ 0).obj (purTwistFiniteOne S l E n)) ∧
        intrinsicFiniteTorsionConstructible l E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) S
          ((DerivedCategory.singleFunctor _ 0).obj (purTwistFiniteOne S l E n)) ∧
        proEtaleCohomologicalSupport
          ((DerivedCategory.singleFunctor _ 0).obj (purTwistFiniteOne S l E n)) ⊆ {0} ∧
        (Nonempty S → proEtaleCohomologicalSupport
          ((DerivedCategory.singleFunctor _ 0).obj (purTwistFiniteOne S l E n)) = {0})) ∧
      WeilConjectures.IsDerivedComplete l E S D hl
        ((DerivedCategory.singleFunctor _ 0).obj (purTwistIntegralModule S l E)) ∧
      WeilConjectures.boundedConstructibleDerivedCompleteIntegral D l hl E S
        ((DerivedCategory.singleFunctor _ 0).obj (purTwistIntegralModule S l E))) := by
  classical
  obtain ⟨hfinite, hcover, hquotient⟩ := purTwistRootLocalModels S l
  have hz := rank_one_of_cover (purTwistZlModule S l) hcover
  obtain ⟨hintegral, hmodels⟩ := purTwistIntegralLocalModels S l E hz
  have hi := rank_one_of_cover (purTwistIntegralModule S l E) hintegral
  have hfmodels (n : ℕ) :
      IsLocallyConstantProEtaleModuleSheaf S (Padic.coefficientExtensionRing l E (n + 1))
        (purTwistFiniteOne S l E n) ∧
      (letI := Padic.finite_coefficientExtensionRing l E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n))
       IsConstructibleProEtaleModuleSheaf S (Padic.coefficientExtensionRing l E (n + 1))
         (purTwistFiniteOne S l E n)) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
        Finite (proEtaleGeometricModuleStalk s
          (WeilConjectures.integralCoefficientCommRingSheaf l E S n)
          (purTwistFiniteOne S l E n)) := by
    let := Padic.finite_coefficientExtensionRing l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n))
    exact finiteLocallyFreeLine_models S (Padic.coefficientExtensionRing l E (n + 1))
      (purTwistFiniteOne S l E n) (rank_one_of_cover _ (hmodels n).2.1)
  have hsingle (n : ℕ) :
      intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) S
        ((DerivedCategory.singleFunctor _ 0).obj (purTwistFiniteOne S l E n)) ∧
      proEtaleCohomologicalSupport
        ((DerivedCategory.singleFunctor _ 0).obj (purTwistFiniteOne S l E n)) ⊆ {0} ∧
      (Nonempty S → proEtaleCohomologicalSupport
        ((DerivedCategory.singleFunctor _ 0).obj (purTwistFiniteOne S l E n)) = {0}) := by
    let := Padic.finite_coefficientExtensionRing l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n))
    have hc := (hfmodels n).2.1
    have hn := (hmodels n).2.2
    obtain ⟨hfin, hconst, hs, heq⟩ := constructible_single_support S
      (Padic.coefficientExtensionRing l E (n + 1)) (purTwistFiniteOne S l E n) hc _ (Iso.refl _)
    exact ⟨⟨hfin, hconst⟩, hs, fun hS ↦ heq (hn hS)⟩
  refine ⟨?_, ⟨hcover, hz, hquotient⟩, ?_, ?_⟩
  · intro n
    obtain ⟨⟨I, U, f, hc, he, ht⟩, hf⟩ := hfinite n
    exact ⟨⟨I, U, f, hc, he, ht⟩,
      rank_one_of_cover _ ⟨I, U, f, hc, ht⟩, hf, purTwistRootTransitions_epi S l n⟩
  · refine ⟨purTwistIntegralBasis l E, purTwistCoefficientComparison_isIso S l E, hi, ?_⟩
    intro n
    obtain ⟨hq, hc, _⟩ := hmodels n
    exact ⟨hq, rank_one_of_cover _ hc, (hfmodels n).1, (hfmodels n).2.2⟩
  · intro D hl
    obtain ⟨hred, hcomplete⟩ := completedLine_derived S l E (purTwistIntegralModule S l E)
      hi D hl
    have e (n : ℕ) := (hred n).some ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (hmodels n).1.some
    refine ⟨fun n ↦ ⟨⟨e n⟩, hsingle n⟩, hcomplete, hcomplete, 0, 0, le_rfl, ?_⟩
    intro n
    let := Padic.finite_coefficientExtensionRing l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n))
    obtain ⟨hfin, hconst, hs, _⟩ := constructible_single_support S
      (Padic.coefficientExtensionRing l E (n + 1)) (purTwistFiniteOne S l E n)
      (hfmodels n).2.1 _ (e n)
    refine ⟨⟨hfin, hconst⟩, ?_⟩
    intro i hisupport
    have hi0 : i = 0 := hs hisupport
    subst i
    exact ⟨le_rfl, le_rfl⟩

end AlgebraicGeometry.Scheme
