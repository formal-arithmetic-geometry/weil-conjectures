/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.Paper.IntegralCriterionReductions
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Sheaf.Paper.AdicStratifiedPerfectData

public import Sheaf.Paper.IntegralHomReductionComparison
import Sheaf.Paper.FiniteFieldHomEtaleWitness
import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom

/-! # Etale residue origin of integral internal Hom

Source: Bhatt--Scholze, Lemma 6.7.13; Stacks Tag 09AL.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})


/-- The canonical invertible reduction comparison and adic input witnesses give bounded
constructible etale origin of the reduced Hom. No bounded representative or Tor assertion
is included here; those follow independently from truncation over the residue field.

Source: Bhatt--Scholze, Lemma 6.7.13, Definition 6.5.1, and Stacks Tag 09AL
(blueprint: lem-sfb-integral-adic-hom-residue-origin).

Proof: unpack the two adic predicates to obtain etale residue complexes C_K,C_L with
bounded constructible cohomology and their coefficient-linear derived comparison
isomorphisms. The DVR theorem identifies the exponent-one quotient with the finite
residue field A of characteristic l. The normalized finite-discrete coefficient
encoding changes its fixed-scalar presentation to ULift(A), and identifies its finite
constant local models and the etale cohomology predicates. Apply finiteField_hom_etale_witness
to Q(C_K),Q(C_L). It gives an etale complex C with bounded constructible cohomology
and inverse image equal to their ambient finite-field Hom. Naturality of Hom in its two
arguments transports the input comparison isomorphisms. The evaluation-preserving
module-object/ringed-site comparison identifies the inverse of the assumed canonical
reduction map with a coefficient-linear isomorphism from this residue Hom to the
reduction of F(Hom(K,L)). Transport the witness's C and its bounds back along the
residue-ring isomorphism, and compose these derived isomorphisms. This proves precisely
the asserted residue origin, also for zero inputs and the empty scheme. -/
theorem integralAdicHom_residue_origin
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (D₀ : WeilConjectures.FiniteFieldDatum.{0}) (hl : l ≠ D₀.p)
    (K L : DerivedCategory (AdicCompletion.Modules l E X))
    (hK : Scheme.IsSfbAdicConstructible X (Scheme.pbcIntegralDatum l E).ideal
      (((integralSectionDerivedEquivalence l E X).functor ⋙
        Scheme.integralDetailedTransport X l E ⋙
        Scheme.pbcDerivedRestrict (Scheme.pbcCompletedComparison X
          (Scheme.pbcIntegralDatum l E)).hom).obj K))
    (hL : Scheme.IsSfbAdicConstructible X (Scheme.pbcIntegralDatum l E).ideal
      (((integralSectionDerivedEquivalence l E X).functor ⋙
        Scheme.integralDetailedTransport X l E ⋙
        Scheme.pbcDerivedRestrict (Scheme.pbcCompletedComparison X
          (Scheme.pbcIntegralDatum l E)).hom).obj L))
    (hred : IsIso (WeilConjectures.integralHomReductionComparison D₀ l hl E X 0
      ((integralSectionDerivedEquivalence l E X).functor.obj K)
      ((integralSectionDerivedEquivalence l E X).functor.obj L))) :
    ∃ C : CochainComplex (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (Scheme.PbcIntegralRing l E ⧸
          (Scheme.pbcIntegralDatum l E).ideal ^ (0 + 1)))) ℤ,
      (∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q → IsZero (C.homology q)) ∧
      (∀ q : ℤ, Scheme.IsConstructibleSheaf (C.homology q)) ∧
      Nonempty (DerivedCategory.Q.obj
        (((comparisonUpperStar (ModuleCat.{u + 1} (Scheme.PbcIntegralRing l E ⧸
          (Scheme.pbcIntegralDatum l E).ideal ^ (0 + 1))) X).mapHomologicalComplex
            (.up ℤ)).obj C) ≅
        DerivedCategory.Q.obj (Scheme.sfbResidueComplex X (Scheme.pbcIntegralDatum l E).ideal
          (((integralSectionDerivedEquivalence l E X).functor ⋙
        Scheme.integralDetailedTransport X l E ⋙
        Scheme.pbcDerivedRestrict (Scheme.pbcCompletedComparison X
          (Scheme.pbcIntegralDatum l E)).hom).obj
        (((CondensedRing.derivedHom (DerivedNakayama.integerRing l E) X).obj
            (op K)).obj L)))) := by sorry

end AlgebraicGeometry.ProEtale
