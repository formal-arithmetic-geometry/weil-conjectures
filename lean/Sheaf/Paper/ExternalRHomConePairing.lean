/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.Paper.ExternalRHomConePairingDefs
import Sheaf.Paper.ExternalEvaluationTransposeNatural
import Sheaf.Paper.LiftedExternalEvaluationChainModel
import Sheaf.Paper.ExternalRHomSignedCones

/-! # External derived Hom evaluation and coefficient cones -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated.Opposite
namespace AlgebraicGeometry.Etale.ExternalRHom
variable (A : Type (u + 1)) [CommRing A]
attribute [local instance] derivedBraiding siteDerivedMonoidal
  siteDerivedClosed siteLocalizationMonoidal constantComplexOplax pullComplexMonoidal
  complexesBraiding coefficientComplexMonoidal

/-- External global derived Hom evaluation, with its chain normalization and both
coefficient-cone compatibilities.

Source: Stacks 08J9, 08JA, 08JB, 08JC, 0A90, 0G7D and 0G7E;
blueprint main-20261015, lem-pur-kunneth-supported proof paragraphs 1 and 3
(blueprint: lem-pur-external-rhom-cone-pairing).

Proof: Use the existing derived constant/sections and tensor/Hom adjunctions to
transpose the tensor of the two pulled evaluations. Resolve the targets by
K-injectives and their global Hom complexes by flat-term K-flat complexes.
The evaluation identity identifies their localized evaluations with the
adjunction counits. Factor each chain evaluation through a flat-term K-flat
complex by Stacks 0G7D. Pull these two complexes to P, tensor them, and resolve
that tensor by J. The Koszul interchange of the second Hom factor of degree s
with the first coefficient of degree q supplies (-1)^(s*q). The two homotopies
to the original evaluations become equalities after localization, proving
that every such chain map is the same transpose. Evaluation naturality proves
all four naturalities and the open-restriction square. Hom into K-injectives,
derived sections, pullback and tensor carry distinguished triangles to
triangles. The first-variable Hom shift sends a degree n cochain f to
(-1)^n f with its coefficient index shifted by -1. For the E shift the two
chain evaluation composites have sign (-1)^(s*q+s); for the H shift they
have sign (-1)^(s*q+q+r). These give the shift squares with, respectively,
the unsigned right-tensor comparison and the (-1)^r left-tensor comparison.
Naturality at the connecting morphism together with these shift squares
proves the third square for the specified cone component in both variables.
The braiding is the existing derived Koszul braiding. The Hom-shift witness
is natural in every target morphism; its representative normalization therefore
transports to the external tensor target as well as K-injective objects. -/
theorem external_rhom_cone_pairing :
    ∃ S : ∀ (X : Scheme.{u}) (K : DerivedCategoryModule A X),
        (homFirst A X K).CommShift ℤ,
      HasKoszulBraiding A ∧
      HasSignedHomShift (homShift := S) A ∧
      (∀ (X : Scheme.{u}) (E I : Complexes A X) [I.IsKInjective],
        IsPlus A ((siteQ A X).obj I) → Nonempty (HomModel A E I)) ∧
      (∀ (X Y P : Scheme.{u}) (a : P ⟶ X) (b : P ⟶ Y)
        (E : Complexes A X) (H : Complexes A Y)
        (I : Complexes A X) (I' : Complexes A Y) [I.IsKInjective] [I'.IsKInjective],
        IsBoundedFlat A E → IsBoundedFlat A H →
        IsPlus A ((siteQ A X).obj I) → IsPlus A ((siteQ A Y).obj I') →
        IsPlus A (external A a b ((siteQ A X).obj I) ((siteQ A Y).obj I')) →
        HasChainNormalization A a b E H I I') ∧
      IsNatural A ∧ CommutesWithOpenRestriction A ∧
      PreservesCoefficientCones (homShift := S) A := by
  obtain ⟨S, hs, hmodel⟩ := lifted_external_evaluation_derived_hom_shift A
  have hm : ∀ (X : Scheme.{u}) (E I : Complexes A X) [I.IsKInjective],
      IsPlus A ((siteQ A X).obj I) → Nonempty (HomModel A E I) := by
    intro X E I _ _
    obtain ⟨m, _, _, _⟩ := hmodel X E I
    exact ⟨m⟩
  have hn : ∀ (X Y P : Scheme.{u}) (a : P ⟶ X) (b : P ⟶ Y)
      (E : Complexes A X) (H : Complexes A Y)
      (I : Complexes A X) (I' : Complexes A Y) [I.IsKInjective] [I'.IsKInjective],
      IsBoundedFlat A E → IsBoundedFlat A H →
      IsPlus A ((siteQ A X).obj I) → IsPlus A ((siteQ A Y).obj I') →
      IsPlus A (external A a b ((siteQ A X).obj I) ((siteQ A Y).obj I')) →
      HasChainNormalization A a b E H I I' := by
    intro X Y P a b E H I I' _ _ hE hH hK hL hF
    exact (lifted_external_evaluation_chain_model A a b E H I I' hE hH hK hL hF).2.2.1
  have hRes : CommutesWithOpenRestriction A := by
    obtain ⟨_, _, _, hx, hy⟩ := external_evaluation_transpose_natural A
    constructor
    · intro X X' Y P P' a b j p a' _ sq E K H L _ _ _ _ _
      exact hx X X' Y P P' a b j p a' sq E K H L
    · intro X Y Y' P P' a b k p b' _ sq E K H L _ _ _ _ _
      exact hy X Y Y' P P' a b k p b' sq E K H L
  refine ⟨S, ?_, hs, hm, hn, external_evaluation_pairing_natural A, hRes, ?_⟩
  · intro X E H _ _
    exact external_rhom_derived_braiding (Modules A X) E H
  · exact external_rhom_coefficient_cones A S hs

end AlgebraicGeometry.Etale.ExternalRHom
