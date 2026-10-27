/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SemilinearOpenClosedData
public import Sheaf.Paper.SequenceSiteOpenExtension
import Sheaf.Paper.SequenceOpenCoefficientConstruction
import Sheaf.Paper.SequenceOpenOrdinary
import Sheaf.Paper.SemilinearClosedSystemPresentation
import Sheaf.Paper.SemilinearOrdinaryLocalizationSequence
import Sheaf.Paper.SemilinearLocalizationScalarCompatibility

/-! # The open-closed sequence of strict semilinear complexes
Source: Stacks 09AH and 09BM
(blueprint: lem-sp-semilinear-open-closed-complex-sequence). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.SemilinearSections.OpenClosed

private theorem sequenceData_of_closed
    {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (U : T.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ)
    (B : ℕ → Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) (K : ClosedData i B τ)
    (O : SequenceOpenOrdinary.{u + 1, u, 0} (Scheme.ProEt.topology T) U B τ)
    (ht : O.Transitions) : Nonempty (SequenceData i U B τ) := by
  have := K.pullAdditive
  have := K.pushAdditive
  refine ⟨{
    openPart := O
    openTransitions := ht
    pullAdditive := K.pullAdditive
    pullLimits := K.pullLimits
    pullColimits := K.pullColimits
    pushAdditive := K.pushAdditive
    pushLimits := K.pushLimits
    pushColimits := K.pushColimits
    pushEvaluation := K.pushEvaluation
    pushEvaluation_sections := K.pushEvaluation_sections
    pullEvaluation := K.pullEvaluation
    levelPresentation := K.levelPresentation
    unitEvaluation := K.unitEvaluation
    complexSequence := ?_ }⟩
  intro C
  let ε := (O.adjunction.mapHomologicalComplex (.up ℤ)).counit.app C
  let η := ((adjunction i B τ).mapHomologicalComplex (.up ℤ)).unit.app C
  have h := semilinearOrdinaryLocalization i U hU B τ K O
  have w : ε ≫ η = 0 := by
    apply HomologicalComplex.hom_ext
    intro q
    change (O.adjunction.counit.app (C.X q)) ≫
      ((adjunction i B τ).unit.app (C.X q)) = 0
    exact (h (C.X q)).2.2.toIsComplex.zero 0 (by decide)
  let S := ShortComplex.mk ε η w
  have hs : S.ShortExact := HomologicalComplex.shortExact_of_degreewise_shortExact S (by
    intro q
    exact {
      mono_f := (h (C.X q)).1
      epi_g := (h (C.X q)).2.1
      exact := (h (C.X q)).2.2.exact 0 })
  exact ⟨hs.mono_f, hs.epi_g, hs.exact.exact_toComposableArrows⟩

attribute [local irreducible] rings ringPresheaf systemRing

/-- The canonical degreewise short exact sequence of unbounded strict semilinear complexes.
Source: Stacks Project, Tags 09AH and 09BM; blueprint
sk-lem-sp-tower-bound-operations.proof.md (2), final sentence
(blueprint: lem-sp-semilinear-open-closed-complex-sequence).

Proof:
1. For a system map, form its kernels and cokernels at every coefficient level.
Scalar restriction is exact on the underlying abelian sheaves, so the transition
maps restrict to the kernels and descend to the cokernels. Uniqueness proves the
identity and composition equations and the universal properties in systems.
Finite biproducts and coimage-image comparisons are componentwise, making the
system category abelian; exactness is detected at every level.
2. The inverse/direct-image scalar comparisons use the inverse-image action and
the coefficient adjunction unit. Direct image retains sections on base changes.
Naturality of the ring unit proves coefficient compatibility and composition.
3. Open extension is the direct-sum extension presheaf followed by module
sheafification. Scalar restriction leaves each additive summand unchanged.
Agreement on all summands and uniqueness of sheafification prove composition
coherence and preservation of the actual open adjunction maps, as in
lem-cbc-ringed-open-scalar-limit-coherence and lem-pur-sequence-site-open-extension.
4. For each output operation the transition is the image of the original
transition followed by its scalar comparison. Naturality and comparison
composition prove every three-index transition equation. They also prove that
the open counit and closed unit are system morphisms, naturally in the input.
5. Apply lem-weil-pbc-proetale-ringed-open-closed at each B_n. Its filtered-colimit
clause is unused, so no qcqs assumption on T is needed. The inverse images are
exact by lem-weil-pbc-proetale-immersion-limit-preservation. Step 1 proves
exactness of all four system functors and the system counit-unit sequence.
6. Apply these additive functors in every integer cochain degree. Functoriality
and additivity preserve d squared equal to zero. Naturality of the counit and
unit proves the chain-map equations. Exact evaluation identifies both arrows
with their ordinary ringed pro-etale counterparts. No boundedness is used.
7. For a compatible B-to-D map, the two routes from B_m to D_n agree. The scalar
comparisons therefore commute with all system transitions and differentials.
The actual counit and unit equations are the openCounit and closedUnit fields.
These comparisons are identities on underlying additive data before taking
adjoints; no flatness, constructibility or normalization hypothesis is used. -/
theorem semilinearOpenClosedComplexSequence
    {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (U : T.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (_hU : Set.range U.hom = (Set.range i)ᶜ)
    (B : ℕ → Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) :
    ∃ P : SequenceData i U B τ,
      ∀ (D : ℕ → Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
        (σ : ∀ n : ℕ, D (n + 1) ⟶ D n) (φ : ∀ n : ℕ, B n ⟶ D n)
        (hφ : ∀ n : ℕ, φ (n + 1) ≫ σ n = τ n ≫ φ n),
        ∃ Q : SequenceData i U D σ, Nonempty (ScalarCompatibility i U B D τ σ φ hφ P Q) := by
  obtain ⟨A⟩ := sequenceOpenCoefficients.{u + 1, u, 0} (Scheme.ProEt.topology T) U
  obtain ⟨O, _, ht⟩ := sequenceOpenOrdinary T U B τ A
  obtain ⟨K⟩ := semilinearClosedSystemPresentation i U _hU B τ
  obtain ⟨P⟩ := sequenceData_of_closed i U _hU B τ K O ht
  refine ⟨P, ?_⟩
  intro D σ φ hφ
  obtain ⟨O', _, ht'⟩ := sequenceOpenOrdinary T U D σ A
  obtain ⟨K'⟩ := semilinearClosedSystemPresentation i U _hU D σ
  obtain ⟨Q⟩ := sequenceData_of_closed i U _hU D σ K' O' ht'
  exact ⟨Q, semilinearLocalizationScalarCompatibility i U _hU B D τ σ φ hφ P Q⟩

end WeilConjectures.SemilinearSections.OpenClosed

