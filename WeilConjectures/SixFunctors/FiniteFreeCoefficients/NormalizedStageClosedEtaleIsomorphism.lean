/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.NormalizedStageComparisonObligations
import all WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageFiniteRingFoundations
import all WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageSiteIsomorphismData
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleLocallyClosedShriek

/-! Ordinary closed stage comparison helper.

Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraphs 1--2.
(blueprint: new-lem-sf-normalized-stage-closed-etale-isomorphism).

The helper proves that the ordinary closed stage comparison is invertible, by the generic
closed-support-triangle criterion `Etale.closedCoefficient_isIso` of
`WeilConjectures.AlgebraicGeometry.Etale.EtaleLocallyClosedShriek`, whose map is definitionally `Sites.stageClosedMap false`. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.FiniteCoefficientAdjoints
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

/--
For the finite-field datum, a stage arrow `a : s ⟶ t` and an ordinary ctf object `M` on `X`,
the closed stage comparison `Sites.stageClosedMap false a i M` is an isomorphism.

Proof. `D.k` has characteristic `D.p`, so `X` and `Z` are Noetherian and `s.ring` has an
annihilating exponent invertible on `X`. Exceptional stability gives that `i^! M` is finite-Tor
constructible, and open restriction gives the same for `M|_V`, `V = X \ i(Z)`. The finite-ring
direct-image theorem makes the direct-image comparisons for `i` at `i^! M` and for `V → X` at
`M|_V` invertible. Tensoring the closed-support triangle `i_* i^! M → M → j_* (M|_V)` with the
scalar extension, the open and middle comparisons are invertible, so the first component is
invertible by two out of three; by full faithfulness of `i_*` and the exceptional counit it is
`etaleShriekClosedCoefficientMap`, definitionally the map of the statement.
Source: blueprint lem-coef-finite-free-extension, paragraphs 1--2.
(blueprint: new-lem-sf-normalized-stage-closed-etale-isomorphism)
-/
theorem normalized_stage_closed_etale_isomorphism
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    (Z : Scheme.{u}) [Z.Over (Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    (i : Z ⟶ X) [IsClosedImmersion i]
    [i.IsOver (Spec (.of D.k))]
    {s t : Stage l E} (a : Arrow s t)
    (M : Sites.D false s.ring X) :
    Sites.Ctf false s.ring X M → IsIso (Sites.stageClosedMap false a i M) := by
  classical
  intro hM
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card.symm.trans D.card_base).trans D.cardinality_eq)
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let := finiteTypeNoetherian D.k X
  let := finiteTypeNoetherian D.k Z
  let : HasInvertibleExponent s.ring X :=
    stageInvertibleExponent D.k D.p l hl s X
  let := (Compactification.ofIsProper i).hasCompactification
  have hClosed : Ctf s.ring Z ((closedUpper s.ring i).obj M) :=
    Etale.finiteTor_closedExceptional s.ring (X ↘ Spec (.of D.k)) i M hM
  have hDirect : IsIso (Etale.finiteCoefficientDirectImageMap a.ringMap i
      ((closedUpper s.ring i).obj M)) :=
    (finite_ring_scalar_direct_foundations D a.ringMap Z X i).2.2 false _ hClosed
  let V : X.Opens := ⟨(Set.range i.base)ᶜ,
    (IsClosedImmersion.isClosedEmbedding i).isClosed_range.isOpen_compl⟩
  have hV : Set.range i.base = (Set.range V.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι]
    exact (compl_compl _).symm
  let : V.toScheme.Over (Spec (.of D.k)) := ⟨V.ι ≫ X ↘ Spec (.of D.k)⟩
  let : V.ι.IsOver (Spec (.of D.k)) := ⟨rfl⟩
  have : LocallyOfFiniteType (V.toScheme ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (V.ι ≫ X ↘ Spec (.of D.k)))
  have : QuasiCompact (V.toScheme ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (V.ι ≫ X ↘ Spec (.of D.k)))
  have hOpen := Etale.finiteTor_restriction s.ring V.ι M hM
  have hOpenDirect : IsIso (Etale.finiteCoefficientDirectImageMap a.ringMap V.ι
      ((Etale.derivedRestriction (A := s.ring) V.ι).obj M)) :=
    (finite_ring_scalar_direct_foundations D a.ringMap V.toScheme X V.ι).2.2 false _ hOpen
  have hi := Etale.closedCoefficient_isIso a.ringMap i V.ι hV M
  exact hi

end WeilConjectures.FiniteFreeCoefficients
