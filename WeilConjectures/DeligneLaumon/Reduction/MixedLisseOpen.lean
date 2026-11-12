/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.MixedNoetherianInduction
public import WeilConjectures.DeligneLaumon.Reduction.MixedWeightsIn
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.ExtensionsMap

/-!
# Mixed sheaves with lisse graded pieces on a dense open

A mixed Weil sheaf on a reduced quasi-compact `k₀`-scheme `X` admits, on a nonempty open `U` of
`X`, a filtration whose successive quotients are lisse and punctually pure
(`AlgebraicGeometry.WeilSheaf.IsMixed.exists_opens_filtrationClosure_isLissePunctuallyPure`):
each of the finitely many pure quotients of a mixed filtration is lisse on a dense open
(`AlgebraicGeometry.WeilSheaf.exists_dense_isLisse_upperStar`). This is the generic step of the
Noetherian inductions of `proposition-weights-under-usual-operations`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  {ι : PadicAlgCl l →+* ℂ} {F : WeilSheaf k₀ l X}

variable (ι) in
/-- The property of a Weil sheaf of being lisse and punctually `ι`-pure of some weight. -/
def isLissePunctuallyPure : ObjectProperty (WeilSheaf k₀ l X) :=
  fun F ↦ F.IsLisse ∧ ∃ v, F.IsPunctuallyPureOfWeight ι v

instance : (isLissePunctuallyPure (k₀ := k₀) (l := l) (X := X) ι).IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨hL, v, h⟩ ↦ ⟨hL.of_iso e, v, h.of_epi e.hom⟩

/-- A sheaf with a finite filtration with lisse quotients is lisse. -/
theorem IsLisse.of_filtrationClosure_isLissePunctuallyPure
    (h : (isLissePunctuallyPure ι).filtrationClosure F) : F.IsLisse := by
  induction h with
  | of_isZero hX => exact isLisse_of_isZero hX
  | of_mono i _ hi ih => exact IsLisse.of_mono_cokernel i ih hi.1

/-- A sheaf with a finite filtration with lisse punctually pure quotients is mixed. -/
theorem IsMixed.of_filtrationClosure_isLissePunctuallyPure
    (h : (isLissePunctuallyPure ι).filtrationClosure F) : F.IsMixed ι := by
  refine IsMixedOfWeightsIn.isMixed (S := Set.univ) ?_
  induction h with
  | of_isZero hX => exact ObjectProperty.filtrationClosure.of_isZero hX
  | of_mono i _ hi ih =>
    obtain ⟨-, v, h⟩ := hi
    exact ObjectProperty.filtrationClosure.of_mono i ih ⟨v, trivial, h⟩

/-- Filtrations with lisse punctually pure quotients pull back. -/
theorem filtrationClosure_isLissePunctuallyPure_upperStar {Y : Scheme.{u}}
    [Y.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    (φ : Y ⟶ X) [φ.IsOver (Spec (CommRingCat.of k₀))]
    (h : (isLissePunctuallyPure ι).filtrationClosure F) :
    (isLissePunctuallyPure ι).filtrationClosure ((WeilSheaf.upperStar φ).obj F) :=
  ObjectProperty.filtrationClosure.map (WeilSheaf.upperStar φ)
    (fun _ ⟨hL, v, h⟩ ↦ ⟨hL.upperStar φ, v, h.upperStar φ⟩) h

/-- **Lisse graded pieces on a nonempty open.** A mixed Weil sheaf `F` on a nonempty reduced
quasi-compact `k₀`-scheme `X` locally of finite type has a nonempty open `U` such that on every
open `V ⊆ U`, the restriction of `F` admits a finite filtration whose successive quotients are
lisse and punctually pure: the restrictions of a mixed filtration to the intersection of the
dense opens on which its pure quotients are lisse
(blueprint: `proposition-weights-under-usual-operations`, proofs of clauses 5 and 6). -/
theorem IsMixed.exists_opens_filtrationClosure_isLissePunctuallyPure [IsReduced X] [Nonempty X]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] (hF : F.IsMixed ι) :
    ∃ U : X.Opens, (U : Set X).Nonempty ∧ ∀ V : X.Opens, V ≤ U →
      (isLissePunctuallyPure ι).filtrationClosure ((WeilSheaf.upperStar V.ι).obj F) := by
  obtain ⟨w, h⟩ := hF
  rw [isMixedOfWeightsAtMost_iff_filtrationClosure] at h
  induction h with
  | of_isZero hX =>
    refine ⟨⊤, ?_, fun V _ ↦ .of_isZero ((WeilSheaf.upperStar V.ι).map_isZero hX)⟩
    rw [TopologicalSpace.Opens.coe_top]
    exact Set.univ_nonempty
  | @of_mono G' G i _ _ hi ih =>
    -- restate `hi` with the cokernel of `i` given by instance search
    have hi' : isPunctuallyPureOfWeightLE ι w (cokernel i) := hi
    obtain ⟨U', ⟨u, hu⟩, hU'⟩ := ih
    obtain ⟨L, hL, hLl⟩ := exists_dense_isLisse_upperStar (cokernel i)
    obtain ⟨v, -, hpure⟩ := hi'
    refine ⟨U' ⊓ L, ?_, fun V hV ↦ ?_⟩
    · rw [TopologicalSpace.Opens.coe_inf]
      exact hL.inter_open_nonempty _ U'.isOpen ⟨u, hu⟩
    have hVL : V ≤ L := hV.trans inf_le_right
    have hlisse : ((WeilSheaf.upperStar V.ι).obj (cokernel i)).IsLisse :=
      (isLisse_upperStar_congr (X.homOfLE_ι hVL) _).1
        ((isLisse_upperStar_comp_iff (X.homOfLE hVL) L.ι _).2 (hLl.upperStar _))
    have hpure' : ((WeilSheaf.upperStar V.ι).obj (cokernel i)).IsPunctuallyPureOfWeight ι v :=
      hpure.upperStar V.ι
    have h₀ : isLissePunctuallyPure ι ((WeilSheaf.upperStar V.ι).obj (cokernel i)) :=
      ⟨hlisse, v, hpure'⟩
    have : Mono ((WeilSheaf.upperStar V.ι).map i) := (WeilSheaf.upperStar V.ι).map_mono i
    exact .of_mono ((WeilSheaf.upperStar V.ι).map i) (hU' V (hV.trans inf_le_left))
      ((isLissePunctuallyPure ι).prop_of_iso (PreservesCokernel.iso (WeilSheaf.upperStar V.ι) i) h₀)

end AlgebraicGeometry.WeilSheaf
