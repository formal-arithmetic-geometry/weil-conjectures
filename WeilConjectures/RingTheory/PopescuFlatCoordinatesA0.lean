/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.RingTheory.PopescuAdmissibleSubalgebra
public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.ArtinianFlatSubalgebras
import WeilConjectures.RingTheory.PopescuFlatCoordinatesSetup

/-!
# An admissible subalgebra containing a finite set

In the Artinian quotient `Λ_q / (qΛ_q)^n` of a geometrically regular Noetherian algebra over a
field, every finite set is contained in a Popescu-admissible subalgebra.

## References

* [Stacks, Tag 07FG], applied in the first paragraph of the proof of [Stacks, Tag 07FH]
-/

@[expose] public section
set_option autoImplicit false
universe u v
namespace Algebra
/-- An admissible Artinian subalgebra containing a finite set in the prime-power quotient. -/
theorem exists_popescu_admissible_containing_finset
    (k : Type u) (Λ : Type v) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (p : ℕ) [CharP k p] (hp : 0 < p)
    (hreg : IsGeometricallyRegular k Λ) (q : Ideal Λ) [q.IsPrime]
    (n : ℕ) (hn : 1 ≤ n)
    (E : Finset (Localization.AtPrime q ⧸
      (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) :
    ∃ (A : Subalgebra k (Localization.AtPrime q ⧸
        (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) (_ : IsLocalRing A),
      A.IsPopescuAdmissible ((q.map (algebraMap Λ (Localization.AtPrime q))).map
        (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))) ∧
      ∀ e ∈ E, e ∈ A := by
  let B := Localization.AtPrime q ⧸
    (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n
  obtain ⟨hArt, hLoc, hMax, hFin⟩ :=
    popescu_flat_coordinates_setup k Λ p hp hreg q n hn
  let : IsArtinianRing B := hArt
  let : IsLocalRing B := hLoc
  obtain ⟨S, hdir, hcover, hprops, _⟩ :=
    exists_directed_artinian_flat_subalgebras.{u, v, 0} k B p hp hFin
  have hnonempty : S.Nonempty := by
    obtain ⟨A, hA, hmem⟩ := hcover (0 : B)
    exact ⟨A, hA⟩
  have hfin : ∃ A ∈ S, ∀ e ∈ E, e ∈ A := by
    classical
    induction E using Finset.induction_on with
    | empty =>
        obtain ⟨A, hA⟩ := hnonempty
        exact ⟨A, hA, by simp⟩
    | @insert x s hx ih =>
        obtain ⟨A, hA, hs⟩ := ih
        obtain ⟨A', hA', hxA'⟩ := hcover x
        obtain ⟨C, hC, hAC, hA'C⟩ := hdir A hA A' hA'
        exact ⟨C, hC, fun e he ↦ by
          by_cases heq : e = x
          · simpa [heq] using hA'C hxA'
          · exact hAC (hs e (Finset.mem_of_mem_insert_of_ne he heq))⟩
  obtain ⟨A, hA, hE⟩ := hfin
  obtain ⟨hAloc, hAart, hAflat, hm, hAeft⟩ := hprops A hA
  let : IsLocalRing A := hAloc
  refine ⟨A, hAloc, ?_, hE⟩
  exact ⟨hAart, hAeft, ⟨hAloc, hAflat, hm.trans hMax⟩⟩

end Algebra
