module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.KrullDimension.Basic

/-! Finite prime-chain contraction in filtered colimits.

Source: Stacks Project, More on Algebra, Tag 06LK.
(blueprint: lem-sc-filtered-colimit-prime-chain-contraction)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

/-- A finite prime chain in a filtered colimit contracts strictly at one stage.
The proof chooses separating elements, represents them in stages, and uses filteredness
to dominate the finitely many stages. Contractions of primes remain prime, and the
separating representatives preserve strictness.
(blueprint: lem-sc-filtered-colimit-prime-chain-contraction) -/
theorem filteredColimit_prime_chain_contraction
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{u}) :
    ∀ (n : ℕ) (p : Fin (n + 1) → Ideal (colimit R : CommRingCat.{u})),
      (∀ j, (p j).IsPrime) → StrictMono p →
      ∃ i : I,
        (∀ j, (Ideal.comap (colimit.ι R i).hom (p j)).IsPrime) ∧
        StrictMono (fun j ↦ Ideal.comap (colimit.ι R i).hom (p j)) := by
  sorry

end CommRingCat
