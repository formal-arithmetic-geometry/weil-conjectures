/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.Algebra.Homology.BoundedFlatReplacement
import WeilConjectures.Algebra.Homology.FlatTruncationSuccessor

/-!
# Compatible flat replacements of good truncations

## References

* Stacks Project, Cohomology on Sites, Lemma 077J
* Stacks Project, Derived Categories, the lemma on special direct systems
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Good truncations admit a strictly compatible tower of bounded-above flat replacements. -/
theorem exists_flat_truncation_tower
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    (G : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) :
    ∃ (E : ℕ → CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
      (t : ∀ n : ℕ, E n ⟶ E (n + 1))
      (q : ∀ n : ℕ, E n ⟶ G.truncLE (n : ℤ)),
      (∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i)) ∧
      (∀ n : ℕ, QuasiIso (q n)) ∧
      (∀ (n : ℕ) (i : ℤ), Epi ((q n).f i)) ∧
      (∀ n : ℕ, t n ≫ q (n + 1) ≫ G.ιTruncLE ((n + 1 : ℕ) : ℤ) =
        q n ≫ G.ιTruncLE (n : ℤ)) := by
  classical
  let A := SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  let Stage (n : ℕ) := {p : (Σ E : CochainComplex A ℤ, E ⟶ G.truncLE (n : ℤ)) //
    (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (p.1.X i)) ∧
    (∀ i : ℤ, SheafOfModules.IsFlat (p.1.X i)) ∧ QuasiIso p.2 ∧
    (∀ i : ℤ, Epi (p.2.f i))}
  -- The initial stage is the existing bounded replacement of the zeroth truncation.
  obtain ⟨Q, ε, hQ⟩ := exists_functorial_boundedAbove_flat_replacement J R 0
  let P : ObjectProperty (CochainComplex A ℤ) :=
    fun K ↦ ∀ i : ℤ, (0 : ℤ) < i → IsZero (K.X i)
  let F : P.FullSubcategory :=
    ⟨G.truncLE 0, fun i hi ↦ (G.truncLE 0).isZero_of_isStrictlyLE 0 i hi⟩
  let s₀ : Stage 0 := ⟨⟨Q.obj F, ε.app F⟩,
    ⟨⟨0, (hQ F).2.1⟩, (hQ F).1, (hQ F).2.2.2, (hQ F).2.2.1⟩⟩
  -- Keep the augmentation and its properties in the dependent recursion state.
  have hnext (n : ℕ) (s : Stage n) :
      ∃ s' : Stage (n + 1), ∃ t : s.val.1 ⟶ s'.val.1,
        t ≫ s'.val.2 ≫ G.ιTruncLE ((n + 1 : ℕ) : ℤ) =
          s.val.2 ≫ G.ιTruncLE (n : ℤ) := by
    obtain ⟨E', t, q', hb, hf, hq, he, hc⟩ :=
      exists_flat_truncation_successor G n s.val.1 s.val.2 s.property.1 s.property.2.1
    exact ⟨⟨⟨E', q'⟩, hb, hf, hq, he⟩, t, hc⟩
  let stages : ∀ n : ℕ, Stage n :=
    fun n ↦ Nat.rec s₀ (fun n s ↦ (hnext n s).choose) n
  have hstages (n : ℕ) : stages (n + 1) = (hnext n (stages n)).choose := rfl
  have htransition (n : ℕ) : ∃ t : (stages n).val.1 ⟶ (stages (n + 1)).val.1,
      t ≫ (stages (n + 1)).val.2 ≫ G.ιTruncLE ((n + 1 : ℕ) : ℤ) =
        (stages n).val.2 ≫ G.ιTruncLE (n : ℤ) := by
    rw [hstages]
    exact (hnext n (stages n)).choose_spec
  refine ⟨fun n ↦ (stages n).val.1, fun n ↦ (htransition n).choose,
    fun n ↦ (stages n).val.2, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun n ↦ (stages n).property.1
  · exact fun n ↦ (stages n).property.2.1
  · exact fun n ↦ (stages n).property.2.2.1
  · exact fun n ↦ (stages n).property.2.2.2
  · exact fun n ↦ (htransition n).choose_spec

end CochainComplex
