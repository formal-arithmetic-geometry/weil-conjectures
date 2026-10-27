/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Field.IsField
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Order.Directed
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Data.Finset.Order

/-!
# Directed ring colimits of separably closed fields

Source: Stacks Project, Algebra, Tag 04GI, proof of `lemma-colimit-henselian`,
the assertion about the colimit of separably closed residue fields
(blueprint: lem-sfb-separably-closed-field-colimit).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

/-- A field presented as a directed colimit in commutative rings of separably closed
fields is separably closed. The stage ring structures are the given ones: `IsField.toField`
only supplies inverses. No algebraicity of the transition field extensions is required.

Source: Stacks Project, Algebra, Tag 04GI, proof of `lemma-colimit-henselian`,
the assertion about separably closed residue fields
(blueprint: lem-sfb-separably-closed-field-colimit).

Proof:
1. The forgetful functor from commutative rings preserves filtered colimits. For each
   coefficient in the finite support of a separable polynomial `p`, choose a stage
   representative using `Concrete.isColimit_exists_rep`.
2. Directedness supplies a common upper stage. Transport all representatives to it;
   naturality of the cocone shows that its image contains every coefficient of `p`.
   `Polynomial.mem_map_range` gives a polynomial `q` with image `p`.
3. Equip the stage with the field structure supplied by `hF`. Separability reflects
   along its map to `k` by `Polynomial.separable_map`, so `q` is separable.
4. The stage is separably closed, so `q` splits. Mapping this splitting to `k` shows
   that `p` splits, as required by `IsSepClosed`. No algebraicity hypothesis is used. -/
theorem isSepClosed_of_isColimit {I : Type u} [PartialOrder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (F : I ⥤ CommRingCat.{u})
    (hF : ∀ i : I, IsField (F.obj i))
    (hsep : ∀ i : I, @IsSepClosed (F.obj i) (hF i).toField)
    (k : Type u) [Field k]
    (ρ : F ⟶ (Functor.const I).obj (CommRingCat.of k))
    (hcolim : IsColimit (Cocone.mk (CommRingCat.of k) ρ)) : IsSepClosed k := by
  classical
  refine ⟨fun p hp ↦ ?_⟩
  choose stage lift hlift using fun n : p.support ↦
    Concrete.isColimit_exists_rep F hcolim (p.coeff n)
  obtain ⟨i, hi⟩ := (Finset.univ.image stage).exists_le
  let e (n : p.support) : stage n ⟶ i :=
    homOfLE (hi _ (Finset.mem_image_of_mem stage (Finset.mem_univ n)))
  let f : F.obj i →+* k := (ρ.app i).hom
  have hcoeff (n : ℕ) : p.coeff n ∈ f.range := by
    by_cases hn : n ∈ p.support
    · let a : p.support := ⟨n, hn⟩
      refine ⟨F.map (e a) (lift a), ?_⟩
      exact (ConcreteCategory.congr_hom (ρ.naturality (e a)) (lift a)).trans (hlift a)
    · exact ⟨0, by simp [Polynomial.notMem_support_iff.mp hn]⟩
  obtain ⟨q, hq⟩ := (Polynomial.mem_map_range f).mpr hcoeff
  change q.map f = p at hq
  let : Field (F.obj i) := (hF i).toField
  have : IsSepClosed (F.obj i) := hsep i
  have hqsep : q.Separable := (Polynomial.separable_map f).mp (by rwa [hq])
  rw [← hq]
  exact (IsSepClosed.splits_of_separable q hqsep).map f

end CommRingCat
