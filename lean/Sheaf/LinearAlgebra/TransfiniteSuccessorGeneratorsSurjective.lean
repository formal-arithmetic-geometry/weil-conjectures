module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.SetTheory.Ordinal.Basic

/-!
# Successor generators of a continuous transfinite filtration

Source: Stacks Project, Algebra, Tag 058V, `lemma-direct-sum-devissage`,
proof identifying the images of the partial sum maps by transfinite induction,
generalized to arbitrary successor-generating maps.
(blueprint: lem-trf-transfinite-successor-generators-surjective)
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

namespace Module

/-- Successor generators generate every stage of a continuous transfinite filtration.

Source: Stacks Project, Algebra, Tag 058V, `lemma-direct-sum-devissage`, proof
lines 20417–20433, with arbitrary successor-generating maps.
(blueprint: lem-trf-transfinite-successor-generators-surjective)

The canonical map is `DirectSum.toModule` of the successor maps followed by the
submodule inclusions into `X`, hence is the sum of their values over finite support.
The set in the image is precisely the partial direct sum `D_β`, expressed by
vanishing of all coordinates with index at least `β`. No injectivity is assumed.

Proof:
1. By `def-weil-pbc-direct-sum-modules`, every input has finite support. If its
   coordinates vanish at indices at least `β`, each supported index `α` satisfies
   `α + 1 ≤ β`. Monotonicity puts its image in `F β`; closure under finite sums
   gives the forward containment, including the empty-support case.
2. Prove the reverse containment by transfinite induction on `β ≤ κ`. At zero,
   every coordinate of an input in `D_0` vanishes, and `F 0 = 0` by hypothesis.
3. At `β = γ + 1`, write `x = y + t γ b` using the successor hypothesis.
   Induction lifts `y` to `a` in `D_γ`. Add the canonical inclusion of `b` into
   the `γ`-th summand, as in `def-weil-pbc-direct-sum-modules`. The resulting
   input lies in `D_β` and maps to `x`, without any uniqueness requirement.
4. At a nonzero limit, continuity puts `x` in some earlier `F γ`. The inductive
   preimage in `D_γ` also belongs to `D_β`, since the coordinate vanishing
   condition is preserved as the bound increases. No infinite sum is taken.
5. These cases exhaust all ordinals. The two containments give the asserted
   equality at every stage. At `κ`, every coordinate index is strictly below
   `κ`, so `D_κ` is the entire direct sum. If `F κ = ⊤`, equality at this
   stage says that the canonical map is surjective.
-/
theorem directSum_toModule_image_of_filtration_successor_generators
    (R : Type u) [CommRing R] (X : Type v) [AddCommGroup X] [Module R X]
    (κ : Ordinal.{w}) (F : Set.Iic κ → Submodule R X) (hmono : Monotone F)
    (A : Set.Iio κ → Type z) [∀ α, AddCommGroup (A α)] [∀ α, Module R (A α)]
    (t : ∀ α : Set.Iio κ,
      A α →ₗ[R] F ⟨Order.succ α.val,
        Order.succ_le_of_lt (a := α.val) (b := κ) α.property⟩)
    (hzero : F ⟨0, (bot_le : (0 : Ordinal.{w}) ≤ κ)⟩ = ⊥)
    (hcont : ∀ μ : Set.Iic κ, Order.IsSuccLimit μ.val →
      (F μ : Set X) = ⋃ (β : Set.Iic κ) (_ : β < μ), (F β : Set X))
    (hgen : ∀ (α : Set.Iio κ)
      (x : F ⟨Order.succ α.val,
        Order.succ_le_of_lt (a := α.val) (b := κ) α.property⟩),
      ∃ (y : F ⟨α.val, le_of_lt (a := α.val) (b := κ) α.property⟩) (a : A α),
        (x : X) = (y : X) + (t α a : X)) :
    (∀ β : Set.Iic κ,
      (DirectSum.toModule R (Set.Iio κ) X
        (fun α ↦ (F ⟨Order.succ α.val,
          Order.succ_le_of_lt (a := α.val) (b := κ) α.property⟩).subtype.comp (t α))) ''
        {a : DirectSum (Set.Iio κ) A | ∀ α : Set.Iio κ, β.val ≤ α.val → a α = 0} =
        (F β : Set X)) ∧
      (F ⟨κ, le_refl κ⟩ = ⊤ →
        Function.Surjective (DirectSum.toModule R (Set.Iio κ) X
          (fun α ↦ (F ⟨Order.succ α.val,
            Order.succ_le_of_lt (a := α.val) (b := κ) α.property⟩).subtype.comp (t α)))) := by
  sorry

end Module
