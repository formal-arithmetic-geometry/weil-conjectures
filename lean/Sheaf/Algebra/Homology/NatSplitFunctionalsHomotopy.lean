/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Natural-degree deformation retract from split functionals

Source: Stacks Project, Algebra, Tag 00MT, the last three sentences of the proof.
(blueprint: lem-weil-pbc-nat-split-functionals-homotopy)
-/

@[expose] public section
universe u v
open CategoryTheory
namespace ChainComplex

/-- The kernel complement of two split functionals is a deformation retract.
Source: Stacks Project, Algebra, Tag 00MT, proof, the complementary spans.

Proof: Set `S_(j+1)=ker α`, `S_j=ker β`, and `S_k=C_k` elsewhere. Define
the complementary complex by restricting the differentials to these submodules.
The middle differential preserves the kernels by `hd`; the incoming one does
so by `hin`; the remaining codomains are full terms. Their composites vanish
because their inclusions are injective and the original composites vanish.
Define `r_(j+1)(x)=x-α(x)•z`, `r_j(x)=x-β(x)•w`, and `r_k(x)=x` elsewhere.
These maps land in the kernels by `hz` and `hw`. They commute with
differentials: for the incoming differential use `hin`, for the middle one
use `hd` and `hdz`, and for the outgoing one use `hout`. Inclusion `ι` and
`r` satisfy `rι=1` because the functionals vanish on their kernels.
Set the sole nonzero homotopy component, from degree `j` to `j+1`, to
`x ↦ -β(x)•z`. Its two nonzero homotopy equations say that `ιr-1` is
`-α(x)•z` at `j+1` and `-β(x)•w` at `j`, by `hd` and `hdz`; elsewhere
both sides vanish. Together with the zero homotopy for `rι=1`, this defines
the homotopy equivalence from the complement to `C`. The forward map is
the submodule inclusion in each degree and is therefore injective. Identify
the special terms with the two kernels, and the others with the full terms.
When `j=0` there is no outgoing nonzero differential: `C.d 0 0=0` by the
chain shape, so the same construction and equations apply at the boundary.
No finite bases or unit matrix coefficients are used in this construction.
(blueprint: lem-weil-pbc-nat-split-functionals-homotopy) -/
theorem exists_nat_homotopy_equiv_of_split_functionals
    {R : Type u} [CommRing R] (C : ChainComplex (ModuleCat.{max u v} R) ℕ)
    (j : ℕ) (α : C.X (j + 1) →ₗ[R] R) (β : C.X j →ₗ[R] R)
    (z : C.X (j + 1)) (w : C.X j)
    (hz : α z = 1) (hw : β w = 1)
    (hd : ∀ x, β ((C.d (j + 1) j).hom x) = α x)
    (hdz : (C.d (j + 1) j).hom z = w)
    (hin : ∀ x, α ((C.d (j + 2) (j + 1)).hom x) = 0)
    (hout : (C.d j (j - 1)).hom w = 0) :
    let S : ∀ i : ℕ, Submodule R (C.X i) := fun i ↦
      if h : i = j + 1 then h ▸ LinearMap.ker α
      else if h : i = j then h ▸ LinearMap.ker β else ⊤
    ∃ (C' : ChainComplex (ModuleCat.{max u v} R) ℕ)
      (g : ∀ i, C'.X i ≃ₗ[R] S i) (e : HomotopyEquiv C' C),
      ∀ i : ℕ, Function.Injective (e.hom.f i).hom := by
  sorry

end ChainComplex
