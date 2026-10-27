module

public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Algebra.Lie.Weights.Basic
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.RootSystem.Reduced
import Sheaf.Algebra.Lie.SplitSemisimpleRootDecomposition
import Mathlib.LinearAlgebra.RootSystem.BaseExists

/-!
# Rational opposition involution for a prescribed simple-root pinning

Source: Milne, Algebraic Groups (2017), Section 23h, printed p.508, with rational
descent by the generator relations on pp.503–504
(blueprint: lem-sfb-rational-opposition-involution).

Roots and coroots use the evaluation root pairing on the given abelian subalgebra.
Root spaces are ordinary simultaneous eigenspaces, `LieModule.weightSpace`.
The rational-field assertion is an agent-stated supporting assertion, rather than
a quotation of a rational-field theorem in Milne.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

namespace LieAlgebra

open Classical in
/-- A prescribed rational simple-root pinning admits a normalized opposition involution,
including the empty base.

Source: Milne, Algebraic Groups (2017), Section 23h, printed p.508; rational descent
using the generator relations on pp.503–504
(blueprint: lem-sfb-rational-opposition-involution).

Proof plan:
1. By `lem-sfb-split-semisimple-root-decomposition`, choose rational negative simple
   vectors `f i` with `[x i, f i] = P.coroot i`. The coroots here are the prescribed
   ones: the bracket line has a unique element evaluating to two. Apply
   `lem-sfb-root-base-rational-integral-spans` to the evaluation pairing and the given
   root basis. The simple coroots form a basis of `H`. If the base is empty, its basis
   makes the dual of `H` zero, hence `H` zero. There are no roots, and the decomposition
   makes `L` zero. Its identity automorphism satisfies the conclusion.
2. Otherwise apply `lem-sfb-pinned-serre-presentation-isomorphism` to the prescribed
   vectors and their normalized partners. It identifies `L` with the free rational Lie
   algebra on `H i`, `E i`, `F i`, modulo the displayed Serre relators, sending these
   generators to the simple coroots, `x i`, and `f i`.
3. On the free Lie algebra send `H i` to `-H i`, `E i` to `-F i`, and `F i` to `-E i`.
   Bilinearity and skew symmetry preserve the Cartan-Cartan relators, send the mixed
   relator `[E i,F j] - delta(i,j) H i` to its negative with indices exchanged, and
   interchange the Cartan-positive and Cartan-negative relators. A nested Serre
   relator of length `n+1` maps to `(-1)^(n+1)` times its opposite relator. Thus the
   inverse image of the relator ideal contains its generators and hence that ideal;
   the map descends. Its square fixes all generators, so it is involutive.
4. Conjugate by the presentation isomorphism to obtain `theta`. It sends `x i` to
   `-f i` and every simple coroot to its negative, hence acts by minus one on `H`.
   Applying it to `[h,z] = alpha(h) z` shows that it carries the alpha root space
   into the negative-alpha root space. Involutivity gives equality of the two
   spaces. Finally `[x i, -theta (x i)] = [x i, f i] = P.coroot i`.
-/
theorem exists_rational_opposition_involution
    (L : Type u) [LieRing L] [LieAlgebra ℚ L] [FiniteDimensional ℚ L]
    [HasTrivialRadical ℚ L] (H : LieSubalgebra ℚ L) [IsLieAbelian H]
    (hmax : ∀ A : LieSubalgebra ℚ L, H ≤ A → IsLieAbelian A → A = H)
    (hsplit : ∀ h : H, (⨆ a : ℚ, (ad ℚ L (h : L)).eigenspace a) = ⊤)
    (I : Type v) [Finite I] (P : RootPairing I ℚ (Module.Dual ℚ H) H)
    [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    (heval : ∀ (α : Module.Dual ℚ H) (h : H), P.toLinearMap α h = α h)
    (hdecomp : DirectSum.IsInternal
      (Sum.elim (fun _ : Unit ↦ H.toSubmodule)
        (fun i : I ↦ (LieModule.weightSpace L (P.root i)).toSubmodule)))
    (hdim : ∀ i : I, Module.finrank ℚ (LieModule.weightSpace L (P.root i)) = 1)
    (hcoroot : ∀ i : I, (P.coroot i : L) ∈ Submodule.span ℚ
      {z : L | ∃ a ∈ LieModule.weightSpace L (P.root i),
        ∃ b ∈ LieModule.weightSpace L (-P.root i), ⁅a, b⁆ = z})
    (Δ : Set I) (b : Module.Basis Δ ℚ (Module.Dual ℚ H))
    (hb : ∀ i : Δ, b i = P.root i)
    (hsign : ∀ i : I,
      P.root i ∈ AddSubmonoid.closure (P.root '' Δ) ∨
        -P.root i ∈ AddSubmonoid.closure (P.root '' Δ))
    (x : Δ → L) (hx : ∀ i : Δ, x i ∈ LieModule.weightSpace L (P.root i))
    (hxne : ∀ i : Δ, x i ≠ 0) :
    ∃ θ : L ≃ₗ⁅ℚ⁆ L,
      Function.Involutive θ ∧
      (∀ h : H, θ (h : L) = -(h : L)) ∧
      (∀ i : I,
        Submodule.map θ.toLinearEquiv.toLinearMap
          (LieModule.weightSpace L (P.root i)).toSubmodule =
            (LieModule.weightSpace L (-P.root i)).toSubmodule) ∧
      (∀ i : Δ, ⁅x i, -θ (x i)⁆ = (P.coroot i : L)) := by
  sorry

end LieAlgebra
