/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.GroupTheory.Index
public import WeilConjectures.Mathlib.RingTheory.Henselian

/-! # Fixed rings of a strict local root algebra

Source: Stacks Project, Tags 0EYG and 09EV, intermediate-root calculation.
(blueprint: lem-sbc-strict-local-root-invariants)
-/

@[expose] public section

universe u
set_option autoImplicit false

namespace AlgebraicGeometry.Scheme

/-- The endomorphism of a root algebra sending its root to `zeta * root`.
Its construction is polynomial evaluation, with no choice of algebra data.
Source: Stacks Project, Tag 09EV, cyclic intermediate-root calculation.
(blueprint: lem-sbc-strict-local-root-invariants) -/
noncomputable def rootRotation (H : Type u) [CommRing H] (h : H) (n : ℕ)
    (ζ : rootsOfUnity n H) :
    AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h) →ₐ[H]
      AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h) :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _)
    (algebraMap H _ ((ζ : Hˣ) : H) * AdjoinRoot.root _) (by
      have hz := (mem_rootsOfUnity' n (ζ : Hˣ)).mp ζ.property
      have ht := AdjoinRoot.eval₂_root
        ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h)
      have ht' : AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h) ^ n =
          algebraMap H _ h := by
        simpa [sub_eq_zero, ← AdjoinRoot.algebraMap_eq] using ht
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, mul_pow, ← map_pow, hz, map_one, one_mul, ht']
      exact sub_self _)

/-- The actual fixed subalgebra for a subgroup of the root rotations.
Source: Stacks Project, Tag 09EV, intermediate subextensions.
(blueprint: lem-sbc-strict-local-root-invariants) -/
noncomputable def rootFixedAlgebra (H : Type u) [CommRing H] (h : H) (n : ℕ)
    (K : Subgroup (rootsOfUnity n H)) :
    Subalgebra H (AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h)) :=
  ⨅ ζ : K, AlgHom.equalizer (rootRotation H h n ζ.val) (AlgHom.id H _)

/-- A subgroup of the root rotations has an intermediate root algebra as its fixed ring.

Source: Stacks Project, Tag 0EYG, final intermediate-field paragraph, and Tag 09EV.
(blueprint: lem-sbc-strict-local-root-invariants)

Proof: Hensel lifting of the simple residue roots of X^n-1 gives all n roots in H.
They form a cyclic group of order n. For a subgroup K let r be its order and e its
index. Lagrange gives r*e=n, e>0 and e dividing n. The monic relation gives the
H-basis 1,t,...,t^(n-1) of C. A generator zeta of K acts on t^i by zeta^i.
If r does not divide i, zeta^i-1 has nonzero residue and is a unit in H, so the
coefficient of t^i in an invariant must vanish. The invariants therefore have
basis 1,t^r,...,t^((e-1)*r). Evaluation s at t^r defines a map H[s]/(s^e-h)
to C^K, since (t^r)^e=h. It carries the standard monic basis bijectively to the
displayed invariant basis and is thus an H-algebra isomorphism. Invert it for
the orientation below. For n=1 and for the trivial subgroup this is the whole
root algebra; for the full subgroup it is H, via H[s]/(s-h). -/
theorem strict_local_root_invariants
    (H : Type u) [CommRing H] [IsStrictlyHenselianLocalRing H]
    (h : H) (n : ℕ) (hn : 0 < n ∧ IsUnit (n : H))
    (K : Subgroup (rootsOfUnity n H)) :
    0 < K.index ∧ K.index ∣ n ∧
      Nonempty (rootFixedAlgebra H h n K ≃ₐ[H]
        AdjoinRoot ((Polynomial.X : Polynomial H) ^ K.index - Polynomial.C h)) := by sorry

end AlgebraicGeometry.Scheme
