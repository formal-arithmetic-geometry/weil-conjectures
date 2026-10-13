/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.RingTheory.GRing
public import Sheaf.RingTheory.PthRootAlgebraLocal
public import Mathlib.RingTheory.Kaehler.Basic

/-! # Cotangent dimensions of a geometrically regular p-root extension

Source: Stacks Project, More on Algebra, Tag 07E5, proof of (2) ⇒ (4).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

/-- Independent coefficient differentials make the p-root quotient a regular base
change of the same local dimension. Its residue extension is finite and its
cotangent dimension equals that of the lower local ring after residue extension.

Source: Stacks Project, More on Algebra, Tag 07E5, proof of (2) ⇒ (4), construction
of k' and A'; Algebra, Tags 07DZ and 00ON, and the regular-local dimension criterion.
(blueprint: lem-weil-pbc-pth-root-cotangent-dimension).

Proof: Adjoin p-th roots of the n coefficients in an algebraic closure of k.
Independence of their differentials gives degree p^n by 07DZ. The polynomial
quotient over k is spanned by the p^n reduced monomials and surjects onto this
field, so comparing dimensions makes it isomorphic to that field. Taking p-th
powers of reduced polynomials shows the extension is purely inseparable. Tensor
the presentation with A to identify B with A tensor_k k'. The trivial extension
in geometric regularity makes A regular (use a universe lift of k if required).
The extension k'/k makes B regular. The base-change locality theorem supplies a
finite free map A -> B, a finite residue extension L/K, and a zero-dimensional
closed fibre. The flat height formula 00ON gives dim B = dim A. The regular-local
criterion identifies each dimension with the finrank of its cotangent space.
Scalar extension K -> L preserves the finrank of the finite-dimensional lower
cotangent space, giving the displayed equality. For n = 0 the extension is k
itself and B is the identity quotient; both assertions still hold. No finiteness
of absolute differentials is asserted or used. -/
theorem pthRoot_cotangent_dimension
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [IsNoetherianRing A] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hA : IsGeometricallyRegular k A) (n : ℕ) (a : Fin n → k) :
    letI := ZMod.algebra k p
    letI := ((algebraMap k A).comp (algebraMap (ZMod p) k)).toAlgebra
    let B := pthRootAlgebra p n A (fun i ↦ algebraMap k A (a i))
    ∀ [IsLocalRing B] [IsLocalHom (algebraMap A B)],
    LinearIndependent k (fun i ↦ KaehlerDifferential.D (ZMod p) k (a i)) →
    let K := IsLocalRing.ResidueField A
    let L := IsLocalRing.ResidueField B
    Module.Finite K L ∧
      Module.finrank L (L ⊗[K] IsLocalRing.CotangentSpace A) =
        Module.finrank L (IsLocalRing.CotangentSpace B) := by
  sorry

end Algebra
