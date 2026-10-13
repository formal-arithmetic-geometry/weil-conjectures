/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.FormalKernelGradedPieces

/-! # Products of formal kernel representatives

Source: Stacks Project, Lemma 087Z and Section 0EHN.
(blueprint: lem-weil-pbc-formal-kernel-representative-product).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Multiplication of actual representatives lands in the successive kernel and is
independent of the representatives. This statement neither lifts arbitrary quotient
sections nor glues local products.
Source: Stacks Project, Lemma 087Z (lemma-finite-over-rees-algebra), associated graded
construction, and Section 0EHN, equation 0880.
(blueprint: lem-weil-pbc-formal-kernel-representative-product).

Proof: On each stalk the adjacent formal quotient identifications, iterated through
nested ideal powers, identify the reduction from level m+n+1 to level n+1 with
quotient by I^(n+1). For n>0, the reduction of t belongs to the adjacent kernel,
so t belongs to I^n times the top level; for n=0 this is automatic. The coefficient
belongs to I^m. Their product belongs to I^(m+n) times the top level, which is the
kernel of the adjacent reduction when m+n>0. The sectionwise kernel universal
property gives its preimage. When m+n=0 the inclusion is the identity.
If b and a have the same quotient class, b-a lies stalkwise in I^(m+1). If s and t
have the same reduction, s-t lies in I^(n+1) times the top level. Expand
b s - a t = (b-a)t + b(s-t). Both summands belong to I^(m+n+1) times that level,
which is zero by the formal annihilation condition. Equality on stalks gives the
section equality, including on the empty open by sheaf separation. This covers
zero degrees and the zero and unit ideals without additional hypotheses. -/
theorem formalKernel_representative_product {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I) (m n : ℕ) (U : X.Opens)
    (a : (Scheme.idealSheafPower I.toModulesι m).1.val.obj (op U))
    (x : (formalKernelPiece F n).val.obj (op U))
    (t : (F.obj.obj (op (m + n))).val.obj (op U))
    (ht : (F.obj.map (homOfLE (Nat.le_add_left n m)).op).val.app (op U) t =
      (formalKernelι F n).val.app (op U) x) :
    (∃ y : (formalKernelPiece F (m + n)).val.obj (op U),
      (formalKernelι F (m + n)).val.app (op U) y =
        (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op U) a)) • t) ∧
    (∀ (b : (Scheme.idealSheafPower I.toModulesι m).1.val.obj (op U))
      (s : (F.obj.obj (op (m + n))).val.obj (op U)),
      (formalAssociatedGradedπ I m).val.app (op U) b =
        (formalAssociatedGradedπ I m).val.app (op U) a →
      (F.obj.map (homOfLE (Nat.le_add_left n m)).op).val.app (op U) s =
        (formalKernelι F n).val.app (op U) x →
      (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op U) b)) • s =
        (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op U) a)) • t) :=
  by sorry

end AlgebraicGeometry
