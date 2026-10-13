/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.FormalKernelGradedPieces
import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.AlgebraicGeometry.IdealModuleProductStalk

/-! # A product section determined by local representatives

Source: Stacks Project, Lemma 087Z and Section 0EHN.
(blueprint: lem-weil-pbc-formal-kernel-product-section).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- For two fixed sections, the local multiplication equations determine one output.
No linear map or compatibility between different pairs of inputs is asserted.
Source: Stacks Project, Lemma 087Z and Section 0EHN, the associated graded construction;
https://stacks.math.columbia.edu/tag/087Z.
(blueprint: lem-weil-pbc-formal-kernel-product-section).

Proof: On stalks, induct through the adjacent quotient isomorphisms of F. Reducing
level r+1 to level n+1 is quotient by I^(n+1): iterated quotients by nested ideal
powers agree with the quotient by the smaller power. Every transition is therefore
a sheaf epimorphism. Locally lift a to a' in I^m and the inclusion of x to t at
level m+n+1. If n>0, t reduces to zero at level n and thus belongs to I^n times
that level. If n=0, use I^0 F=F. Consequently a't belongs to I^(m+n) F and has a
unique preimage in the kernel K_(m+n); for m+n=0 use the identity inclusion.
Changing t by I^(n+1) F changes a't by I^(m+n+1) F=0. Changing a' by I^(m+1)
has the same effect, since t belongs to I^n F. Thus the local kernel preimages
agree on overlaps and glue by the sheaf axiom. On any smaller open, compare its
specified representatives with the restrictions of the original local ones;
independence and sheaf separation give the displayed equation. For uniqueness,
locally lift a and x around every point. Both proposed outputs have the same
image a't under the kernel inclusion, which is injective on sections. Sheaf
separation equates the outputs. On an empty open the cover is empty and separation
still applies. Zero degrees, the zero ideal, the unit ideal, and zero modules need
no exception to this argument. -/
theorem formalKernel_product_section_existsUnique {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I) (m n : ℕ) (U : X.Opens)
    (a : (formalAssociatedGradedPiece I m).val.obj (op U))
    (x : (formalKernelPiece F n).val.obj (op U)) :
    ∃! y : (formalKernelPiece F (m + n)).val.obj (op U),
      ∀ (V : X.Opens) (h : V ≤ U)
        (a' : (Scheme.idealSheafPower I.toModulesι m).1.val.obj (op V))
        (t : (F.obj.obj (op (m + n))).val.obj (op V)),
        (formalAssociatedGradedπ I m).val.app (op V) a' =
          (formalAssociatedGradedPiece I m).val.map (homOfLE h).op a →
        (F.obj.map (homOfLE (Nat.le_add_left n m)).op).val.app (op V) t =
          (formalKernelι F n).val.app (op V)
            ((formalKernelPiece F n).val.map (homOfLE h).op x) →
        (formalKernelι F (m + n)).val.app (op V)
          ((formalKernelPiece F (m + n)).val.map (homOfLE h).op y) =
            (@id Γ(X, V)
              ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op V) a')) • t := by sorry

end AlgebraicGeometry
