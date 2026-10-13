/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.AlgebraicGeometry.FormalKernelGradedPieces

/-! # Bilinear multiplication on formal kernel pieces

Source: Stacks Project, Lemma 087Z and Section 0EHN.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Bilinear action maps on formal kernels, before imposing any algebra laws.
Source: Stacks Project, Lemma 087Z, its associated graded module construction,
and Section 0EHN; https://stacks.math.columbia.edu/tag/087Z.
(blueprint: lem-weil-pbc-formal-kernel-bilinear-action-exists).

Proof: Iterate the adjacent quotient identifications in the definition of a coherent
formal module. For r >= n, the transition from F_(r+1) to F_(n+1) is the quotient by
I^(n+1); for n > 0, its composite to F_n is the quotient by I^n. These descriptions
follow by induction, since taking a further quotient by I^n after a quotient by a
higher power gives the same quotient. In particular all transitions are sheaf epis.
Given a section x of K_n, locally lift its inclusion to t in F_(m+n+1), and locally
lift a coefficient in I^m/I^(m+1) to a in I^m. For n > 0, t maps to zero in F_n, so
it lies locally in I^n F_(m+n+1). The product a t reduces to zero in F_(m+n), and
therefore has a unique preimage in K_(m+n); in degree m+n=0 this is just a t.
Changing t by a section of I^(n+1)F_(m+n+1) changes a t by a section of
I^(m+n+1)F_(m+n+1), which is zero. Changing a by I^(m+1) has the same effect,
using t in I^n F_(m+n+1); when n=0 use I^0 F=F. The uniqueness in a kernel and
these independence statements glue the locally defined outputs, on overlaps and
on arbitrary opens. Addition and scalar multiplication commute with this procedure,
by taking simultaneous local lifts, giving linearity in each variable. The same local
calculation commutes with restrictions, proving naturality. Finally an already given
global lift can be used on each member of the local cover, so sheaf uniqueness proves
the formula for every lift. Empty opens and zero modules are covered by uniqueness;
no global surjectivity of a sheaf epimorphism on arbitrary opens is asserted. -/
theorem formalKernel_bilinear_action_exists {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I) :
    ∃ act : ∀ (m n : ℕ) (U : X.Opens),
      (formalAssociatedGradedPiece I m).val.obj (op U) →ₗ[Γ(X, U)]
        (formalKernelPiece F n).val.obj (op U) →ₗ[Γ(X, U)]
          (formalKernelPiece F (m + n)).val.obj (op U),
      (∀ (m n : ℕ) (U V : X.Opens) (h : V ≤ U)
        (a : (formalAssociatedGradedPiece I m).val.obj (op U))
        (x : (formalKernelPiece F n).val.obj (op U)),
      (formalKernelPiece F (m + n)).val.map (homOfLE h).op (act m n U a x) =
        act m n V ((formalAssociatedGradedPiece I m).val.map (homOfLE h).op a)
          ((formalKernelPiece F n).val.map (homOfLE h).op x)) ∧
      (∀ (m n : ℕ) (U : X.Opens)
          (a : (Scheme.idealSheafPower I.toModulesι m).1.val.obj (op U))
          (x : (formalKernelPiece F n).val.obj (op U))
          (t : (F.obj.obj (op (m + n))).val.obj (op U)),
          (F.obj.map (homOfLE (Nat.le_add_left n m)).op).val.app (op U) t =
            (formalKernelι F n).val.app (op U) x →
          (formalKernelι F (m + n)).val.app (op U)
            (act m n U ((formalAssociatedGradedπ I m).val.app (op U) a) x) =
              (@id Γ(X, U)
                ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op U) a)) • t) := by sorry

end AlgebraicGeometry
