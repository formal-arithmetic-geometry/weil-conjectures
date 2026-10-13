/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule

/-! # Quasi-coherent candidate from affine formal gluing

Source: Stacks Project, Tags 0889(1), 0ALK(1) and 0888.
(blueprint: lem-weil-pbc-torsion-controlled-affine-candidate).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Formal gluing constructs a quasi-coherent candidate, without a finiteness assertion.

Source: Stacks Project, Tag 0889(1), affine construction using 0ALK(1), 087W and 0888.
(blueprint: lem-weil-pbc-torsion-controlled-affine-candidate).

Proof: identify X with Spec A by its canonical affine isomorphism and let I be J's
ideal of global sections. Under 087W, N corresponds to a finite completed module Q,
and H to a finite A-module P. The tensor comparison for finite P identifies the
formal map with Q -> S tensor P, where S is the I-adic completion. Remark 0888
transfers the given bound to its kernel and cokernel. The map A -> S is flat,
I is finitely generated, and A/I -> S/IS is an isomorphism. Apply 0ALK(1) to obtain
T -> P and Q isomorphic to S tensor T. Its kernel and cokernel are canonically
isomorphic as A-modules to those of the formal map, so the same positive power
of I kills them. Sheafify T and this map. Exactness of tilde and the affine
ideal-product formula give the asserted sheaf annihilation.

For each positive n the completion ring map gives A/I^n isomorphic to S/I^n S.
Consequently T/I^n T is naturally isomorphic to (S tensor T)/I^n(S tensor T),
without requiring T to be finite. Compose with the quotients of Q and the
reconstruction isomorphism of 087W to give beta. These quotient comparisons
commute with all reductions and with the glued map, hence form an isomorphism
of inverse systems and satisfy the factorization. This argument does not use
finiteness of T. When I is the unit ideal, take T=P and the identity; when I=0,
use the original module map since the completion ring is A. The zero ring and
empty spectrum satisfy the same formulas. -/
theorem torsionControlled_affine_candidate
    {X : Scheme.{u}} [IsNoetherian X] [IsAffine X] (J : X.IdealSheafData)
    (H : CoherentModules X) (N : CoherentFormalModule X J)
    (δ : N ⟶ (completion X J).obj H)
    (htorsion : ∃ t : ℕ, 1 ≤ t ∧ ∀ e : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2
        (kernel (δ.hom.app (op e)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2
        (cokernel (δ.hom.app (op e))))) :
    ∃ (F : X.Modules) (_ : F.IsQuasicoherent) (a : F ⟶ H.obj)
      (β : N.obj ≅ (formalCompletionFunctor J).obj F),
      δ.hom = β.hom ≫ (formalCompletionFunctor J).map a ∧
      (∃ s : ℕ, 1 ≤ s ∧
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
          (kernel a)) ∧
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
          (cokernel a))) := by sorry

end AlgebraicGeometry
