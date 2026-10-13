/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule

/-! # The affine part of torsion-controlled algebraization

Source: Stacks Project, Tag 0889(1), affine paragraph, using Tags 087W, 0ALK and 05EU.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Algebraization on a single affine scheme. Descent to a nonaffine scheme is not
part of this assertion.

Source: Stacks Project, Tag 0889(1), affine paragraph, using Tags 087W, 0ALK and 05EU.
(blueprint: lem-weil-pbc-torsion-controlled-affine-algebraization).

Proof: Identify X with Spec A via its canonical affine isomorphism. Coherent sheaves
correspond to finite A-modules. The affine formal-module equivalence identifies N
with a finite completed module M' and completion H with completion of the finite
module P of sections of H. Remark 0888 transfers the componentwise bound to the
kernel and cokernel of the map M' to completion P. Completion of P is its tensor
product with the completed ring. The completion ring map is flat and induces an
isomorphism modulo J, so apply the map-to part of formal-gluing Lemma 0ALK.
It yields a module T, a map T to P, and a compatible completed isomorphism, with
ideal-power-torsion kernel and cokernel. At each generator f of J, localization
kills that kernel and cokernel, so T_f is isomorphic to the finite module P_f.
Its completed scalar extension is M', also finite. The finiteness criterion of
Remark 05EU therefore makes T finite. Over the Noetherian ring A the
kernel and cokernel are finite. Choose finitely many generators of each and take
the maximum of their annihilating exponents and 1. This gives one positive bound.
Sheafify T and the map, and transport the completed isomorphism back through the
affine equivalence; compatibility gives the displayed factorization. If J is the
unit ideal, take T=P and the identity map; if J is zero, completion is the identity
and the original map provides the triple. The zero ring causes no exception. -/
theorem torsionControlled_affine_algebraization
    {X : Scheme.{u}} [IsNoetherian X] [IsAffine X] (J : X.IdealSheafData)
    (H : CoherentModules X) (N : CoherentFormalModule X J)
    (δ : N ⟶ (completion X J).obj H)
    (htorsion : ∃ t : ℕ, 1 ≤ t ∧ ∀ e : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2
        (kernel (δ.hom.app (op e)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2
        (cokernel (δ.hom.app (op e))))) :
    ∃ (F : CoherentModules X) (a : F ⟶ H) (β : N ≅ (completion X J).obj F),
      δ = β.hom ≫ (completion X J).map a ∧
      (∃ s : ℕ, 1 ≤ s ∧
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
          (kernel a.hom)) ∧
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
          (cokernel a.hom))) := by sorry

end AlgebraicGeometry
