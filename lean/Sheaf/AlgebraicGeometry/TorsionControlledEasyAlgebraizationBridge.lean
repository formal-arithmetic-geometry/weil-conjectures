/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule

/-! A bridge from componentwise annihilation to torsion-controlled algebraization.
Source: Stacks Project, Tag 0889(1), after Remark 0888.
(blueprint: new-stage3-torsion-controlled-easy-algebraization-bridge).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The affine componentwise annihilation condition is sufficient for a
    torsion-controlled coherent algebraization.

Source: Stacks Project, Tag 0889(1), construction after Remark 0888
(blueprint: new-stage3-torsion-controlled-easy-algebraization-bridge).

Proof: apply the affine algebraization construction on a finite affine cover.
Remark 0888 identifies the componentwise annihilation hypothesis with the
annihilation of the inverse-limit kernels and cokernels on each affine. The
finite-module lifting theorem then supplies local maps whose completions agree
with `δ`; formal gluing makes these maps compatible on overlaps. Glue the local
finite modules and maps to obtain `F` and `a`. The local annihilation bounds have
a common positive upper bound, which annihilates the coherent kernel and
cokernel of `a` globally, and the glued completed identifications give `β` and
the stated factorization. -/
theorem torsionControlled_easy_algebraization_bridge
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
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
        (cokernel a.hom))) := by
  sorry

end AlgebraicGeometry
