/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafWedgeMapExists
import Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeQuotientFactor

/-!
# The wedge of lifts annihilates the quotient kernel

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- The wedge map on the sheaf of lifts annihilates the exterior quotient kernel.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph
(blueprint: new-determinant-lift-wedge-kernel).

Proof: Sectionwise send a tensor of wedges to the concatenated wedge of the images
under `S.f` and the second tuple. Exterior multiplication is alternating separately
in these tuples, so the exterior-power and tensor universal properties give a linear
map. The formula commutes with restrictions; sheafification gives `w`. The formula
for `q` determines it on local generators, so it is the tensor of the identity with
the exterior-power map of `S.g`. Locally trivialize `S.X₁`. Exactness identifies the
kernel of `S.g` with the image of `S.f`. The exterior quotient has kernel generated
by wedges with a factor from that image: algebraically exterior powers commute with
quotients, and the relations for the quotient exterior power are precisely wedges
containing such a factor. This description applies after sheafification, since
finite tuples in the quotient lift locally. Every such term, after wedging with
`r₁` first-term factors, contains `r₁ + 1` factors from a free module of rank `r₁`.
Expand them in a local basis; each term has a repeated basis vector and vanishes by
alternation. Hence the composite of the kernel inclusion with `w` is locally zero,
and separatedness makes it zero globally. Degree zero in the second factor gives
an identity quotient and zero kernel; rank zero in the first factor gives `S.f = 0`
and `S.g` an isomorphism, with the same conclusion. -/
theorem determinant_liftWedge_kernel_exists {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁]
    (q : exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₂ r₃ ⟶
      exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃)
    (hq : ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
      (c : Fin r₃ → S.X₂.val.obj (op U)),
      q.val.app (op U)
          (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
            (exteriorSheafSection S.X₂ r₃ U c)) =
        tmulSection (M := exteriorSheaf S.X₁ r₁) (N := exteriorSheaf S.X₃ r₃)
          (exteriorSheafSection S.X₁ r₁ U a)
          (exteriorSheafSection S.X₃ r₃ U (fun i ↦ S.g.val.app (op U) (c i)))) :
    ∃ w : exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₂ r₃ ⟶ exteriorSheaf S.X₂ r₂,
      kernel.ι q ≫ w = 0 ∧ ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
        (c : Fin r₃ → S.X₂.val.obj (op U)),
        w.val.app (op U)
            (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
              (exteriorSheafSection S.X₂ r₃ U c)) =
          exteriorSheafSection S.X₂ r₂ U
            (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i)) := by
  obtain ⟨w, hw⟩ := exteriorSheaf_wedgeMap_exists S.f r₁ r₃ r₂ hr
  obtain ⟨φ, hφ⟩ := determinant_wedge_quotient_factor S hS r₁ r₂ r₃ hr q w hq hw
  refine ⟨w, ?_, hw⟩
  rw [← hφ, ← Category.assoc, kernel.condition, zero_comp]

end AlgebraicGeometry.Scheme.Modules
