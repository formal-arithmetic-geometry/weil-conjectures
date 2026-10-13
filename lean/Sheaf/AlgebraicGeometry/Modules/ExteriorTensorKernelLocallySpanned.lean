/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Local generators of an exterior tensor quotient kernel

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
-/

@[expose] public section

universe v
open CategoryTheory Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- A section killed by an exterior tensor quotient is locally a linear combination of
pure wedge tensors with an argument in the image of the first map.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph; step 1 and the
finite-germ representation part of step 2 of `new-j1-exterior-tensor-kernel-relations`.
(blueprint: lem-sc-exterior-tensor-kernel-locally-spanned).

Proof: Fix a point x. Exactness on stalks identifies C_x with B_x/im(f_x). Present
exterior powers by their alternating multilinear generators and relations. Quotienting
B_x by im(f_x) adds precisely the relations that wedges with an argument in im(f_x)
vanish: multilinearity expands changes of representatives into these relations, so
the resulting quotient has the universal property of the exterior power of C_x.
Tensoring with the exterior power of A_x is right exact. Pure wedges span this first
factor, so the tensor kernel is spanned by the displayed pure wedge tensors. Exterior
powers and tensor products commute with stalks, since their presentations use finite
sums and finite tuples and commute with filtered colimits and scalar extension.
The formula for q identifies its stalk map with this quotient map. Express the germ
of t as a finite linear combination of these generators. Represent the finitely many
coefficients, wedge entries, and preimages under f_x on one common neighborhood V of
x contained in U. Shrink V to make every equation c_j=f(d) hold for sections, and
shrink once more to make the linear combination equal to the restriction of t.
The resulting equality proves membership in the displayed span. The assumption
s ≠ 0 excludes the degree-zero isomorphism case, handled separately by the caller.
For r=0 the empty wedge generates the first factor. At a zero stalk ring all modules
are zero; on an empty open there are no points to check. -/
theorem exteriorTensor_kernel_locally_mem_span {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (A : X.Modules) (r s : ℕ) (hs : s ≠ 0)
    (q : exteriorSheaf A r ⊗ exteriorSheaf S.X₂ s ⟶
      exteriorSheaf A r ⊗ exteriorSheaf S.X₃ s)
    (hq : ∀ (U : X.Opens) (a : Fin r → A.val.obj (op U))
      (c : Fin s → S.X₂.val.obj (op U)),
      q.val.app (op U)
        (tmulSection (exteriorSheafSection A r U a)
          (exteriorSheafSection S.X₂ s U c)) =
        tmulSection (M := exteriorSheaf A r) (N := exteriorSheaf S.X₃ s)
          (exteriorSheafSection A r U a)
          (exteriorSheafSection S.X₃ s U (fun i ↦ S.g.val.app (op U) (c i))))
    (U : X.Opens)
    (t : (exteriorSheaf A r ⊗ exteriorSheaf S.X₂ s).val.obj (op U))
    (ht : q.val.app (op U) t = 0) (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      (exteriorSheaf A r ⊗ exteriorSheaf S.X₂ s).val.map (homOfLE hVU).op t ∈
        Submodule.span (X.presheaf.obj (op V))
          {z | ∃ (a : Fin r → A.val.obj (op V))
            (c : Fin s → S.X₂.val.obj (op V)) (j : Fin s)
            (d : S.X₁.val.obj (op V)), c j = S.f.val.app (op V) d ∧
              z = tmulSection (M := exteriorSheaf A r) (N := exteriorSheaf S.X₂ s)
                (exteriorSheafSection A r V a)
                (exteriorSheafSection S.X₂ s V c)} := by sorry

end AlgebraicGeometry.Scheme.Modules
