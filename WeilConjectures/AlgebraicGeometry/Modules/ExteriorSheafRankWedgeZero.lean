/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Vanishing of a wedge with too many factors from a finite locally free sheaf

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
-/

@[expose] public section

universe v
open CategoryTheory Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- Wedging a full-rank tuple with an additional image from that sheaf gives zero.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph, lift independence
(blueprint: new-j1-exterior-sheaf-rank-wedge-zero).

Proof: Restrict to a trivializing cover of A and then to a common refinement with U.
There A has a basis of size r. Expand each of the r first entries and d in this basis.
Multilinearity expands the concatenated wedge into a finite sum of terms containing
r+1 images of basis vectors under f. Since there are only r basis vectors, two of
these entries coincide. Alternation makes every term zero, independently of the
remaining entries from B and the position j of the additional image. Naturality of
wedge sections and separatedness of the exterior sheaf imply zero on U. No exactness
or monomorphism assumption on f is needed. When r=0, A is locally zero, so d=0 and
one entry is zero. When s=0, there is no j and hence no assertion to check. The empty
scheme and the zero ring obey the same argument. The equality n=r+s only reindexes
this wedge and introduces no positivity assumption. -/
theorem exteriorSheaf_rank_wedge_eq_zero {X : Scheme.{v}} {A B : X.Modules}
    (f : A ⟶ B) (r n s : ℕ) (hr : n = r + s) [A.IsFiniteLocallyFreeOfRank r]
    (U : X.Opens) (a : Fin r → A.val.obj (op U))
    (c : Fin s → B.val.obj (op U)) (j : Fin s) (d : A.val.obj (op U))
    (hc : c j = f.val.app (op U) d) :
    exteriorSheafSection B n U
      (fun i ↦ Fin.append (fun k ↦ f.val.app (op U) (a k)) c (Fin.cast hr i)) = 0 := by sorry

end AlgebraicGeometry.Scheme.Modules
