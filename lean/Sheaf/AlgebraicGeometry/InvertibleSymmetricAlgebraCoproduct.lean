/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Sheaf.CategoryTheory.CommAlgebraSheafModule
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-! # The homogeneous coproduct of a line bundle's symmetric algebra

Source: Stacks Project, Modules, Section 01CF; Schemes, Section 01LA (9); Tag 09MS.
(blueprint: lem-sc-invertible-symmetric-algebra-coproduct).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

/-- Multiplicative tensor-power maps to a locally symmetric algebra of a line bundle
are a coproduct cofan of module sheaves.

Source: Stacks Project, Modules, Section 01CF; Schemes, Section 01LA (9); Tag 09MS.
(blueprint: lem-sc-invertible-symmetric-algebra-coproduct).
Proof: Refine the affine cover by affine opens on which L has a frame e. The affine
comparison identifies B there with Sym(L(U)), hence with O(U)[T], sending j(e) to T.
The degree-zero and degree-one conditions and multiplicativity identify b_d(e^d) with
T^d. These identifications persist on smaller affine opens: the symmetric algebra
comparison is determined by the structure map and its values on degree one, so it
commutes with restrictions. The tensor powers have frames e^d, and polynomial modules
are direct sums of their monomials. A family of module-sheaf maps from L^d to any M
therefore extends locally to B by finite summation of coefficients times the images
of e^d. Sheafify the polynomial-module presheaf to extend to arbitrary opens, whose
sections need only be locally finite sums. On intersections the extensions agree,
since both send each b_d to the prescribed map and the local polynomial expansion
is unique. Sheaf gluing gives the global desc map. The same local calculation proves
its factorization through every b_d and uniqueness; these three facts define IsColimit.
No global direct-sum formula for sections is used. Empty opens have the unique map;
zero coefficients and degree zero are covered by the polynomial expansion. -/
theorem isColimit_invertible_symmetricAlgebra_cofan {X : Scheme.{u}}
    (L : X.Modules) [L.IsInvertible] (B : X.CommAlgebraSheaf)
    (j : L ⟶ commAlgebraSheafModule X.sheaf B)
    (b : ∀ d : ℕ, L.tensorPow d ⟶ commAlgebraSheafModule X.sheaf B)
    (hAffine : ∀ U : X.affineOpens,
      ∃ e : SymmetricAlgebra (X.presheaf.obj (op U.1)) (L.val.obj (op U.1)) ≃+*
          B.right.obj.obj (op U.1),
        (∀ r : X.presheaf.obj (op U.1),
          e (algebraMap (X.presheaf.obj (op U.1))
            (SymmetricAlgebra (X.presheaf.obj (op U.1)) (L.val.obj (op U.1))) r) =
            B.hom.hom.app (op U.1) r) ∧
        (∀ x : L.val.obj (op U.1),
          e (SymmetricAlgebra.ι (X.presheaf.obj (op U.1)) (L.val.obj (op U.1)) x) =
            j.val.app (op U.1) x))
    (hZero : ∀ (U : X.Opens) (r : Γ(X, U)),
      (b 0).app U (unitSectionsEquiv U r) = B.hom.hom.app (op U) r)
    (hOne : b 1 = (ρ_ L).hom ≫ j)
    (hMul : ∀ (U : X.Opens) (a d : ℕ) (s : Γ(L.tensorPow a, U))
      (t : Γ(L.tensorPow d, U)),
      (show B.right.obj.obj (op U) from (b a).app U s) *
        (show B.right.obj.obj (op U) from (b d).app U t) =
        (show B.right.obj.obj (op U) from
          (b (a + d)).app U ((L.tensorPowAddIso a d).inv.app U (tmulSection s t)))) :
    Nonempty (IsColimit (Cofan.mk (commAlgebraSheafModule X.sheaf B) b)) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
