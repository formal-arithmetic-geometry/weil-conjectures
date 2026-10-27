module

public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra
import Sheaf.RingTheory.FiniteSubcomodule
import Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Faithful finite-dimensional representations of affine group schemes

Source: Milne, Algebraic Groups (2017), Theorem 4.9 and Corollary 4.10,
printed p.87, and Corollary 3.35, printed p.75.
(blueprint: lem-sfb-affine-group-faithful-linear-representation)

The general linear scheme and its matrix-valued point identification are the existing
constructions. Scalar extension uses the canonical pullback functor on schemes over the base.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- Every affine finite-type group scheme over a field has a closed faithful representation
of positive finite dimension, injective on all algebra-valued points and after field extension.
Source: Milne, Algebraic Groups (2017), Theorem 4.9 and Corollary 4.10, printed p.87;
Corollary 3.35, printed p.75.
(blueprint: lem-sfb-affine-group-faithful-linear-representation)

Proof:
1. By lem-sfb-affine-group-coordinate-hopf the coordinate algebra H = k[G] has its canonical
   Hopf structure. By lem-pc-affine-finite-type-algebra it is finitely generated over k,
   in the sense of def-weil-pbc-finite-type-algebra. Apply
   lem-sfb-comodule-finite-subcomodule to the regular coaction and the finite set consisting
   of 1 and algebra generators. Obtain a finite-dimensional subcomodule V containing that set.
2. Choose a finite basis using def-weil-finite-dimensional-subspace. Since the counit sends
   1 to 1, the vector 1 is nonzero and dim V = m is positive. Write the restricted coaction
   as c(e_j) = sum_i e_i tensor a_ij; tensor coordinate functionals give unique coefficients
   by def-weil-pbc-module-tensor-product.
3. The lem-sfb-rational-representation-comodule-dictionary produces the group-scheme map
   rho to the existing GL_m of def-sc-general-linear-group. On every R-point x its matrix
   is (x(a_ij)). Evaluating at the universal H-point, as in def-weil-affine-spectrum,
   shows that the coordinate pullback sends x_ij to a_ij.
4. Applying counit tensor identity to Delta(e_j) gives e_j = sum_i epsilon(e_i) a_ij.
   Thus the image of the coordinate pullback contains V and all algebra generators of H.
   By def-weil-pbc-finite-type-algebra it is surjective.
5. By lem-weil-pbc-closed-immersion-affine-cover-criterion on the single whole affine target,
   this coordinate surjection makes rho a closed immersion.
6. Points are algebra maps by def-weil-affine-spectrum. Precomposition with a surjection is
   injective: lift any h in H to a coordinate b and evaluate two maps at b. This includes
   nonreduced R and the zero ring. By lem-weil-pbc-fibre-product-affine-spectra the coordinate
   map after extension K/k is its tensor extension. It is still surjective: lift each first
   factor in a finite sum of pure tensors, using
   lem-weil-pbc-algebra-tensor-pushout-universal-property. The same argument proves injectivity
   on every K-algebra point of the pullback. No geometric regularity hypothesis is used.
-/
theorem exists_closedImmersion_generalLinearGroup
    {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]
    [IsAffine G.left] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    ∃ (m : ℕ) (_ : 1 ≤ m) (ρ : G ⟶ GeneralLinearGroup (LinearGroupSchemes.Index.{u} m) k),
      IsMonHom ρ ∧ IsClosedImmersion ρ.left ∧
      (∀ (A : Type u) [CommRing A] [Algebra k A],
        Function.Injective (fun x : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G ↦
          GeneralLinearGroup.homMulEquiv (LinearGroupSchemes.Index.{u} m) k A (x ≫ ρ))) ∧
      ∀ (K : Type u) [Field K] [Algebra k K]
        (A : Type u) [CommRing A] [Algebra K A],
        Function.Injective
          (fun x : (Spec (.of A)).asOver (Spec (.of K)) ⟶
              (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G ↦
            x ≫ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map ρ) := by
  sorry

end AlgebraicGeometry
