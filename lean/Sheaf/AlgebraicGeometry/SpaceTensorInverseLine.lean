/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q155
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceCommAlgebraSheaf
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Tensor inverses detect line modules on algebraic spaces

Source: Stacks Project, Modules on Sites, Tags 0B8N and 0B8Q
(blueprint: lem-sfb-space-tensor-inverse-line).

The tensor is the existing sectionwise tensor followed by module sheafification.
The conclusion uses the existing local-triviality predicate on the small etale site.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- An inverse for the sheaf tensor makes both factors line modules, without any
finite-presentation hypothesis.

Source: Stacks Project, Modules on Sites, Tag 0B8N, equivalence (1)-(2), and
Tag 0B8Q, the locally ringed converse, applied to the small etale structure sheaf
(blueprint: lem-sfb-space-tensor-inverse-line).

Proof:
1. Fix an etale object U and an isomorphism psi from the tensor to the structure
   module. Use lem-sfb-localized-site-tensor-restriction to identify its restriction
   to every slice with the tensor of the restrictions, preserving pure tensors.
2. By lem-weil-pbc-site-sheafification-sections-local and
   lem-pc-sites-sheafification-underlying-sets, locally psi-inverse(1) is represented
   by an ordinary tensor, hence a finite sum of pure tensors x_i tensor y_i. Pad
   the zero expression if needed. Thus the functions a_i = psi(x_i tensor y_i)
   sum to 1. This uses the sheafification construction of the tensor product.
3. At every point of the scheme U, some a_i has a unit germ, since otherwise
   their sum belongs to the maximal ideal. Represent the inverse germ on a
   Zariski neighbourhood and shrink until a_i is invertible there. These opens
   are etale by lem-weil-pbc-open-immersion-etale and cover U. Normalize x_i by
   a_i-inverse to obtain x,y with psi(x tensor y) = 1. For an empty chart the
   empty covering suffices.
4. On the resulting slice define f(a) = a x and g(m) = psi(m tensor y),
   sectionwise. They commute with restrictions and are linear, and gf = id.
   The endomorphism fg is an automorphism: insert psi-inverse(1), interchange
   the two M factors, and evaluate with psi, using the associators, symmetry
   and unitors of lem-pc-sheaf-modules-tensor-closed. This composite sends m
   to x psi(m tensor y). Since (fg)^2 = fg, invertibility gives fg = id.
   Thus f and g trivialize M on the slice.
5. Apply the same construction to N,M and psi composed with the symmetry.
   It gives inverse maps a to a y and n to psi(x tensor n), trivializing N
   on the same cover. As U was arbitrary, both existing IsLineModule
   predicates hold. No step assumes finite presentation. -/
theorem isLineModule_of_tensor_inverse
    {S : Scheme.{u}} (X : AlgebraicSpace S) (M N : X.Modules)
    (h : Nonempty
      ((SheafOfModules.siteSheafTensorRight (A := X.commStructureSheaf) N).obj M ≅
        SheafOfModules.unit X.structureSheaf)) :
    X.IsLineModule M ∧ X.IsLineModule N := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
