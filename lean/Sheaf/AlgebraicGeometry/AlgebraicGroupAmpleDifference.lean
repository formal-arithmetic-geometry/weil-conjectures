/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Monoidal.Grp
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import WeilConjectures.AlgebraicGeometry.AmpleTwistGlobalGeneration
import WeilConjectures.AlgebraicGeometry.AmplePositiveTensorPower
import WeilConjectures.AlgebraicGeometry.GlobalGenerationNonvanishingCover
import WeilConjectures.AlgebraicGeometry.TensorSectionAffineOpen

/-! # Invertible modules on algebraic groups are differences of ample modules

Source: Stacks Project, Groupoids, Tag 0BF7, lemma-algebraic-quasi-projective;
Morphisms, Tag 0FVC, lemma-invertible-add-enough-ample-very-ample.
(blueprint: lem-sfb-algebraic-group-ample-difference)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Every invertible module on a separated finite-type group scheme over a field
is the tensor product of an ample invertible module and the dual of another.
The dual is the existing internal Hom into the structure module. No properness,
smoothness, commutativity, connectedness, or symmetry assumption is made.

Source: Stacks Project, Groupoids, Tag 0BF7, lemma-algebraic-quasi-projective;
Morphisms, Tag 0FVC, lemma-invertible-add-enough-ample-very-ample.
(blueprint: lem-sfb-algebraic-group-ample-difference)

Proof plan, following the four steps of the node:
1. By lem-sfb-finite-type-group-ample-line, choose an absolutely ample invertible
   module M on H. Its ampleness includes quasi-compactness and affine nonvanishing
   neighbourhoods from sections of positive tensor powers.
2. The invertible module L is quasi-coherent and finite type, by its local frames
   (def-sc-invertible-module and pqf-def-coherent). Apply
   lem-weil-pbc-coherent-twist-global-generation and choose a sufficiently large
   natural number n so that F = L tensor M^n has finitely many generating global
   sections. It is invertible by tensoring local frames. Put B = M^(n+1) and
   A = M tensor F. Then B is ample by lem-sc-ample-positive-tensor-power.
3. At x choose a section s of M^r with r positive and affine nonvanishing locus
   containing x. By lem-sc-global-generation-nonvanishing-cover choose a global
   section t of F nonvanishing at x. The section s tensor t^r of A^r has affine
   nonvanishing locus H_s intersect H_(t^r), by lem-sc-tensor-section-affine-open.
   Together with quasi-compactness, this proves absolute ampleness of A by
   def-weil-pbc-ample-invertible-module.
4. Rearrange tensor factors to identify A with L tensor B. In local frames,
   evaluation identifies B tensor Hom(B,O_H) with O_H, sending b tensor b-dual
   to 1; its inverses agree on overlaps because a change of frame and its dual
   have reciprocal coefficients. Tensor cancellation gives A tensor B-dual
   isomorphic to L. Invert this isomorphism to obtain the asserted orientation.
   These are the sheaf tensor and dual of def-pur-sheaf-tensor-product and
   def-sc-invertible-module. -/
theorem exists_ample_tensor_dual_of_group
    (k : Type u) [Field k] (H : Over (Spec (CommRingCat.of k))) [GrpObj H]
    [IsSeparated H.hom] [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]
    (L : H.left.Modules) [L.IsInvertible] :
    ∃ (A B : H.left.Modules) (_ : A.IsInvertible) (_ : B.IsInvertible),
      IsAmple H.left A ∧ IsAmple H.left B ∧ Nonempty (L ≅ A ⊗ B.dual) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
