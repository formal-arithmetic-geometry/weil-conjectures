/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P5
-/
module

public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-! # Cech recovery in a triangulated class closed under products

Source: steps 1 and 7--9 of lem-sfb-supported-hull-proetale-descent, using the
coherent augmented Cech model and the short-exact-complex triangle.
(blueprint: lem-sfb-proetale-cech-product-class-recovery).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A replete triangulated class closed under products recovers a module from
coinduced restrictions on the qcqs refinements of an affine pro-etale cover.
The hypothesis on refinements includes the finite Cech intersections, which need
not themselves be affine or weakly contractible. This theorem concerns an arbitrary
class P and makes no assertion that inverse image or direct image preserves a hull.

Source: steps 1 and 7--9 of lem-sfb-supported-hull-proetale-descent, and the
coherent augmented Cech pushforward model (Stacks sites-cohomology.tex, Tag 03FC).
(blueprint: lem-sfb-proetale-cech-product-class-recovery)

Proof: for the empty scheme all modules are zero, so use triangulated zero and
repleteness. Otherwise choose a finite affine refinement of the given covering.
Replacing the refinement members by their original affine U_i still covers, as
the finite refinement on every affine test continues to refine the larger family.
Retain this finite list. Its iterated fibre products over V and all their projections
are qcqs and weakly etale. Apply the coherent Cech pushforward-model theorem with
f the identity. The resulting nonnegative bicomplex has total isomorphic to N[0].
Finite-family geometry and localization identify every column with a finite
product of R(r b_i)_*(r^* b_i^*N)[0] as displayed in hpieces. The finite-product
injective-resolution theorem verifies this derived column comparison. Hence every
column belongs to P. Horizontally truncate after column m, discarding the outgoing
differential. The projection to the preceding quotient truncation has kernel the
mth column shifted by -m, with its signed differential. Its short exact triangle
and induction put all these finite totals in P. The truncation projections split
as graded maps. The degreewise limit is the full total, because each total degree
stabilizes. The sequence from that total to the product of truncations, followed
by 1 minus the shift on that product, is degreewise short exact. For surjectivity,
start x_0=0 and lift x_m-y_m recursively with the graded splitting; this gives a
morphism of sheaves, not just choices of sectionwise preimages. Termwise products
compute derived products. The short exact triangle, rotation, shifts and product
closure now put the total in P. Transport through the augmented-total isomorphism.
Neither retracts nor filtered-colimit closure is needed in this final recovery.
-/
theorem proetale_cech_product_class_recovery
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (V : Scheme.{u}) [CompactSpace V] [QuasiSeparatedSpace V]
    (N : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V))
    (I : Type (u + 1)) (U : I → V.ProEt)
    (hcover : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
      Scheme.proetalePrecoverage.coverings V)
    (haffine : ∀ i : I, IsAffine (U i).left)
    (P : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V))))
    (htri : P.IsTriangulated) (hiso : P.IsClosedUnderIsomorphisms)
    (hprod : ∀ (J : Type (u + 1))
      (K : J → DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V)))
      (c : Cone (Discrete.functor K)), IsLimit c → (∀ j : J, P (K j)) → P c.pt)
    (hpieces : ∀ (i : I) (W : Scheme.{u})
      [CompactSpace W] [QuasiSeparatedSpace W]
      (r : W ⟶ (U i).left) [WeaklyEtale r] [QuasiCompact r] [QuasiSeparated r],
      P ((CondensedRing.moduleObjectDerivedPushforward Λ (r ≫ (U i).hom)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((CondensedRing.upperStar Λ r).obj
            ((CondensedRing.upperStar Λ (U i).hom).obj N))))) :
    P ((DerivedCategory.singleFunctor _ 0).obj N) := by sorry

end AlgebraicGeometry.ProEtale
