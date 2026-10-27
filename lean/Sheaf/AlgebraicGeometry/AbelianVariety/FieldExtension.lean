module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.CategoryTheory.Monoidal.Grp
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.Dimension
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeAffineCovers
import WeilConjectures.AlgebraicGeometry.DimensionBaseChange
import WeilConjectures.AlgebraicGeometry.DimensionAffineOpenCover

/-! # Abelian varieties under field extension

Source: Stacks Project, Groupoids, Tag 0BFB, lemma-abelian-variety-change-field;
Morphisms, Tag 02FY, lemma-dimension-fibre-after-base-change, part (1).
(blueprint: lem-sfb-abelian-field-extension)

The group object is the image of `Grp.mk A` under `(Over.pullback g).mapGrp`.
Its underlying scheme is `pullback A.hom g`, its structure morphism is the second
projection, and its group operations are the base changes of those on `A`.
Dimension uses `Scheme.dim`, the supremum of the dimensions of the local rings.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Extending the ground field preserves abelian varieties and their dimension.
Source: Stacks Project, Tag 0BFB, lemma-abelian-variety-change-field, and Tag 02FY,
lemma-dimension-fibre-after-base-change (1).
(blueprint: lem-sfb-abelian-field-extension)

The bundled group object `(Over.pullback g).mapGrp.obj (Grp.mk A)` supplies the
canonical base-changed multiplication, inverse and identity; no arbitrary group
structure on the pullback is chosen. Its `.X` is definitionally `(Over.pullback g).obj A`.

Proof:
1. Base change the operations using `def-sc-group-scheme` and `def-pc-base-change`.
   On every test scheme, the pullback universal property identifies its points
   with the original functor of points restricted to schemes over the new field.
   The group identities therefore persist. The identity is a section, so `A` is nonempty.
2. By `def-sc-abelian-variety`, the structure morphism is proper and smooth.
   Both properties persist under base change by `lem-pc-proper-base-change`.
3. Apply `lem-sbc-connected-rational-point-geometrically-connected` to `A` and its
   identity section. The pullback is connected, hence is an abelian variety.
4. Properness implies local finite type (`def-weil-proper-morphism`). Apply
   `lem-pc-dim-base-change-affine-covers` to obtain nonempty scalar extension
   and matching affine covers with rings `R i` and `R i` tensor the new field,
   where each `R i` is a finite type algebra over the original field.
5. The affine clause of `lem-pc-dim-base-change` identifies the dimensions of
   matching chart rings. Apply `lem-pc-dimension-affine-open-cover` to each
   nonempty scheme. Their suprema agree, giving precisely the local-ring
   dimension equality of `def-pc-dimension`, including empty affine charts. -/
theorem IsAbelianVariety.fieldExtension
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A] :
    IsAbelianVariety
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp.obj
        (Grp.mk A)).X) ∧
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp.obj
        (Grp.mk A)).X).left.dim = A.left.dim := by
  sorry

end AlgebraicGeometry
