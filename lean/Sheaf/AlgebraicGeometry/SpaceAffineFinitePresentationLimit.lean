/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite
public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativeSpecCorrespondence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineChartCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition

/-! # Affine algebraic spaces as limits of finitely presented affine spaces

Source: Stacks Project, Limits of Spaces, Tag 0870, lemma-affine-morphism-is-limit
(blueprint: lem-sfb-space-affine-fp-limit).

The cone is a limit in fppf sheaves over the target, via the full-subcategory
inclusion and its induced functor on slice categories. Absolute quasi-separatedness
uses the shared affine-pair test, without any separation condition on the base scheme.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- An affine map with qcqs target is a directed limit of affine finitely presented maps.
Source: Stacks Project, Limits of Spaces, Tag 0870, lemma-affine-morphism-is-limit
(blueprint: lem-sfb-space-affine-fp-limit).

Proof:
1. By [lem-sfb-space-relative-spec-correspondence], write Z as relative Spec of the
   quasi-coherent algebra A = p_* O_Z on B. Since B is qcqs,
   [lem-sfb-space-algebra-fp-directed-colimit] expresses A as a small nonempty directed
   colimit of finitely presented algebras A_i.
2. Put Z_i = Spec_B A_i. The same relative-Spec correspondence gives the maps over B,
   their compatibility, and affineness and finite presentation of each Z_i over B.
   Choose affine etale charts of B by [lem-a1-space-affine-etale-cover]. Their pullbacks
   cover the stages by [lem-trf-space-fibre-products-etale-covers]. On each such chart,
   transitions are maps of affine schemes, so are affine by
   [lem-weil-pbc-morphism-affine-schemes-affine]. Descend this property by
   [lem-sfb-space-affine-locality].
3. By [lem-sfb-space-qcoh-affine-chart-calculus], sections of A are the colimit of
   sections of A_i on each affine etale chart. The chart formulas for relative Spec
   identify the pulled-back cone with the spectrum of that ring colimit. The affine
   case of [lem-weil-pbc-limit-affine-transition] makes this a scheme limit, hence a
   represented fppf-sheaf limit by its universal property on each test scheme.
   Sheaf limits and base changes are computed on sections. The local inverse maps
   agree on overlaps by uniqueness and glue by the sheaf axiom, yielding the limit
   cone in fppf sheaves over B. -/
theorem exists_affine_finitePresentation_limit
    {S : Scheme.{u}} {Z B : AlgebraicSpace S} (p : Z ⟶ B)
    (hp : MapIsAffine p)
    (hqc : IsQuasiCompact B.obj)
    (hqs : IsAbsolutelyQuasiSeparated B) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : Iᵒᵖ ⥤ Over B)
      (π : (Functor.const Iᵒᵖ).obj (Over.mk p) ⟶ D),
      (∀ i : Iᵒᵖ,
        MapIsAffine (D.obj i).hom ∧
        IsQuasiCompactPresheafMap (D.obj i).hom.hom.hom ∧
        IsQuasiCompactPresheafMap (pullback.diagonal (D.obj i).hom.hom.hom) ∧
        MapIsLocallyOfFinitePresentation (D.obj i).hom) ∧
      (∀ (i j : Iᵒᵖ) (f : i ⟶ j),
        MapIsAffine (D.map f).left) ∧
      Nonempty (IsLimit ((Over.post (ObjectProperty.ι (IsAlgebraicSpace (S := S)))).mapCone
        (Cone.mk (Over.mk p) π))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
