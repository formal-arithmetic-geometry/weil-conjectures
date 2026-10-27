/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.AlgebraicGeometry.OpenImmersionInverseLimitDescent
import WeilConjectures.AlgebraicGeometry.LimitFibreProducts
import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent

/-! # Spreading open finite-presentation charts of fpqc forms

Source: Raynaud, Un critere d'effectivite de descente, Theorem 4.1 proof,
reductions 3 and 4, printed pp. 5-19--5-20; Stacks Project, Tags 01ZM, 0EUU, 01Z5.
(blueprint: lem-sfb-fpqc-chart-limit-spreading)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A specified finitely presented open chart in a scheme representing the limit restriction
of an fpqc form spreads to a representable open chart at a finite stage. If the chart is
quasi-affine, the stage chart can be chosen quasi-affine too.

The cartesian square `IsPullback g.left V.hom Vi.hom ...` specifies the isomorphism
`Vi × T ≅ V` over the limit. The equality of sections identifies the base-changed chart map
with the given inclusion into `F_T`, through this very isomorphism. In particular, the stage
restriction of `F` is not assumed representable.

Source: Raynaud, Un critere d'effectivite de descente, Theorem 4.1 proof,
reductions 3 and 4, printed pp. 5-19--5-20; Stacks Project, Tags 01ZM, 0EUU, 03N0, 01Z5.
(blueprint: lem-sfb-fpqc-chart-limit-spreading)

Proof:
1. Apply thm-pd-spreading-out to the finitely presented map V to T. The stages are qcqs
   and their transitions affine by lem-weil-pbc-affine-scheme-qcqs and
   lem-weil-pbc-morphism-affine-schemes-affine. The stage base changes of V form a qcqs
   affine-transition system with limit V by lem-weil-pbc-qcqs-morphism-permanence and
   lem-weil-pbc-limit-fibre-products.
2. Yoneda turns the specified inclusion into a section of F(V). Apply
   lem-sfb-fpqc-form-qcqs-limit-continuity to descend that section to a stage chart.
   Yoneda then supplies the chart map, retaining its prescribed base coordinate.
3. Base change by A. The stage section gives maps into the representing scheme P.
   Their limiting map is the base change of the given open immersion. By
   lem-weil-pbc-fibre-product-affine-spectra and lem-weil-pbc-limit-fibre-products the
   base systems remain affine with the displayed limits. The source of a stage map
   is quasi-compact, so its image in P lies in a finite union P0 of affine opens.
   Since P/A is quasi-separated and A affine, P0 is qcqs and finitely presented over A,
   using lem-weil-pbc-qcqs-morphism-permanence.
4. The map from the stage source into P0 is locally of finite presentation: for
   finitely presented R-algebras C and D, a map D to C presents C over D by adjoining
   the generators of C and the finitely many equations identifying the D-generators
   with their chosen polynomial images (def-sbc-locally-finite-presentation).
5. Apply lem-weil-pbc-descend-open-immersion-qcqs to this map over the affine base
   system obtained by base change by A. At a later stage it is an open immersion
   into P0, hence also into P.
6. For every scheme test H with a section of F, the chart pullback over H times A
   is an open. Its two overlap restrictions agree because they express equality
   of the same F-sections. Descend the open by lem-weil-pbc-open-subscheme-fpqc-descent
   and lem-weil-pbc-fpqc-covering-axioms. A lift on this open descends uniquely by
   lem-weil-pbc-fpqc-representable-descent; equality of its F-section descends by
   the fpqc equalizer condition. Thus the stage chart is representable by opens.
7. If V is quasi-affine, lem-sfb-limit-quasi-affine-eventual makes a later chart
   quasi-affine. Base change preserves finite presentation and the representable
   open-immersion property, as well as the specified isomorphism and section equality. -/
theorem exists_fpqc_chart_of_isLimit
    (S A : Scheme.{u}) [IsAffine S] [IsAffine A]
    (p : A ⟶ S) [Flat p] [Surjective p] [QuasiCompact p]
    (F : (Over S)ᵒᵖ ⥤ Type (max u v))
    (hF : Presheaf.IsSheaf (Scheme.fpqcTopology.over S) F)
    (P : Over A) (hP : Nonempty (((Over.map p).op ⋙ F).RepresentableBy P))
    [QuasiSeparated P.hom] [LocallyOfFinitePresentation P.hom]
    (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S) [∀ i : Iᵒᵖ, IsAffine (D.obj i).left]
    (c : Cone D) (hc : IsLimit c)
    (Y : Over c.pt.left) (hY : ((Over.map c.pt.hom).op ⋙ F).RepresentableBy Y)
    (V : Over c.pt.left) (j : V ⟶ Y) [IsOpenImmersion j.left]
    [LocallyOfFinitePresentation V.hom] [QuasiCompact V.hom] [QuasiSeparated V.hom] :
    ∃ (i : I) (Vi : Over (D.obj (op i)).left)
      (α : uliftYoneda.{v}.obj Vi ⟶ (Over.map (D.obj (op i)).hom).op ⋙ F)
      (g : (Over.map c.pt.hom).obj V ⟶ (Over.map (D.obj (op i)).hom).obj Vi),
      LocallyOfFinitePresentation Vi.hom ∧ QuasiCompact Vi.hom ∧ QuasiSeparated Vi.hom ∧
      (MorphismProperty.over (@IsOpenImmersion)).relative uliftYoneda.{v} α ∧
      IsPullback g.left V.hom Vi.hom (c.π.app (op i)).left ∧
      F.map g.op
        (uliftYonedaEquiv.{v} (F := (Over.map (D.obj (op i)).hom).op ⋙ F) α) =
        hY.homEquiv j ∧
      (V.left.IsQuasiAffine → Vi.left.IsQuasiAffine) := by
  sorry

end AlgebraicGeometry
