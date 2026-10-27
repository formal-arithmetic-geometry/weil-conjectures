/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
import Sheaf.AlgebraicGeometry.NodalFamilyEtaleSourceLocality
import Sheaf.AlgebraicGeometry.NodalPointEtaleLocality
import Sheaf.AlgebraicGeometry.SchemeNodalRelativeCurve
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.AlgebraicGeometry.FlatCompositeFibreDimensionAtPoint
import Sheaf.AlgebraicGeometry.EtaleCompletedLocalRingIso
import Sheaf.AlgebraicGeometry.SmoothEtaleLocalSource
import Sheaf.TraceFormula.NodeAlgebraicallyClosedExtension
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.Jacobson.Ring

/-! # Nodal algebraic-space morphisms on étale scheme charts

Source: Stacks Project, spaces-more-morphisms.tex, Tags 0DSG(4)--(7) and 0DSF;
curves.tex, Tags 0C57 and 0C5D (blueprint: lem-sfb-space-nodal-chart-locality).

The scheme condition uses `IsNodalRelativeCurveWithScalars`, retaining the structural
scalars required by this node. The existential chart condition is defined on presheaf
maps, so it also applies to canonical fibre products and actual open-subfunctor inclusions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

namespace AlgebraicSpace

/-- The existential scheme-chart definition of a nodal relative curve. Only the source
chart must be surjective; neither vertical map is assumed separated or quasi-compact.
Source: Stacks Project, spaces-more-morphisms.tex, definition-nodal-family and Tag 0DSG(7)
(blueprint: lem-sfb-space-nodal-chart-locality). -/
def IsNodalRelativeDimensionOne {S : Scheme.{u}} {E F : (Over S)ᵒᵖ ⥤ Type u}
    (f : E ⟶ F) : Prop :=
  ∃ (U V : Over S) (a : yoneda.obj U ⟶ E) (b : yoneda.obj V ⟶ F) (h : U ⟶ V),
    IsEtale a ∧ IsSurjective a ∧ IsEtale b ∧
      a ≫ f = yoneda.map h ≫ b ∧ IsNodalRelativeCurveWithScalars h.left

/-- The universal-chart, target-atlas and source-atlas criteria, written on the actual
presheaf maps. The universal test has no surjectivity requirement on either chart.
Source: Stacks Project, spaces-more-morphisms.tex, Tag 0DSG(4)--(7)
(blueprint: lem-sfb-space-nodal-chart-locality). -/
def NodalAtlasCriteria {S : Scheme.{u}} {E F : (Over S)ᵒᵖ ⥤ Type u}
    (f : E ⟶ F) : Prop :=
  (IsNodalRelativeDimensionOne f ↔
    ∀ (U V : Over S) (a : yoneda.obj U ⟶ E) (b : yoneda.obj V ⟶ F) (h : U ⟶ V),
      IsEtale a → IsEtale b → a ≫ f = yoneda.map h ≫ b →
        IsNodalRelativeCurveWithScalars h.left) ∧
  (IsNodalRelativeDimensionOne f ↔
    ∃ (V : Over S) (b : yoneda.obj V ⟶ F),
      IsEtale b ∧ IsSurjective b ∧
        IsNodalRelativeDimensionOne (Limits.pullback.snd f b)) ∧
  (IsNodalRelativeDimensionOne f ↔
    ∃ (U : Over S) (a : yoneda.obj U ⟶ E),
      IsEtale a ∧ IsSurjective a ∧ IsNodalRelativeDimensionOne (a ≫ f))

/-- Nodal chart and atlas equivalences, arbitrary base change, and source-open restriction.
The same three equivalences hold for every source open, whether or not the original map
is nodal. No properness, nonemptiness, connectedness or global purity is assumed.
Source: Stacks Project, spaces-more-morphisms.tex, Tags 0DSG(4)--(7) and 0DSF
(blueprint: lem-sfb-space-nodal-chart-locality).

Proof, following the five steps of the node:
1. The scheme condition can be tested on all algebraically closed geometric points:
   compare with the chosen algebraic closure by field-extension component dimension and
   node_algebraically_closed_extension. Flatness and local finite presentation are stable
   under base change; pullback pasting identifies each new geometric fibre with the old
   one. Its purity, smoothness and completed local algebra are therefore unchanged.
2. Choose a target atlas and a source atlas over it. Compare a witnessing diagram with
   any other diagram using U ×_X U' and V ×_Y V', schemes by the representable scheme
   tests. The first common refinement surjects onto U'. Nodal-family étale source locality
   and scheme nodal étale postcomposition transport nodality across the common refinement
   and descend it to U' → V'. The converse applies the universal test to the chosen atlas.
3. For B → Y with B a scheme, base change the witness U → V to U ×_Y B → V ×_Y B.
   These are schemes; this top map is the scheme base change of U → V and is nodal by
   step 1. Its vertical maps are étale and its source map is surjective. For arbitrary
   Y' → Y, take a scheme atlas B → Y' and a scheme atlas of X ×_Y B. The universal
   criterion in step 2 supplies a witnessing diagram for X ×_Y Y' → Y'.
4. Pullback along a target atlas gives the forward target-atlas implication. Conversely
   choose a source atlas of that pullback and compose its surjective étale map to X.
   For a source atlas, use the universal criterion after composing the source charts;
   conversely compose the source atlas with the source chart of a witness.
5. Pull the witness back to an arbitrary source open. Its source is an open subscheme
   of U and remains nodal by source locality, since an open immersion is étale. The same
   arguments in steps 2--4 apply to this open subspace and give all three equivalences.
   All constructions include empty schemes and empty fibres.
-/
theorem nodal_chart_locality {S : Scheme.{u}} (X Y : AlgebraicSpace S) (f : X ⟶ Y) :
    NodalAtlasCriteria f.hom.hom ∧
    (IsNodalRelativeDimensionOne f.hom.hom →
      ∀ (Y' : AlgebraicSpace S) (g : Y' ⟶ Y),
        IsNodalRelativeDimensionOne (Limits.pullback.snd f.hom.hom g.hom.hom)) ∧
    (∀ A : OpenSubspace X,
      (IsNodalRelativeDimensionOne f.hom.hom →
        IsNodalRelativeDimensionOne (A.val.ι ≫ f.hom.hom)) ∧
      NodalAtlasCriteria (A.val.ι ≫ f.hom.hom)) := by
  sorry

/-- The chart definition agrees with the scheme condition when both spaces are schemes.
Source: Stacks Project, spaces-more-morphisms.tex, paragraph before definition-nodal-family
(blueprint: lem-sfb-space-nodal-chart-locality).
Proof: the identity diagram gives a witness in one direction. In the other direction
compare a witness with the identity diagram using the common-refinement argument of
step 2 of nodal_chart_locality, étale source locality and étale postcomposition. -/
theorem nodal_yoneda_iff {S : Scheme.{u}} (U V : Over S) (h : U ⟶ V) :
    IsNodalRelativeDimensionOne (yoneda.map h) ↔ IsNodalRelativeCurveWithScalars h.left := by
  sorry

end AlgebraicSpace

/-- Smooth curve points and ordinary nodes are preserved and reflected on étale scheme
charts over an algebraically closed field, without a purity hypothesis on the schemes.
The completed local algebra comparison is the map induced by the stalk map, as specified
by its values modulo every power of the maximal ideals. This also compares two charts
through their common refinement.
Source: Stacks Project, curves.tex, Tag 0C57, and spaces-more-morphisms.tex, Tag 0DSG
(blueprint: lem-sfb-space-nodal-chart-locality).

Proof (step 5 of the node): smooth_at_iff_of_etale preserves and reflects smoothness.
Flat-composite fibre dimension adds the zero-dimensional étale fibre, so the relative
dimension-one condition agrees. A closed point of a locally finite type scheme over Ω
has residue field Ω by Zariski's lemma. Apply etale_completedLocalRing_iso to obtain the
bijective induced completed stalk map and closedness on both sides. Germ naturality
shows this map preserves the structural scalars. Compose its algebra equivalence with
the nodal presentation, in either direction. For two charts take their scheme common
refinement; the same induced maps give the two compatible completion computations.
-/
theorem nodal_geometric_point_chart_locality
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {C D : Scheme.{u}}
    (b : C ⟶ Spec (.of Ω)) [LocallyOfFiniteType b]
    (e : D ⟶ C) [Etale e] (y : D) :
    ((∃ W : C.Opens, e y ∈ W ∧ SmoothOfRelativeDimension 1 (W.ι ≫ b)) ↔
      ∃ W : D.Opens, y ∈ W ∧ SmoothOfRelativeDimension 1 (W.ι ≫ e ≫ b)) ∧
    (IsOrdinaryNodeOver b (e y) ↔ IsOrdinaryNodeOver (e ≫ b) y) ∧
    ((e y ∈ closedPoints C ∨ y ∈ closedPoints D) →
      e y ∈ closedPoints C ∧ y ∈ closedPoints D ∧ Nonempty
        (@AlgEquiv Ω
          (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk (e y)))
            (C.presheaf.stalk (e y)))
          (AdicCompletion (IsLocalRing.maximalIdeal (D.presheaf.stalk y))
            (D.presheaf.stalk y))
          _ _ _ (b.completedLocalScalarMap (e y)).toAlgebra
          ((e ≫ b).completedLocalScalarMap y).toAlgebra) ∧
      ∃ ehat :
          AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk (e y)))
              (C.presheaf.stalk (e y)) →+*
            AdicCompletion (IsLocalRing.maximalIdeal (D.presheaf.stalk y))
              (D.presheaf.stalk y),
        Function.Bijective ehat ∧
        (∀ a : Ω, ehat (b.completedLocalScalarMap (e y) a) =
          (e ≫ b).completedLocalScalarMap y a) ∧
        ∀ (n : ℕ)
          (z : AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk (e y)))
            (C.presheaf.stalk (e y))) (a : C.presheaf.stalk (e y)),
          AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (C.presheaf.stalk (e y))) n z =
              Ideal.Quotient.mk (IsLocalRing.maximalIdeal (C.presheaf.stalk (e y)) ^ n) a →
          AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (D.presheaf.stalk y)) n (ehat z) =
            Ideal.Quotient.mk (IsLocalRing.maximalIdeal (D.presheaf.stalk y) ^ n)
              ((e.stalkMap y).hom a)) := by
  sorry

end AlgebraicGeometry
