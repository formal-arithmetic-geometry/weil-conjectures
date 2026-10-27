/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q95
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.TraceFormula.SyntomicLocusBaseChange
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.LciEtalePointwiseInvariance
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import Sheaf.AlgebraicGeometry.EtaleOpenChartMorphismDescent
import Sheaf.TraceFormula.LciPointwiseCriterion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Fibrewise complete-intersection source locus for algebraic spaces

Source: Stacks Project, spaces-more-morphisms.tex, Tags 06CA and 06C9;
morphisms.tex, Tags 01UF, 01UG and 02V3
(blueprint: lem-sfb-space-fibrewise-lci-source-locus).

The base scheme of the sheaf presentation is `B`; the scheme called `S` in the node is
`T.left`. The map `f` is a map to that scheme's Yoneda presheaf. All base changes use
literal presheaf pullbacks. Open subspaces use the existing representable open subfunctors.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every fibre is a local complete intersection, tested on every representable étale
scheme chart. For a locally finite type structural map, the existing local-ring condition
is equivalent to an affine cover by finite type local-complete-intersection algebras,
by `lci_pointwise_criterion`. This formulation also applies to an open subfunctor or the
literal presheaf fibre product, retaining its canonical map to the target scheme.
Source: Stacks, morphisms.tex, Tags 01UF, 01UG, 02V3; spaces-morphisms.tex,
lemma-syntomic-local (blueprint: lem-sfb-space-fibrewise-lci-source-locus). -/
def HasCompleteIntersectionFibresToScheme {B : Scheme.{u}} (T : Over B)
    {E : (Over B)ᵒᵖ ⥤ Type u} (f : E ⟶ yoneda.obj T) : Prop :=
  ∀ (V : Over B) (a : yoneda.obj V ⟶ E), IsEtale a →
    (yoneda.preimage (a ≫ f)).left.HasCompleteIntersectionFibres

/-- A flat locally finitely presented algebraic space over a scheme has a largest source
open with local-complete-intersection fibres. Its inverse image in every étale scheme
chart is the existing scheme fibrewise complete-intersection locus. After every scheme
base change, flatness and local finite presentation persist and the literal inverse-image
open is again largest. Thus it equals the locus of the base-changed morphism. The original
open is the whole source exactly when all fibres are local complete intersections.

Source: Stacks Project, spaces-more-morphisms.tex, Tags 06CA and 06C9, specialized to
Y = Z = the base scheme; morphisms.tex, Tags 01UF, 01UG and 02V3
(blueprint: lem-sfb-space-fibrewise-lci-source-locus).

Proof, following the node's seven steps:
1. Choose a representable surjective étale scheme atlas P of X. The chart criterion
   lem-sfb-space-local-properties-chart-test gives flatness and local finite presentation
   for its composite h to T. Apply lem-trf-syntomic-locus-base-change to obtain its open
   fibrewise complete-intersection locus L.
2. The two projections of P ×_X P are étale scheme maps, by
   lem-trf-space-fibre-products-etale-covers. On every residue-field fibre,
   lem-sfb-lci-etale-pointwise-invariance identifies the complete-intersection conditions
   at corresponding points. Thus both projections pull L back to the same open.
3. Descend L by lem-trf-etale-open-chart-morphism-descent to an open A of X. For any other
   étale scheme chart V, compare on V ×_X P. Pointwise étale invariance identifies both
   pullbacks there; scheme-test uniqueness in the descent lemma gives the chart formula.
4. Apply lem-trf-lci-pointwise-criterion on residue-field fibres to identify the local-ring
   condition with affine covers by finite type local-complete-intersection algebras.
   The pulled-back charts cover the fibres by lem-trf-space-fibre-products-etale-covers.
   Conversely any source open with this fibre property pulls back inside L on P, so
   surjectivity and lem-a1-space-point-open-calculus put that open inside A. The same
   étale-invariance argument proves independence of the scheme charts used in the test.
5. For any scheme base change T' → T, pull back the atlas. Scheme flatness and local
   finite presentation persist by lem-weil-pbc-flat-morphism-base-change and clause (3)
   of lem-weil-pbc-qcqs-morphism-permanence. The chart criterion gives these properties
   for the space map. The scheme locus becomes the inverse image of L by
   lem-trf-syntomic-locus-base-change. Descent uniqueness therefore identifies the new
   largest source open with the literal inverse image of A.
6. If A is the whole source its fibre property is the required one for f. Conversely,
   if every fibre of f is a local complete intersection, maximality applied to the whole
   source gives A = X.
7. For empty sources the atlas and locus are empty; empty fibres impose no condition.
   No step uses closedness or properness.
-/
theorem exists_fibrewiseLci_open_baseChange {B : Scheme.{u}} (X : AlgebraicSpace B)
    (T : Over B) (f : X.obj.obj ⟶ yoneda.obj T)
    (hflat : MapToSchemeIsLocally (@Flat) X T f)
    (hfp : MapToSchemeIsLocally (@LocallyOfFinitePresentation) X T f) :
    ∃ A : OpenSubspace X,
      HasCompleteIntersectionFibresToScheme T (A.val.ι ≫ f) ∧
      (∀ C : OpenSubspace X,
        HasCompleteIntersectionFibresToScheme T (C.val.ι ≫ f) → C ≤ A) ∧
      (∀ (V : Over B) (a : yoneda.obj V ⟶ X.obj.obj), IsEtale a →
        schemePointMap a ⁻¹' pointImage A.val.ι =
          (yoneda.preimage (a ≫ f)).left.fiberCompleteIntersectionLocus) ∧
      (∀ (T' : Over B) (g : T' ⟶ T),
        (∀ (V : Over B) (a : yoneda.obj V ⟶ Limits.pullback f (yoneda.map g)),
          IsEtale a →
            Flat (yoneda.preimage (a ≫ Limits.pullback.snd f (yoneda.map g))).left ∧
            LocallyOfFinitePresentation
              (yoneda.preimage (a ≫ Limits.pullback.snd f (yoneda.map g))).left) ∧
        IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left)
          (A.val.preimage (Limits.pullback.fst f (yoneda.map g))).ι ∧
        HasCompleteIntersectionFibresToScheme T'
          ((A.val.preimage (Limits.pullback.fst f (yoneda.map g))).ι ≫
            Limits.pullback.snd f (yoneda.map g)) ∧
        (∀ C : Subfunctor (Limits.pullback f (yoneda.map g)),
          IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) C.ι →
          HasCompleteIntersectionFibresToScheme T'
            (C.ι ≫ Limits.pullback.snd f (yoneda.map g)) →
          C ≤ A.val.preimage (Limits.pullback.fst f (yoneda.map g)))) ∧
      (A.val = ⊤ ↔ HasCompleteIntersectionFibresToScheme T f) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
