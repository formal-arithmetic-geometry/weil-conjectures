module

public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Sheaf.AlgebraicGeometry.SchemeGroupoidQuotientPresentation
public import Sheaf.AlgebraicGeometry.FppfGroupoidRestrictionQuotient
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.ModuliStackProperties
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Sheaf.CategoryTheory.GroupoidStackificationLocalDescription
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFourPropertyFppfDescent
import WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover
import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts
import Mathlib.AlgebraicGeometry.RelativeGluing
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Finite flat groupoid quotients and invariant opens

Source: Stacks Project, Tags 0DUM, 06FH, 06FI, 0507, 04M9 and 0DTY
(blueprint: lem-sfb-finite-flat-groupoid-quotient-open-geometry).

The quotient is specified by the existing fppf quotient-presentation interface, rather
than by an arbitrary stack or a quotient of sets of objects. The open correspondence
retains the scheme base-change projection. Restricted groupoid operations are normalized
by their maps to the original relation. The last clause uses the absolute diagonal.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

namespace CategoryTheory

/-- An open in the object scheme, with its original base structure.
Source: Stacks 0507, pullback of an open substack
(blueprint: lem-sfb-finite-flat-groupoid-quotient-open-geometry). -/
def groupoidOpenChart {S : Scheme.{u}} (U : Over S) (V : U.left.Opens) : Over S :=
  Over.mk (V.ι ≫ U.hom)

/-- The canonical inclusion of the open chart into the original object scheme.
Source: Stacks 0507, pullback of an open substack
(blueprint: lem-sfb-finite-flat-groupoid-quotient-open-geometry). -/
def groupoidOpenChartInclusion {S : Scheme.{u}} (U : Over S) (V : U.left.Opens) :
    groupoidOpenChart U V ⟶ U :=
  Over.homMk V.ι

/-- A finite locally free groupoid with DM fppf quotient has a finite flat surjective
scheme presentation, and its invariant opens are exactly its open substacks. Their
restricted presentations retain the original groupoid operations and atlas maps.
An affine object scheme makes the quotient absolutely separated.

Source: Stacks Project, Tags 0DUM, 06FH, 06FI, 0507, 04M9 and 0DTY(6)
(blueprint: lem-sfb-finite-flat-groupoid-quotient-open-geometry).

Proof, following the nine steps of the node:
1. Finite local freeness gives finite, flat, locally finitely presented endpoints.
Apply lem-sfb-flat-groupoid-algebraic-quotient to obtain the algebraic quotient,
its representable flat lfp surjective presentation, and R = U times_Q U.
2. On an affine scheme test T, stackification gives fppf local lifts to U by
lem-sfb-groupoid-stackification-local-description. The relation calculation identifies
the pulled-back presentation with a base change of s or t, hence finite and affine by
lem-weil-pbc-finite-morphism-permanence. Descend affineness first by
lem-sfb-space-four-property-fppf-descent, so the source is an affine scheme.
The fppf family is fpqc by lem-trf-fppf-covering-is-fpqc; then apply
lem-weil-pbc-fpqc-descend-finite to this scheme morphism.
3. Glue these affine scheme tests by lem-weil-pbc-relative-glueing-affine-opens.
Their canonical comparisons satisfy the cocycle. The lemma
lem-weil-pbc-finite-local-on-target gives finiteness on every scheme test.
Field-extension lifts give surjectivity of the actual map on point classes.
4. Pull back an open substack to U. Strict fullness and R = U times_Q U identify
its two inverse images on R, giving invariance.
5. Conversely pull an invariant open back along local lifts of an object to U.
The arrows in R identify these opens on overlaps. Apply
lem-weil-pbc-open-subscheme-fpqc-descent to descend them to an open in each test T.
Uniqueness gives independence of lifts, pullback compatibility and invariance under
isomorphisms. The full subgroupoid where this open is all of T is an open substack.
6. Uniqueness in fpqc descent of opens shows the two constructions are inverse.
This gives a bijection with the specified pullback, including the empty open.
7. Restrict an etale DM atlas to show the open substack is DM. Its presentation
is the base change of p, so finiteness is preserved by
lem-weil-pbc-finite-morphism-permanence and flatness, lfp and surjectivity by
lem-sfb-stack-chartwise-smooth-etale-calculus. Invariance identifies the restricted
relation with each endpoint inverse image. Its projections are finite locally free.
The induced identity, inverse and composition commute with the original operations.
The kernel-pair calculation and lem-sfb-fppf-groupoid-stack-presentations(2) give
exactly the displayed quotient presentation of the open substack.
8. If U is affine, C = U times_Z U is affine by
lem-weil-pbc-fibre-product-affine-spectra. Its projection to U is separated by
lem-weil-pbc-affine-source-morphism-separated. The composite R -> C -> U is finite,
hence proper by lem-weil-pbc-finite-proper. Apply
lemma-nagata-proper-to-separated-target to deduce R -> C is proper.
9. Forgetting the S-structure gives the same total quotient and relation over Z.
The absolute product is algebraic by lem-sfb-algebraic-stack-fibre-products.
The product cover is fppf surjective by the chartwise calculus; its pullback of the
absolute diagonal is precisely R -> C. Apply
lem-sfb-representable-proper-fppf-target-test to descend its properness.
No separatedness of S, constant degree, or characteristic restriction is used. -/
theorem finiteFlatGroupoid_quotient_open_geometry
    {S : Scheme.{u}} {U R : Over S} (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R)
    (c : pullback s.left t.left ⟶ R.left)
    (hG : IsGroupoidScheme s.left t.left e.left i.left c)
    [s.left.IsFiniteLocallyFree] [t.left.IsFiniteLocallyFree]
    (Q : BasedCategory.{v, w} (Over S))
    (p : BasedFunctor (discreteModuli (yoneda.obj U)) Q)
    (presentation : SchemeGroupoidQuotientPresentation s t e.left i.left c Q p)
    (hQ : IsDeligneMumfordModuliStack Q) :
    ModuliSchemeTest (fun _ _ f ↦
      Surjective f ∧ IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f) p ∧
    (∃ b : OpenModuliSubstack Q ≃
        {V : U.left.Opens // s.left ⁻¹ᵁ V = t.left ⁻¹ᵁ V},
      ∀ W : OpenModuliSubstack Q,
        (∃ a : BasedFunctor (discreteModuli (yoneda.obj (groupoidOpenChart U (b W).val)))
            (moduliTwoFiberProduct p (fullModuliInclusion Q W.property)),
          IsSchemeModuliBaseChange a (groupoidOpenChartInclusion U (b W).val)) ∧
        ∃ pV : BasedFunctor
            (discreteModuli (yoneda.obj (groupoidOpenChart U (b W).val))) W.category,
          Nonempty (ModuliTwoIso (pV.comp (fullModuliInclusion Q W.property))
            ((discreteModuliMap (yoneda.map (groupoidOpenChartInclusion U (b W).val))).comp
              p)) ∧
          ModuliSchemeTest (fun _ _ f ↦
            Surjective f ∧ IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f) pV ∧
          (restrictedEtaleRelationSource s t
            (groupoidOpenChartInclusion U (b W).val)).left.IsFiniteLocallyFree ∧
          (restrictedEtaleRelationTarget s t
            (groupoidOpenChartInclusion U (b W).val)).left.IsFiniteLocallyFree ∧
          ∃ (eV : groupoidOpenChart U (b W).val ⟶
              restrictedEtaleRelation s t (groupoidOpenChartInclusion U (b W).val))
            (iV : restrictedEtaleRelation s t (groupoidOpenChartInclusion U (b W).val) ⟶
              restrictedEtaleRelation s t (groupoidOpenChartInclusion U (b W).val))
            (cV : pullback
              (restrictedEtaleRelationSource s t
                (groupoidOpenChartInclusion U (b W).val)).left
              (restrictedEtaleRelationTarget s t
                (groupoidOpenChartInclusion U (b W).val)).left ⟶
              (restrictedEtaleRelation s t (groupoidOpenChartInclusion U (b W).val)).left),
            eV ≫ restrictedGroupoidMiddle s t (groupoidOpenChartInclusion U (b W).val) =
              groupoidOpenChartInclusion U (b W).val ≫ e ∧
            iV ≫ restrictedGroupoidMiddle s t (groupoidOpenChartInclusion U (b W).val) =
              restrictedGroupoidMiddle s t (groupoidOpenChartInclusion U (b W).val) ≫ i ∧
            cV ≫ (restrictedGroupoidMiddle s t
                (groupoidOpenChartInclusion U (b W).val)).left =
              restrictedGroupoidComposableMap s t (groupoidOpenChartInclusion U (b W).val) ≫
                c ∧
            Nonempty (SchemeGroupoidQuotientPresentation
              (restrictedEtaleRelationSource s t (groupoidOpenChartInclusion U (b W).val))
              (restrictedEtaleRelationTarget s t (groupoidOpenChartInclusion U (b W).val))
              eV.left iV.left cV W.category pV)) ∧
    Function.Surjective (moduliPointMap p) ∧
    (IsAffine U.left → HasProperModuliDiagonal (BasedCategory.ofFunctor
      (Q.p ⋙ Over.map (AlgebraicGeometry.specULiftZIsTerminal.from S)))) := by
  sorry

end CategoryTheory
