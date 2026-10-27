module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.CategoryTheory.Adjunction.Basic
import Sheaf.AlgebraicGeometry.SpacePerfectLocalizingGeneration
import Sheaf.AlgebraicGeometry.AlgebraicSpaceCompactPerfectGenerator
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.CompactlyGenerated
import WeilConjectures.CategoryTheory.BrownRepresentabilityRightAdjoint

/-! # Right adjoint of quasi-coherent pushforward for qcqs algebraic spaces

Source: Stacks Project, Duality for Spaces, Tag 0E55, lemma-twisted-inverse-image,
and section-trace (blueprint: lem-sfb-qcqs-space-pushforward-right-adjoint).

The direct image is the recorded K-injective derived functor on the equivalent
small ringed models. Its restriction is identified with that ambient functor by
`QCohDirectImagePresentation.comparison`. Quasi-separatedness is absolute, using
the affine-pair criterion of Properties of Spaces, Tag 0AHR.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Derived direct image between qcqs algebraic spaces preserves quasi-coherent
cohomology and has a right adjoint on the full quasi-coherent derived subcategories.
The inverse Hom equivalence is composition of the direct image of the given map
with the adjunction counit. No condition is imposed on the base scheme.
Source: Stacks Project, Duality for Spaces, Tag 0E55 and section-trace
(blueprint: lem-sfb-qcqs-space-pushforward-right-adjoint).

Proof:
1. By lem-sfb-space-qcqs-permanence, f is qcqs. Apply
   lem-sfb-space-derived-pushforward-coproducts to obtain preservation of
   quasi-coherent cohomology and coproducts by the canonical derived direct image.
   The resulting full-subcategory restriction has its comparison with the ambient
   functor. By lem-sfb-space-perfect-localizing-generation, both subcategories
   inherit ambient coproducts, shifts and distinguished triangles.
2. The chart-limit direct image is additive, because its projections respect
   sums of module maps. Module sheaves on the small ringed models have K-injective
   resolutions by prop-pur-kinjective-resolutions-exist. Hence
   lem-pc-right-derived-functor-triangulated makes the ambient derived direct image
   triangulated. Its restriction to these full triangulated subcategories is exact.
3. By lem-sfb-space-compact-perfect-generator the source has one compact perfect
   generator. Replacing a shift n by -n gives the generating criterion of
   def-pc-compactly-generated. Apply lem-pc-brown-representability-right-adjoint
   to the coproduct-preserving exact restriction to obtain a right adjoint a.
4. Naturality of the adjunction bijection in E gives its value on u by composing
   the direct image of u with its value on the identity of a(F). The latter is
   the counit at F; naturality in F gives the counit transformation. This proves
   the stated Hom formula, using only the qcqs hypotheses throughout. -/
theorem qcqs_derivedDirectImage_hasRightAdjoint
    {S : Scheme.{u}} (X Y : AlgebraicSpace S) (f : X ⟶ Y)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    (hXqc : CompactSpace (Point X.obj.obj))
    (hXqs : ∀ (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj)
      (b : yoneda.obj V ⟶ X.obj.obj), IsAffine U.left → IsAffine V.left →
        CompactSpace (Point (Limits.pullback a b)))
    (hYqc : CompactSpace (Point Y.obj.obj))
    (hYqs : ∀ (U V : Over S) (a : yoneda.obj U ⟶ Y.obj.obj)
      (b : yoneda.obj V ⟶ Y.obj.obj), IsAffine U.left → IsAffine V.left →
        CompactSpace (Point (Limits.pullback a b))) :
    (∀ E : X.DerivedModules, X.derivedQCohProperty E →
      Y.derivedQCohProperty ((derivedDirectImage f).obj E)) ∧
    ∃ (D : QCohDirectImagePresentation f) (a : Y.DerivedQCoh ⥤ X.DerivedQCoh)
      (adj : D.functor ⊣ a),
      ∀ (E : X.DerivedQCoh) (F : Y.DerivedQCoh) (v : E ⟶ a.obj F),
        (adj.homEquiv E F).symm v = D.functor.map v ≫ adj.counit.app F := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
