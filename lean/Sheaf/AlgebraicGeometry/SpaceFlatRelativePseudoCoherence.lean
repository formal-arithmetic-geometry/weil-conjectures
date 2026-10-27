module

public import Sheaf.AlgebraicGeometry.AlgebraicSpacePseudoCoherentComplex
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion
import Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus
import Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Relative pseudo-coherence for flat algebraic-space morphisms

Source: Stacks Project, More on Morphisms of Spaces, Tag 0DII,
lemma-relative-pseudo-coherent-is-moot; the relative definition is Tag 0CSY
(blueprint: lem-sfb-space-flat-relative-pseudocoherence).

The left side expands relative pseudo-coherence over every integer and every compatible
pair of etale scheme charts. Chart restriction is the existing derived Zariski restriction,
and relative pseudo-coherence on schemes uses the existing affine-space embedding definition.
-/

@[expose] public section

set_option autoImplicit false

universe u w wS

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- A quasi-coherent derived object for a flat, locally finitely presented space morphism
is relatively pseudo-coherent exactly when it is absolutely pseudo-coherent.
Source: Stacks Project, More on Morphisms of Spaces, Tag 0DII and Definition 0CSY
(blueprint: lem-sfb-space-flat-relative-pseudocoherence).

Proof:
1. On any commuting etale chart square, the horizontal scheme morphism is flat and
locally of finite presentation, hence locally of finite type, by
lem-sfb-scheme-etale-source-target-properties and
lem-sfb-space-etale-presentation-property-criterion. A presentation with surjective
source exists. By lem-sfb-space-derived-etale-chart-calculus and
lem-sfb-derived-etale-zariski-equivalence the restricted object is the corresponding
Zariski object with quasi-coherent cohomology.
2. Apply lem-sfb-flat-ambient-relative-pseudocoherence to the identity closed immersion
of the source chart into itself, with its flat locally finitely presented map to the
target chart. Derived pushforward by the identity is the identity, so relative
pseudo-coherence on that chart is equivalent to absolute scheme pseudo-coherence.
3. If the left condition holds, apply step 2 to a surjective source presentation.
The local bounded-above finite-free models on its Zariski opens pull back to etale
models. For every etale object W over X, the scheme cover W times_X U and the pulled
back Zariski opens give the same models, by lem-trf-space-fibre-products-etale-covers
and lem-sfb-space-derived-etale-chart-calculus. Represent K by a K-injective complex;
its restrictions remain K-injective by lem-pur-kinjective-restrict-localized. Thus the
local derived identifications are represented by quasi-isomorphisms into that fixed
representative, by lem-sc-kinjective-quasi-iso-comparison. Covering transitivity gives
exactly def-sfb-space-pseudocoherent-complex, with locally varying bounds.
4. Conversely restrict the absolute finite-free models to any source chart. For each
integer m their stupid truncations in degrees at least m are bounded finite-free:
they induce cohomology isomorphisms above m and a surjection in degree m. Apply
lem-sfb-etale-pseudocoherence-descent and the Zariski/etale equivalence to obtain
absolute scheme pseudo-coherence. Step 2 gives relative pseudo-coherence on the
chart, hence relative m-pseudo-coherence for every m. The charts were arbitrary,
so this is the left condition. Covers, embeddings and models may vary with m. -/
theorem pseudoCoherentRelativeTo_iff_of_flat_locallyOfFinitePresentation
    [hD : ∀ Z : Scheme.{u},
      HasDerivedCategory.{wS} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hflat : MapIsFlat f) (hlfp : MapIsLocallyOfFinitePresentation f)
    [HasDerivedCategory.{w} X.SmallModules]
    (K : X.DerivedModules) (hK : X.derivedQCohProperty K) :
    (∀ (m : ℤ) (U : X.EtaleSite) (V : Y.EtaleSite) (h : U.obj.left ⟶ V.obj.left)
      (comm : U.obj.hom ≫ f.hom.hom = yoneda.map h ≫ V.obj.hom),
      @Scheme.IsMPseudoCoherentRelativeTo hD _ _ h.left
        (@instLocallyOfFiniteTypeOfLocallyOfFinitePresentation _ _ h.left
          (hlfp U.obj.left V.obj.left U.obj.hom V.obj.hom h U.property V.property comm))
        m (derivedSchemeRestriction X U K)) ↔ X.IsPseudoCoherent K := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
