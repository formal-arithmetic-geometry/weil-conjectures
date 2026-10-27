/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.CategoryTheory.SiteStackification
public import Sheaf.CategoryTheory.GroupoidStackificationLocalDescription
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.SpaceChangeBase
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus
import Sheaf.AlgebraicGeometry.RelativeFiniteHilbertGroupoids
import Sheaf.AlgebraicGeometry.OpenStackAlgebraicLfp
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.FlatUnramifiedFormallyEtale
import Sheaf.AlgebraicGeometry.EtaleLocalInfinitesimalSmoothCriterion
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion
import Mathlib.AlgebraicGeometry.Limits

/-! # Algebraicity from a representable fppf algebraic-space cover

Source: Stacks Project, criteria.tex, Tag 06DC (theorem-bootstrap), with algebraic-space
source; Tag 05XW for the diagonal argument
(blueprint: lem-sfb-fppf-stack-algebraicity-bootstrap).

The hypothesis retains an equivalence over each test scheme and tests the actual
projection on all representable étale scheme charts. Surjectivity uses the existing
chart-point predicate, equivalently lifting field-valued points after a field extension.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- An fppf stack covered representably by an algebraic space with surjective flat
locally finitely presented scheme base changes is algebraic.

Source: Stacks Project, criteria.tex, Tag 06DC (theorem-bootstrap), with source A;
Tag 05XW (lemma-flat-finite-presentation-surjective-diagonal)
(blueprint: lem-sfb-fppf-stack-algebraicity-bootstrap).

Proof:
1. For y₁,y₂ over T their isomorphism presheaf I is an fppf sheaf. Set
   Aᵢ = A ×_Y,yᵢ T, B = A ×_S T and P = A₁ ×_B A₂. These are spaces by
   lem-trf-space-fibre-products-etale-covers and lem-sfb-space-change-base-to-integers.
   A point of P is a common a and isomorphisms αᵢ : f(a) ≅ yᵢ. Map it to
   α₂ α₁⁻¹ in I. Over any φ in I(Z), the pullback identifies with A₁ ×_T Z:
   choose α₁ and put α₂ = φ α₁. By lem-sfb-space-fppf-covering-calculus this
   projection is surjective flat locally finitely presented. Apply
   lem-sfb-fppf-space-atlas-bootstrap to make I a space, proving representability
   of the diagonal without assuming it.
2. For each d ≥ 1 form H_d and its lci open L_d by
   def-sfb-relative-finite-hilbert-groupoids. Apply
   lem-sfb-relative-finite-hilbert-algebraic and
   lem-sfb-relative-finite-hilbert-lci-open, then lem-sfb-open-stack-algebraic-lfp.
   Choose a smooth surjective scheme atlas V_d → L_d using
   def-sfb-algebraic-moduli-stack. Its composite g_d : V_d → Y is representable
   by step 1 and lem-sfb-stack-diagonal-space-source-representability.
3. The open inclusion L_d → H_d is étale, hence locally finitely presented, by
   lem-weil-pbc-open-immersion-etale and def-weil-etale-morphism. The smooth
   atlas also has that property by def-sbc-smooth-morphisms and
   lem-sfb-space-local-properties-chart-test. For an affine directed limit and
   an object v over it with specified identification over a stage of Y, descend
   its H_d object by lem-sfb-relative-finite-hilbert-limit-descent. Descend its
   L_d object and finally v by lem-sfb-representable-lfp-object-limit-test,
   retaining the comparison isomorphisms. Apply the converse of that test to
   obtain local finite presentation of every scheme base change of g_d.
4. For a square-zero affine thickening and a compatible object of V_d on its
   closed subscheme, lem-sfb-relative-finite-hilbert-lci-lift lifts its L_d
   object. The smooth space V_d ×_L_d T' has the prescribed closed point.
   Choose a surjective étale scheme chart. Its pullback to the closed subscheme
   is a surjective étale scheme cover, by lem-trf-space-fibre-products-etale-covers.
   Lift that cover by sbc-lem-thickening-etale-site, take affine open pieces,
   and use formal smoothness from def-sbc-smooth-morphisms to lift their maps
   to the chart. Projection yields étale-local compatible object lifts to V_d.
5. Fix T → Y and Z_d = V_d ×_Y T. A surjective étale scheme chart W → Z_d
   is locally finitely presented over T by step 3 and
   lem-sfb-space-local-properties-chart-test. Step 4 lifts a square-zero test
   étale locally to Z_d. The étale scheme pullback W ×_Z_d B' extends its
   prescribed closed section by def-weil-etale-morphism and
   lem-weil-pbc-flat-unramified-formally-etale. Thus W has étale-local lifts.
   Apply lem-sfb-etale-local-infinitesimal-lifts-smooth. Then
   lem-sfb-scheme-etale-source-target-properties and
   lem-sfb-space-etale-presentation-property-criterion give smoothness of Z_d → T.
6. For any field object y, A_y is nonempty and locally finitely presented.
   By lem-sfb-relative-finite-hilbert-lci-field it has an unramified lci finite
   locally free family of positive degree d. The 2-fibre-product comparison
   is exactly an object of L_d by def-sfb-relative-finite-hilbert-groupoids.
   Surjectivity of V_d → L_d gives a lift after a field extension, so the
   maps g_d are jointly surjective on field-valued objects.
7. Form V = ∐ V_d in the chosen universe by lem-weil-pbc-scheme-coproduct-family
   and def-weil-size-convention. Stack descent on the disjoint open cover
   glues the g_d to g : V → Y. Step 1 and
   lem-sfb-stack-diagonal-space-source-representability make g representable.
   Each scheme pullback decomposes into the open pieces Z_d, so it is smooth
   by step 5 and lem-weil-pbc-smooth-local-on-source; step 6 gives surjectivity.
   Étale covers are fppf by lem-sfb-space-fppf-covering-calculus, hence Y is
   an étale stack. Together with the diagonal and g, this is exactly
   def-sfb-algebraic-moduli-stack.

For a space over T, SpaceMapIsSurjective is equivalent to field-extension lifting:
restrict to Spec κ(t), lift the resulting point, and then take a point of an étale
chart above it. Conversely a chart point has a residue field extending the given
field and gives the required lift. Thus the predicate includes empty test schemes
and imposes no section over the original field. -/
theorem fppf_stack_algebraicity_bootstrap
    {S : Scheme.{u}} (Y : BasedCategory.{v, w} (Over S))
    (hstack : IsFppfModuliStack Y) (A : AlgebraicSpace S)
    (f : BasedFunctor (discreteModuli A.obj.obj) Y)
    (hcover : ∀ (T : Over S) (y : BasedFunctor (discreteModuli (yoneda.obj T)) Y),
      ∃ (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange f T y Z p ∧
          (∀ (U : Over S) (b : yoneda.obj U ⟶ Z.obj.obj), AlgebraicSpace.IsEtale b →
            Flat (yoneda.preimage (b ≫ p)).left ∧
              LocallyOfFinitePresentation (yoneda.preimage (b ≫ p)).left) ∧
          SpaceMapIsSurjective Z T p) :
    IsAlgebraicModuliStack Y := by
  sorry

end CategoryTheory
