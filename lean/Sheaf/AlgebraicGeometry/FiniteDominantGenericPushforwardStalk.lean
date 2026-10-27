module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Topology.Sober
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import Sheaf.TraceFormula.LocalDimensionFormula
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import WeilConjectures.AlgebraicGeometry.AffinePushforwardStalkLocalization

/-!
# Generic stalk of a finite dominant direct image

Source: Stacks Project, varieties.tex, Tag 0AYZ,
lemma-degree-pullback-map-proper-curves, first sentence of the proof;
the generic-stalk identification used in the rank calculation.
(blueprint: lem-sfb-finite-dominant-generic-pushforward-stalk)

The comparison is the actual map on germs, with its scalar compatibility stated
against `Scheme.Hom.dominantFunctionFieldAlgebra`. Bijectivity of this ring map
together with that compatibility says exactly that it is a function-field algebra
isomorphism. No choice of an abstract field isomorphism is involved.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The canonical map from the generic stalk of `f_* O_X` to `k(X)`: identify
`f (genericPoint X)` with `genericPoint Y` using dominance, then apply Mathlib's
`stalkPushforward`. Thus the germ of a section on `f ⁻¹ᵁ V` goes to its germ at
`genericPoint X`. The equality of points follows directly by taking closures of
images of the generic point, so the construction requires no postponed proof.
Source: Stacks Project, varieties.tex, Tag 0AYZ, generic-rank calculation, and
morphisms.tex, lemma-dominant-between-integral, implication (1) to (2).
(blueprint: lem-sfb-finite-dominant-generic-pushforward-stalk) -/
def Scheme.Hom.genericPushforwardStalkMap
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] :
    ((TopCat.Presheaf.pushforward CommRingCat f.base).obj X.presheaf).stalk
        (genericPoint Y) ⟶ X.functionField :=
  let h : f (genericPoint X) = genericPoint Y := by
    refine ((genericPoint_spec Y).eq ?_).symm
    have hi := (genericPoint_spec X).image f.continuous
    rw [Set.image_univ, f.denseRange.closure_range] at hi
    exact hi
  ((TopCat.Presheaf.pushforward CommRingCat f.base).obj X.presheaf).stalkSpecializes
      (specializes_of_eq h) ≫
    TopCat.Presheaf.stalkPushforward CommRingCat f.base X.presheaf (genericPoint X)

/-- For a finite dominant morphism of integral schemes the canonical generic-stalk
map is an isomorphism of `k(Y)`-algebras. The first conjunct is bijectivity of the
ring map. In the second, the source scalar map is the stalk at `genericPoint Y`
of `f.c : O_Y ⟶ f_* O_X`; the target scalar map is exactly the recorded dominant
function-field algebra. Multiplicativity then gives compatibility with scalar
multiplication on every element.
Source: Stacks Project, varieties.tex, Tag 0AYZ,
lemma-degree-pullback-map-proper-curves, first proof sentence.
(blueprint: lem-sfb-finite-dominant-generic-pushforward-stalk)

Proof:
1. The generic point maps to the generic point: continuity gives that the image
   lies in the closure of the image of the source generic point, and dominance
   makes this closure all of Y. Use uniqueness of generic points
   (def-sc-generic-point, def-weil-locally-ringed-space-morphism,
   lem-sc-scheme-sober).
2. Choose an affine open V containing the target generic point. Finiteness makes
   U = f⁻¹V affine, containing the source generic point. Their section rings A,B
   are domains and B is finite over A (def-weil-finite-integral-morphism,
   def-pc-integral-scheme). The actual germs identify k(Y), k(X) with their
   fraction fields (lem-sc-integral-function-field-affine-fraction). The square
   of germs and the dominant function-field map commutes, so A → B is injective
   (def-sfb-dominant-function-field-map,
   def-weil-locally-ringed-space-morphism).
3. The prime of V corresponding to the target generic point is zero: zero is
   prime in a domain and its closure is the entire spectrum, so apply uniqueness
   (def-weil-affine-spectrum, def-sc-generic-point, lem-sc-scheme-sober).
4. By lem-sc-affine-pushforward-stalk-localization the actual germ B → C, where
   C = (f_* O_X) at the generic point, localizes B at the images of A minus zero.
   Every element has the form b/a, and the specified comparison sends it to the
   identical fraction in k(X).
5. Finite implies integral (pqf-lem-finite-integral-lft). For nonzero b in B take
   a monic equation, include its leading coefficient 1, and choose the least i
   with nonzero coefficient a_i. Cancel b^i in the domain B to obtain
   phi(a_i) + b*d = 0. Here i is less than the degree, since otherwise b is
   nilpotent. In C the image of phi(a_i) is invertible, so the inverse of the
   image of b is -d/phi(a_i). This uses only the monic equations of
   def-weil-finite-integral-morphism.
6. If a fraction b/a maps to zero in k(X), injectivity of the germ from B gives
   b = 0, hence the fraction was zero. Conversely every element of k(X) is b/b'
   with b' nonzero by lem-sc-integral-function-field-affine-fraction; step 5
   already inverted b' in C. Thus the canonical ring map is bijective.
7. Write a scalar in k(Y) as a/a'. Its action on C is through the germ of the
   pullback section, by def-weil-pbc-module-stalk. The commuting germ square of
   step 2 sends it to the image of a/a' under precisely the algebra map of
   def-sfb-dominant-function-field-map. This proves the displayed scalar-map
   equality, and multiplicativity gives scalar compatibility for every element.
-/
theorem Scheme.Hom.finite_dominant_generic_pushforward_stalk
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f] :
    Function.Bijective (f.genericPushforwardStalkMap) ∧
      ∀ a : Y.functionField,
        f.genericPushforwardStalkMap
            (((TopCat.Presheaf.stalkFunctor CommRingCat (genericPoint Y)).map f.c) a) =
          @algebraMap Y.functionField X.functionField _ _
            (Scheme.Hom.dominantFunctionFieldAlgebra f) a := by
  sorry

end AlgebraicGeometry
