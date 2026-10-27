module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
import Sheaf.AlgebraicGeometry.FerrandSchemePushout

/-! # Ferrand scheme pushouts agree with algebraic-space pushouts

Source: Stacks Project, Spaces Pushouts, Tag 0EDP, with the hypotheses of More on Morphisms,
Situation `situation-pushout-along-closed-immersion-and-integral`
(blueprint: lem-sfb-ferrand-pushout-space-agreement).

Maps from schemes into algebraic spaces are natural transformations from their relative
Yoneda presheaves. Thus every morphism and its unique extension are over the specified base.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A Ferrand scheme pushout has the same universal property for algebraic-space targets.
Source: Stacks Project, Spaces Pushouts, Tag 0EDP
(blueprint: lem-sfb-ferrand-pushout-space-agreement).

Proof:
1. Apply `lem-sfb-ferrand-scheme-pushout` to the stated closed immersion, integral map and
   affine neighbourhoods. Uniqueness of scheme colimits identifies its pushout with `P`.
   The quotient-topology clause gives joint surjectivity of the legs. The scheme universal
   property is also relative over `S`: a candidate extension is over `S` because its two
   composites to `S` agree on both legs, so scheme-pushout uniqueness makes them equal.
2. By the converse of `lem-sfb-ferrand-etale-scheme-patching`, every etale scheme `U` over
   `P` is the pushout of its pullbacks to `X` and `T` along its pullback to `Z`. This holds
   without separatedness or quasi-compactness of `U` over `P`. Uniqueness again makes this
   a relative pushout over `S`.
3. A cartesian compatible family of separated etale schemes on the span identifies its
   two pullbacks to `Z`. The forward clause of `lem-sfb-ferrand-etale-scheme-patching`
   glues it to an etale scheme over `P`, with its prescribed component identifications.
4. Apply `lem-sfb-scheme-colimit-upgrade-space-targets` (Stacks 07SX) to the finite span
   category. Steps 1, 2 and 3 verify joint surjectivity, stability under etale scheme base
   change, and effectivity of separated etale families. Its conclusion is the bijection
   between maps from `P` to `H` and compatible families on the span. Such a family is
   precisely `f` and `g` agreeing on `Z`, giving the asserted unique extension.
-/
theorem ferrand_pushout_space_agreement
    (S : Scheme.{u}) (Z X T P : Over S)
    (i : Z ⟶ X) (j : Z ⟶ T) (a : X ⟶ P) (b : T ⟶ P)
    [IsClosedImmersion i.left] [IsIntegralHom j.left]
    (hAffine : ∀ t : T.left, ∃ U : X.left.Opens, IsAffineOpen U ∧
      ∀ z : Z.left, j.left z = t → i.left z ∈ U)
    (hPushout : IsPushout i.left j.left a.left b.left) :
    ∀ (H : AlgebraicSpace S) (f : yoneda.obj X ⟶ H.obj.obj)
      (g : yoneda.obj T ⟶ H.obj.obj),
      yoneda.map i ≫ f = yoneda.map j ≫ g →
      ∃! h : yoneda.obj P ⟶ H.obj.obj,
        yoneda.map a ≫ h = f ∧ yoneda.map b ≫ h = g := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
