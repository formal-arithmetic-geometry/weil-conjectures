/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # The open-diagonal criterion for unramified algebraic-space morphisms

Source: Stacks Project, Morphisms of Spaces, Tag 05W1
(lemma-diagonal-unramified-morphism), part (2)
(blueprint: lem-sfb-space-unramified-open-diagonal).

Local finite type and unramifiedness use the existing all-compatible-charts test.
The relative diagonal is the diagonal of the underlying sheaf map, viewed in presheaves;
limits of sheaves are computed on their underlying presheaves. Its open-immersion property
uses the existing representable scheme-test predicate.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally finite type morphism of algebraic spaces whose relative diagonal is an
open immersion is unramified on all compatible etale scheme charts.
Source: Stacks Project, Morphisms of Spaces, Tag 05W1(2)
(blueprint: lem-sfb-space-unramified-open-diagonal).

Proof:
1. Fix any compatible etale charts a : U → X and b : V → Y and a scheme map
h : U → V with f a = b h. The local finite type hypothesis says that h is locally
of finite type, using def-weil-finite-type-morphism and def-weil-unramified-morphism.
No surjectivity is required of these particular charts.
2. Put Q = X ×_Y X, an algebraic space by lem-trf-space-fibre-products-etale-covers,
and P = U ×_Y U, a scheme by lem-trf-space-representable-etale-scheme-tests.
The map P → Q is a composite of two base changes of a, hence representable etale:
the intermediate product is X ×_Y U. The pullback identifications forget the repeated
X coordinate, with inverse inserting a(u).
3. Put E = V ×_Y V and D = U ×_V U, both schemes. The map E → Y is etale,
so its comparison map V → E is etale. The square D → V over P → E is cartesian:
a triple (u₁,u₂,v) satisfies h(u₁) = v = h(u₂), and forgetting v identifies it with
D. Thus D → P, and consequently D → Q, are representable etale. These scheme tests,
base changes, composites and comparison maps use
lem-trf-space-representable-etale-scheme-tests.
4. The open diagonal X → Q is representable etale, since open immersions of schemes
are etale by lem-weil-pbc-etale-composition-cancellation. Thus U → X → Q is etale.
The diagonal δ : U → D commutes with these maps to Q. Comparison between the two
schemes U and D etale over Q makes δ etale, by the same scheme-test lemma.
5. The diagonal δ is a monomorphism, since either projection recovers its argument.
By def-weil-etale-morphism it is flat and locally of finite presentation. Then
lem-pe-flat-lfp-monomorphism-open makes δ an open immersion. Together with Step 1,
def-weil-unramified-morphism gives IsUnramified h. As the compatible chart diagram
was arbitrary, this proves the required chartwise unramifiedness of f. -/
theorem unramified_of_open_diagonal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (hft : MapIsLocally (@LocallyOfFiniteType) f)
    (hdiag : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left)
      (pullback.diagonal f.hom.hom)) :
    MapIsLocally (@AlgebraicGeometry.IsUnramified) f := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
