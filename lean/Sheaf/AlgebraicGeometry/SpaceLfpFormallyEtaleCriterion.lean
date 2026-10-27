/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import WeilConjectures.AlgebraicGeometry.Thickening
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # The infinitesimal criterion for étaleness of algebraic spaces

Source: Stacks Project, More on Morphisms of Spaces, Tag 0616, implication (2) to (1),
and Tag 04GC (blueprint: lem-sfb-space-lfp-formally-etale-criterion).

Local finite presentation and étaleness use the existing test on all compatible étale
scheme charts. The infinitesimal hypothesis is written out on affine schemes over the base.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally finitely presented morphism of algebraic spaces with unique lifts across
all affine first order thickenings is étale on every compatible pair of étale scheme charts.
Source: Stacks Project, More on Morphisms of Spaces, Tag 0616, (2) implies (1),
with formal étaleness as in Tag 04GC
(blueprint: lem-sfb-space-lfp-formally-etale-criterion).

Proof: (1) Fix any compatible diagram of representable étale scheme charts `U → X`,
`V → Y`, and `h : U → V`. The local finite presentation assumption gives local finite
presentation of `h`. Apply [lem-sfb-formally-etale-space-chart-locality], the forward
implication of Stacks Tag 04GD, to transfer the unique affine first order lifting property
from `f` to `h`.
(2) For an arbitrary affine scheme lifting problem for `h`, give its target test scheme
`T` the base map `T → V → S`, and give `T₀` its composite base map. The commutative
square makes `a₀` a map over `S`. Every lift with composite `b` to `V` is automatically
over `S`, so existence and uniqueness over `S` give existence and uniqueness among all
scheme lifts. This is elementary base-structure bookkeeping.
(3) Apply [lem-sfb-lfp-unique-infinitesimal-lifts-etale], Stacks Tag 02HM, to `h`.
It is étale. Since the compatible chart diagram was arbitrary, `MapIsLocally (@Etale) f`
holds, exactly the chartwise meaning of étaleness stipulated by the node. -/
theorem etale_on_charts_of_lfp_of_unique_affine_thickening_lifts
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hlfp : MapIsLocallyOfFinitePresentation f)
    (hlift : ∀ (T₀ T : Over S) [IsAffine T₀.left] [IsAffine T.left]
      (j : T₀ ⟶ T), IsFirstOrderThickening j.left →
      ∀ (a₀ : yoneda.obj T₀ ⟶ X.obj.obj) (b : yoneda.obj T ⟶ Y.obj.obj),
        a₀ ≫ f.hom.hom = yoneda.map j ≫ b →
        ∃! a : yoneda.obj T ⟶ X.obj.obj,
          yoneda.map j ≫ a = a₀ ∧ a ≫ f.hom.hom = b) :
    MapIsLocally (@Etale) f := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
