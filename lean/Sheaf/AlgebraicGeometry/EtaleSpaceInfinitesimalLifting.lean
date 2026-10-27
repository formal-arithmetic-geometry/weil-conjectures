/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import WeilConjectures.AlgebraicGeometry.Thickening
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.FlatUnramifiedFormallyEtale

/-! # Unique infinitesimal lifting for étale algebraic spaces

Source: Stacks Project, More on Morphisms of Spaces, Tag 0616, (1) implies (2),
and Tag 04GC (definition-formally-etale), with the affine square-zero lifting convention
of definition-formally-smooth-etale-unramified
(blueprint: lem-sfb-etale-space-infinitesimal-lifting).

Étaleness is tested on all compatible étale scheme charts. Maps from test schemes
are natural transformations from their representable presheaves over the base.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- An étale morphism of algebraic spaces has exactly one lift in each affine
first order thickening diagram.
Source: Stacks Project, More on Morphisms of Spaces, Tags 0616 and 04GC
(blueprint: lem-sfb-etale-space-infinitesimal-lifting).

Proof: (1) Fix any compatible étale scheme charts `a : U → E`, `c : V → Y`
and `h : U → V`. The chartwise étaleness hypothesis makes `h.left` étale.
By [def-weil-etale-morphism], it is flat and unramified, as well as locally
of finite presentation; only the first two properties are needed.
(2) Given an affine first order thickening diagram for `h`, regard its target test
scheme as a scheme over `V` using the lower arrow, and its source test scheme via
composition with the thickening. Apply [lem-weil-pbc-flat-unramified-formally-etale]
to `h.left`. It gives a unique lift over `V`, which is automatically over `S`.
Thus the affine square-zero unique lifting property holds on every compatible chart.
(3) Apply the reverse implication of [lem-sfb-formally-etale-space-chart-locality],
Stacks Tag 04GD, to obtain that property for `p`. Its specialization to `i`, `e₀`
and `b` gives precisely both equations in the conclusion and uniqueness. -/
theorem etale_unique_affine_thickening_lift
    {S : Scheme.{u}} {E Y : AlgebraicSpace S} (p : E ⟶ Y)
    (hp : MapIsLocally (@Etale) p)
    (T₀ T : Over S) [IsAffine T₀.left] [IsAffine T.left] (i : T₀ ⟶ T)
    (hi : IsFirstOrderThickening i.left)
    (b : yoneda.obj T ⟶ Y.obj.obj) (e₀ : yoneda.obj T₀ ⟶ E.obj.obj)
    (w : e₀ ≫ p.hom.hom = yoneda.map i ≫ b) :
    ∃! e : yoneda.obj T ⟶ E.obj.obj,
      yoneda.map i ≫ e = e₀ ∧ e ≫ p.hom.hom = b := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
