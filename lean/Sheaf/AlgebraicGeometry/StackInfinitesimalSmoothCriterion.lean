/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Thickening
import WeilConjectures.AlgebraicGeometry.FormallySmooth
import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Infinitesimal smoothness criterion for an algebraic stack

Source: Stacks Project, Tags 0DP0 (lemma-smooth-formally-smooth) and 0DNY
(lemma-reformulate-formal-smoothness), with scheme target
(blueprint: lem-sfb-stack-infinitesimal-smooth-criterion).

The lifting hypothesis uses arrows of the total category lying over the thickening.
In a category fibred in groupoids every arrow is cartesian, so such an arrow is
exactly a lift together with an isomorphism from its restriction to the original object.
This formulation requires no choice of cleavage or pullback functor.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- An algebraic stack locally of finite presentation over a scheme is smooth if
objects lift, up to isomorphism, across every affine first order thickening.
Source: Stacks Project, Tags 0DP0 and 0DNY
(blueprint: lem-sfb-stack-infinitesimal-smooth-criterion).

Proof: (1) Choose the smooth surjective atlas `U` with locally finitely presented
structural map supplied by `hfp`, using def-sfb-algebraic-moduli-stack. Test formal
smoothness of `U → S` on an affine first order thickening `i : T → T'` and an
`S`-map `u : T → U`, as in def-sbc-formally-smooth.
(2) Apply `hlift` to the image of `u` in the stack, retaining the isomorphism between
its lift's restriction and that image. The atlas base change `Z = T' ×_F U` is an
algebraic space smooth over `T'`. The triple consisting of `i`, `u` and this
isomorphism defines a map `s : T → Z` above `i`; this is the explicit two-fibre
product of def-sfb-stable-pointed-moduli-groupoids.
(3) Apply lem-sfb-smooth-space-affine-infinitesimal-lift to `Z → T'`, `i`, `s` and
the identity of `T'`. It supplies a section `s' : T' → Z` restricting to `s`.
Projection to `U` yields an `S`-map extending `u`. Thus `U → S` is formally smooth.
(4) Its local finite presentation and formal smoothness imply scheme smoothness
by def-sbc-smooth-morphisms (Stacks 02H6). The original smooth surjective atlas now
has smooth structural composite, which is exactly `IsSmoothModuliStack F`. -/
theorem isSmoothModuliStack_of_affine_firstOrder_lifting
    {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S))
    (hF : IsAlgebraicModuliStack F)
    (hfp : ∃ (U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
      IsSmoothModuliAtlas F U a ∧ LocallyOfFinitePresentation U.hom)
    (hlift : ∀ (T T' : Over S) (i : T ⟶ T'),
      IsAffine T.left → IsAffine T'.left → IsFirstOrderThickening i.left →
      ∀ (x : F.obj), F.p.obj x = T →
        ∃ (x' : F.obj) (a : x ⟶ x'), F.p.IsHomLift i a) :
    IsSmoothModuliStack F := by
  sorry

end CategoryTheory
