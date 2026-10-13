/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Coordinate naturality of the derived base-change mate

Source: Stacks Project, Tags 08HY, 0D5S and 0D5T.
(blueprint: lem-pc-derived-base-change-coordinate-naturality).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- Changing coordinates of a cartesian square transports its derived base-change mate.
Source: Stacks Project, Tag 08HY, adjoint description; Tags 0D5S and 0D5T, composition.
(blueprint: lem-pc-derived-base-change-coordinate-naturality).

Proof: The pullback universal property applied to g' and f' followed by eT gives
an isomorphism e from X' to P. Its two projections are g' and f' followed by eT.
Put U = R(e.hom)_* and T = R(eT.inv)_*. Composition of derived direct images
along e.hom, q and eT.inv gives k. Since e is an isomorphism, its inverse pullback
and its direct image are naturally isomorphic, by uniqueness of the right adjoint
to its pullback equivalence. Derived pullback composition along p and e gives j.
The same argument for eS and eT gives a on the source functors. Choose all these
comparisons using mates of the coherent pullback composition comparisons fixed
in schemeDerivedBaseChangeMap, rather than unrelated adjunction structures.
Transpose the asserted equation under the second-projection adjunction. The
composition comparisons and their unit laws cancel eS, eT and e with their
inverses. The two transposes are then Lg'^* applied to the counit of f. Naturality
of that counit and associativity of pullback composition identify them. The Hom
equivalence is injective, so the original arrows agree, naturally in E. This
argument uses no module comparison and no invertibility of the base-change map;
it also works for empty schemes and for the zero object. -/
theorem exists_derivedBaseChange_coordinate_naturality
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (sq : IsPullback g' f' f g)
    {A B : Scheme.{u}} (eS : S ≅ A) (eT : S' ≅ B) :
    let fA := f ≫ eS.hom
    let gA := eT.inv ≫ g ≫ eS.hom
    let p := pullback.fst fA gA
    let q := pullback.snd fA gA
    let T := schemeDerivedDirectImage eT.inv
    ∃ e : X' ≅ pullback fA gA,
      e.hom ≫ p = g' ∧ e.hom ≫ q = f' ≫ eT.hom ∧
      ∃ j : derivedPullback g' ⋙ schemeDerivedDirectImage e.hom ≅ derivedPullback p,
      ∃ k : schemeDerivedDirectImage f' ≅
          schemeDerivedDirectImage e.hom ⋙ schemeDerivedDirectImage q ⋙ T,
      ∃ a : schemeDerivedDirectImage f ⋙ derivedPullback g ≅
          schemeDerivedDirectImage fA ⋙ derivedPullback gA ⋙ T,
        ∀ E : schemeDerivedCategory X,
          schemeDerivedBaseChangeMap f f' g g' sq.w E ≫
              k.hom.app ((derivedPullback g').obj E) ≫
              T.map ((schemeDerivedDirectImage q).map (j.hom.app E)) =
            a.hom.app E ≫ T.map
              (schemeDerivedBaseChangeMap fA q gA p pullback.condition E) := by sorry

end AlgebraicGeometry
