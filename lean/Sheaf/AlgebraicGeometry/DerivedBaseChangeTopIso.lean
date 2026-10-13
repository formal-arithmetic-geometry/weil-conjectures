/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap

/-! # Transport of the derived mate at the upper-left vertex

Source: Stacks Project, Tags 08HY, 0D5S and 0D5T.
(blueprint: lem-pc-derived-base-change-top-iso).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

/-- Change only the upper-left scheme of a commutative square by an isomorphism.
Source: Stacks Project, Tag 08HY (counit description), Tags 0D5S and 0D5T.
(blueprint: lem-pc-derived-base-change-top-iso).

Proof: Use the pullback comparisons c and identity comparisons i selected by
exists_derivedPullbackComposition, and their pinned derived adjunctions used in
schemeDerivedBaseChangeMap. The comparisons for e.hom e.inv and e.inv e.hom,
followed by i, exhibit L(e.hom)^* and L(e.inv)^* as inverse equivalences.
Uniqueness of the right adjoint, with its pinned unit and counit, supplies
R(e.hom)_* ≅ L(e.inv)^*. The equality e.hom p = g' and the pullback comparison
give Lg'^* ≅ Lp^* L(e.hom)^*. Compose on the right with R(e.hom)_* and cancel
L(e.hom)^* R(e.hom)_* by the inverse of the pinned adjunction unit; this defines j.
The equality e.hom q = f'
and the right-adjoint mate of c e.hom q give k : Rf'_* ≅ R(e.hom)_* Rq_*.
Transpose the asserted equation under Lq^* ⊣ Rq_*. The definition of k as the
mate of c identifies its effect on a transpose with applying R(e.hom)_* to the
transpose under Lf'^* ⊣ Rf'_*. Substitute the counit definition of each base-change
map. On the left this leaves the comparison identifying Lf'^* Lg^* with Lg'^* Lf^*,
followed by Lg'^* of the counit of f, and then j. Naturality of j moves that counit
past j. The associativity law for c, applied to e.hom, q and g, identifies the
remaining comparison with the comparison identifying Lq^* Lg^* with Lp^* Lf^*.
The unit laws cancel e.hom and e.inv in j. This is precisely the transpose of the
right-hand base-change map. Injectivity of the Hom equivalence proves equality.
No cartesian hypothesis is used. Identity e gives the unit laws; empty schemes
and zero E are included, since all steps are identities of natural transformations. -/
theorem exists_derivedBaseChange_top_iso
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S P S' X' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (p : P ⟶ X) (q : P ⟶ S') (h : p ≫ f = q ≫ g)
    (e : X' ≅ P) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (hp : e.hom ≫ p = g') (hq : e.hom ≫ q = f')
    (h' : g' ≫ f = f' ≫ g) :
    ∃ j : derivedPullback g' ⋙ schemeDerivedDirectImage e.hom ≅ derivedPullback p,
    ∃ k : schemeDerivedDirectImage f' ≅
        schemeDerivedDirectImage e.hom ⋙ schemeDerivedDirectImage q,
      ∀ E : schemeDerivedCategory X,
        schemeDerivedBaseChangeMap f f' g g' h' E ≫
            k.hom.app ((derivedPullback g').obj E) ≫
            (schemeDerivedDirectImage q).map (j.hom.app E) =
          schemeDerivedBaseChangeMap f q g p h E := by sorry

end AlgebraicGeometry
