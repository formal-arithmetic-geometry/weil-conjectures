/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison

/-! # Leray comparison and the base-change mate
Source: Stacks Project, cohomology.tex, Remark 08HY; duality.tex, Tag 0AA8,
lemma-more-base-change, final comparison diagrams.
(blueprint: lem-sc-global-sections-base-change-mate).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- Leray transfers the base-change mate of any map between sheaf complexes.
This statement has no internal Hom or tensor-Hom input.
Source: Stacks Project, cohomology.tex, Remark 08HY; duality.tex, Tag 0AA8,
lemma-more-base-change, final comparison diagrams.
(blueprint: lem-sc-global-sections-base-change-mate).

Proof: write the adjunction transpose of a as unit followed by direct image of a.
Naturality of the Leray isomorphism moves a to the final direct-image factor.
For the units, expand beta as the canonical pullback-composition comparison and
counit, transpose under g and f', and cancel the adjacent unit and counit by the
triangle identity. This identifies both maps with the unit along the common
composite X' to Y. The composition comparisons for derived global sections are
unique comparisons compatible with the right-derived units. Resolve by
K-injective complexes and use that the underived global-sections/direct-image
comparison is the identity on sections; the scalar-composition comparisons
are the identity module comparisons too. Consequently the identification of
the two scalar paths is exactly schemeGlobalScalarSquareIso. The derived
universal property extends this unit identity to every E, and naturality
then gives the displayed identity for a. -/
theorem schemeGlobalSections_baseChange_mate
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (E : schemeDerivedCategory X) (E' : schemeDerivedCategory (pullback f g))
    (a : (derivedPullback (pullback.fst f g)).obj E ⟶ E') :
    (schemeGlobalScalarRestriction f).map
        ((schemeDerivedGlobalSections X).map
          ((schemeHomPullbackAdjunction (pullback.fst f g)).homEquiv _ _ a) ≫
          (schemeGlobalSectionsDirectImageIso (pullback.fst f g)).hom.app E') ≫
      (schemeGlobalScalarSquareIso f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition).hom.app ((schemeDerivedGlobalSections (pullback f g)).obj E') ≫
      (schemeGlobalScalarRestriction g).map
        ((schemeGlobalSectionsDirectImageIso (pullback.snd f g)).inv.app E') =
    (schemeGlobalSectionsDirectImageIso f).inv.app E ≫
      (schemeDerivedGlobalSections Y).map
        ((schemeHomPullbackAdjunction g).homEquiv _ _
          (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
            pullback.condition E ≫
            (schemeDerivedDirectImage (pullback.snd f g)).map a)) ≫
      (schemeGlobalSectionsDirectImageIso g).hom.app
        ((schemeDerivedDirectImage (pullback.snd f g)).obj E') := by sorry

end AlgebraicGeometry
