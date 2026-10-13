/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison
public import Sheaf.AlgebraicGeometry.MixedGlobalSectionsDirectImageIso
public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition

/-! # Sections of the base-change unit square with independent universes
Source: Stacks Project, cohomology.tex, Tags 08HY and 0D5T.
(blueprint: lem-sc-mixed-sections-base-change-unit-square).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w wA
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

/-- Taking sections of the unit description of sheaf base change gives this identity
over the global ring of Y. No affine or quasi-coherence hypothesis is needed.
It concerns only the canonical unit at E, and constructs no extension isomorphism.
Source: Stacks Project, cohomology.tex, Remark 08HY and Lemma 0D5T.
(blueprint: lem-sc-mixed-sections-base-change-unit-square).

Proof:
1. Expand schemeDerivedBaseChangeMap as the f'-adjunct of the pullback-composition
comparison followed by Lg_X* of the counit of f. Apply the g-adjunction unit.
Naturality of the units moves the composition comparison through the adjunct.
The triangle identity for f cancels its counit with its unit. What remains is the
unit for g_X followed by the mate of the pullback-composition comparison, namely
the direct-image composition comparison of Tag 0D5T.
2. Apply RΓ_Y to this equation. The normalized Leray isomorphisms for f, g, f',
and g_X replace sections of the composed direct images with the two restrictions
of sections on X'. On underived sheaves these isomorphisms act identically on
sections. Equality of the two scalar actions is precisely pullback.condition;
schemeGlobalScalarSquareIso is the corresponding identity comparison.
3. On K-injective representatives the two composite comparisons are therefore
identical. Their right-derived-unit equations, supplied by
exists_mixedGlobalSectionsDirectImageIso and the derived direct-image composition
comparison, identify them on the full derived categories by the universal property
of right derivation. Thus the equality from step 1 becomes the displayed equality.
The sheaf and module localizations are separate, so their universe levels can differ.
This is an equality of maps, not an invertibility statement: E=0, identity maps,
empty schemes, and nonflat g all satisfy it without extra assumptions. -/
theorem mixedSectionsBaseChange_unit_square
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (E : schemeDerivedCategory X) :
    (schemeDerivedGlobalSections Y).map
        ((schemeHomPullbackAdjunction g).unit.app ((schemeDerivedDirectImage f).obj E)) ≫
      (mixedGlobalSectionsDirectImageIso g).hom.app
        ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj E)) ≫
      (schemeGlobalScalarRestriction g).map
        ((schemeDerivedGlobalSections Y').map
            (schemeDerivedBaseChangeMap f (pullback.snd f g) g
              (pullback.fst f g) pullback.condition E) ≫
          (mixedGlobalSectionsDirectImageIso (pullback.snd f g)).hom.app
            ((derivedPullback (pullback.fst f g)).obj E)) =
      (mixedGlobalSectionsDirectImageIso f).hom.app E ≫
        (schemeGlobalScalarRestriction f).map
          ((schemeDerivedGlobalSections X).map
              ((schemeHomPullbackAdjunction (pullback.fst f g)).unit.app E) ≫
            (mixedGlobalSectionsDirectImageIso (pullback.fst f g)).hom.app
              ((derivedPullback (pullback.fst f g)).obj E)) ≫
        (schemeGlobalScalarSquareIso f (pullback.snd f g) g (pullback.fst f g)
          pullback.condition).hom.app
            ((schemeDerivedGlobalSections (pullback f g)).obj
              ((derivedPullback (pullback.fst f g)).obj E)) := by sorry

end AlgebraicGeometry
