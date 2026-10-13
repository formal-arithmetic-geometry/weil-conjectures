/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison
public import Sheaf.AlgebraicGeometry.MixedGlobalExtension
public import Sheaf.AlgebraicGeometry.MixedGlobalSectionsDirectImageIso
public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Sheaf.AlgebraicGeometry.DerivedCategory
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition

/-! # Affine sections transport the base-change mate with independent universes
Source: Stacks Project, Tags 0AA7, 08HY and 0D5T.
(blueprint: lem-sc-mixed-affine-sections-base-change-mate).
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

/-- Restricted derived sections intertwine the two base-change mates.
This does not assume flatness, perfectness, or invertibility of sheaf base change.
Only Rf_*E is required to have quasi-coherent cohomology.
Source: Stacks Project, perfect.tex, Tag 0AA7, construction of the canonical map;
cohomology.tex, Tags 08HY (counit description) and 0D5T (Leray).
(blueprint: lem-sc-mixed-affine-sections-base-change-mate).

Proof:
1. Identify each affine base with the spectrum of its global ring by isoSpec.
   Derived direct-image composition identifies restricted RΓ_X E with RΓ_Y Rf_*E.
   On sheaves this comparison is the identity on sections. Derive it with its
   right-derived-unit equation, as for mixedGlobalSectionsDirectImageIso.
2. Rf_*E is quasi-coherent. The affine derived equivalence and the tilde/pullback
   formula on K-flat representatives identify RΓ_Y' Lg^*Rf_*E with derived
   extension of RΓ_Y Rf_*E. Uniqueness of the left adjoint to the fixed derived
   restriction identifies this extension with mixedGlobalExtension g, including
   its unit. Compose with extension of the inverse comparison from step 1 to
   obtain a. Direct-image composition gives the natural target comparison d.
3. Transpose the displayed right-hand composite under the fixed scalar adjunction.
   Expand sheaf base change as the mate of pullback composition and the counit
   for f. Naturality moves m past that counit; the adjunction triangle identities
   cancel the paired units and counits. Direct-image composition leaves RΓ_X(m)
   followed by Leray for g_X. The identity on underived sections and the
   right-derived-unit equation identify this with mixedGlobalSectionsDirectImageIso.
   The scalar-square identification is the equality of the two restricted actions.
4. The scalar adjunction Hom equivalence is injective, giving the stated equality
   simultaneously for all L and m. These computations take place in the sheaf
   and module localizations separately, so their universe levels need not agree.
   Zero E or an empty base gives the same identity on zero objects. -/
theorem exists_mixedAffineSectionsBaseChangeMate
    {X Y Y' : Scheme.{u}} [IsAffine Y] [IsAffine Y']
    (f : X ⟶ Y) (g : Y' ⟶ Y) (E : schemeDerivedCategory X)
    (hE : schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E)) :
    ∃ a : (mixedGlobalExtension g).obj
        ((schemeGlobalScalarRestriction f).obj ((schemeDerivedGlobalSections X).obj E)) ≅
        (schemeDerivedGlobalSections Y').obj
          ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj E)),
      ∃ d : schemeDerivedDirectImage (pullback.snd f g) ⋙ schemeDerivedGlobalSections Y' ≅
          schemeDerivedGlobalSections (pullback f g) ⋙
            schemeGlobalScalarRestriction (pullback.snd f g),
        ∀ (L : schemeDerivedCategory (pullback f g))
          (m : E ⟶ (schemeDerivedDirectImage (pullback.fst f g)).obj L),
          ((mixedGlobalExtensionAdjunction g).homEquiv _ _).symm
              ((schemeGlobalScalarRestriction f).map
                  ((schemeDerivedGlobalSections X).map m ≫
                    (mixedGlobalSectionsDirectImageIso (pullback.fst f g)).hom.app L) ≫
                (schemeGlobalScalarSquareIso f (pullback.snd f g) g (pullback.fst f g)
                  pullback.condition).hom.app ((schemeDerivedGlobalSections
                    (pullback f g)).obj L)) =
            a.hom ≫ (schemeDerivedGlobalSections Y').map
              (schemeDerivedBaseChangeMap f (pullback.snd f g) g
                (pullback.fst f g) pullback.condition E) ≫
              (schemeDerivedGlobalSections Y').map
                ((schemeDerivedDirectImage (pullback.snd f g)).map
                  (((schemeHomPullbackAdjunction (pullback.fst f g)).homEquiv E L).symm m)) ≫
              d.hom.app L := by sorry

end AlgebraicGeometry
