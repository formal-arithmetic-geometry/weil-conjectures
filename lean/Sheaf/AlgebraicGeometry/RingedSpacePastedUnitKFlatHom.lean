/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Homology.KFlatPullback
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral

/-!
# The pasted direct-image unit tested on K-flat complexes

Source: Stacks Project, Cohomology, Tags 079W, 0D5S and 0D5T.
(blueprint: lem-pc-ringed-space-pasted-unit-kflat-hom).
-/

@[expose] public section

universe u wX wY wZ

open CategoryTheory

set_option autoImplicit false

namespace AlgebraicGeometry.RingedSpace

/-- Postcomposition with the pasted derived units induces a Hom bijection when the
source is a localized K-flat complex and the original target is K-injective.
Source: Stacks Project, Cohomology, `lemma-adjoint` (079W),
`lemma-derived-pullback-composition` (0D5S), and the argument of
`lemma-derived-pushforward-composition` (0D5T).
(blueprint: lem-pc-ringed-space-pasted-unit-kflat-hom).

Proof: write H for the homotopy category and P = f* g* for successive tensor
pullback. Pullback preserves K-flatness by `isKFlat_pullback`, so P K computes
Lf* Lg* QK. Choose the derived adjunctions induced from the underived adjunctions,
not arbitrary adjunctions with the same functors. Their Hom equivalences and the
K-injective Hom computation identify Hom(QK, Rg* Rf* QI) with Hom_H(P K, I).

Here is the localization step, which does not treat K-flat as K-projective.
Represent a map QK to Q(g* f* I) by a roof K ←s K' →a g* f* I. Resolve K' by a
K-flat complex K''; replace s and a by their composites with the resolution.
The new s has K-flat endpoints. Successive pullback takes s to a quasi-isomorphism:
on K-flat complexes it computes the derived pullback, which inverts Q(s).
Adjunction takes a to a map b : P K'' → I. The roof defines
Q(b) composed with the inverse of Q(P s), a map Q(P K) to QI, hence a unique
homotopy class P K → I by K-injectivity. Naturality of adjunction makes this
independent of refinement of the roof. Conversely a homotopy class P K → I
has an underived adjunct K → g* f* I, whose localization gives a preimage.
These operations are inverse: for the original roof the composite of this
adjunct with s is homotopic to a, since their adjuncts become equal after
localization and maps into I are computed faithfully in H. This proves both
surjectivity and injectivity, with common refinements for equality of roofs.

Finally apply the unit/counit compatibility for the derived adjunction induced
from the underived adjunction (`Adjunction.derivedε_fac_app`), first for f and
then for g. Under the two derived Hom equivalences the localized underived
adjunct of b : P K → I maps back to that adjunct followed by ηg(f* I) and
Rg*(ηf(I)). Naturality gives the same identity for roofs. Thus precisely the
displayed postcomposition function is the composite of the two Hom bijections.
This expands the adjunction argument of 079W and 0D5T on K-flat representatives;
no preservation of K-injectivity by direct image is used. -/
theorem moduleDirectImage_pastedUnit_kFlat_hom_bijective
    {X Y Z : RingedSpace.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]
    [HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings Z))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ) [I.IsKInjective]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Z)) ℤ) (hK : K.IsKFlat) :
    Function.Bijective (fun
      (a : DerivedCategory.Q.obj K ⟶ DerivedCategory.Qh.obj
        (((moduleDirectImage g).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          (((moduleDirectImage f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)))) =>
      a ≫ (moduleDirectImage g).rightDerivedFunctorUnit.app
          (((moduleDirectImage f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≫
        (derivedModuleDirectImage g).map
          ((moduleDirectImage f).rightDerivedFunctorUnit.app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by sorry

end AlgebraicGeometry.RingedSpace
