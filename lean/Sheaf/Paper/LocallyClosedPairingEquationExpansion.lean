/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module
public import Sheaf.Paper.InternalAdjunctionPairingChange
public import Sheaf.Paper.EtaleLocallyClosedShriek
public import Sheaf.Paper.NormalizedComparisonWord
/-! # Expansion of the locally closed pairing equation
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Etale.CoefficientPairingChange
attribute [local irreducible] derivedHom derivedTensor upperStar lowerStar
attribute [local irreducible] internalAdjunction evaluationComparison
  ordinaryComparison compactComparison etaleShriekLocallyClosedCoefficientMap
/-- Expansion of the locally closed pairing equation into its categorical word.
Source: thm-coef-finite-hom, proof paragraph 4.
(blueprint: lem-coef-locally-closed-pairing-cancellation).
The assertion is obtained by unfolding `PairingChangeEquation` and reassociating the
functor map. -/
theorem pairingEquation_expanded
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {S Z X : Scheme.{u}} (φ : A →+* B) (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategoryModule A S) (M : DerivedCategoryModule A X)
    (b : (scalarExtension φ S).obj ((exceptional A g j).obj M) ≅
      (exceptional B g j).obj ((scalarExtension φ X).obj M))
    (hp : PairingChangeEquation φ g j L M b) :
    ordinaryComparison φ g j
        (((derivedHom (ModuleCat A) S).obj (op L)).obj ((exceptional A g j).obj M)) ≫
      (star B g j).map
        (evaluationComparison φ S L ((exceptional A g j).obj M) ≫
          ((derivedHom (ModuleCat B) S).obj
            (op ((scalarExtension φ S).obj L))).map b.hom) ≫
      internalAdjunction B g j ((scalarExtension φ S).obj L) ((scalarExtension φ X).obj M) ≫
      ((derivedHom (ModuleCat B) X).map (compactComparison φ g j L).op).app
        ((scalarExtension φ X).obj M) =
    (scalarExtension φ X).map (internalAdjunction A g j L M) ≫
      evaluationComparison φ X ((shriek A g j).obj L) M := by
  sorry

end AlgebraicGeometry.Etale.CoefficientPairingChange
