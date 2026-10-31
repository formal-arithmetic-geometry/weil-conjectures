/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientPairingChange.InternalAdjunctionPairingChange
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleLocallyClosedShriek
public import WeilConjectures.CategoryTheory.Normalized.NormalizedComparisonWord
import WeilConjectures.AlgebraicGeometry.CoefficientPairingChange.LocallyClosedPairingEquationExpansion
/-! # Cancellation of the locally closed pairing equation

Source: thm-coef-finite-hom, proof paragraph 4.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Etale.CoefficientPairingChange
attribute [local irreducible] derivedHom derivedTensor upperStar lowerStar
attribute [local irreducible] internalAdjunction evaluationComparison
  ordinaryComparison compactComparison etaleShriekLocallyClosedCoefficientMap
/-- Cancellation of the inverse internal-adjunction factor in the pairing equation.
Source: thm-coef-finite-hom, paragraph 4
(blueprint: lem-coef-locally-closed-pairing-cancellation).
Proof: expand `PairingChangeEquation`, reassociate, use functoriality of scalar extension,
and rewrite `inv I ≫ I = 𝟙`. -/
theorem pairingCancellation
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {S Z X : Scheme.{u}} (φ : A →+* B) (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategoryModule A S) (M : DerivedCategoryModule A X)
    [IsIso (internalAdjunction A g j L M)]
    [IsIso (ordinaryComparison φ g j
      (((derivedHom (ModuleCat A) S).obj (op L)).obj ((exceptional A g j).obj M)))]
    [IsIso (evaluationComparison φ S L ((exceptional A g j).obj M))]
    [IsIso (etaleShriekLocallyClosedCoefficientMap φ g j M)]
    [IsIso (compactComparison φ g j L)]
    (hp : PairingChangeEquation φ g j L M
      (asIso (etaleShriekLocallyClosedCoefficientMap φ g j M))) :
    MappedComparisonEquation (scalarExtension φ X) (star B g j)
    (derivedHom (ModuleCat B) X) (internalAdjunction A g j L M)
    (ordinaryComparison φ g j
      (((derivedHom (ModuleCat A) S).obj (op L)).obj ((exceptional A g j).obj M)))
    (evaluationComparison φ S L ((exceptional A g j).obj M))
    (((derivedHom (ModuleCat B) S).obj (op ((scalarExtension φ S).obj L))).map
      (etaleShriekLocallyClosedCoefficientMap φ g j M))
    (compactComparison φ g j L) ((scalarExtension φ X).obj M)
    (internalAdjunction B g j ((scalarExtension φ S).obj L) ((scalarExtension φ X).obj M))
    (evaluationComparison φ X ((shriek A g j).obj L) M)   := by
  unfold MappedComparisonEquation
  apply CategoryTheory.cancelMappedPairing
    (scalarExtension φ X) (star B g j)
    (internalAdjunction A g j L M)
    (ordinaryComparison φ g j
      (((derivedHom (ModuleCat A) S).obj (op L)).obj ((exceptional A g j).obj M)))
    (evaluationComparison φ S L ((exceptional A g j).obj M))
    (((derivedHom (ModuleCat B) S).obj (op ((scalarExtension φ S).obj L))).map
      (etaleShriekLocallyClosedCoefficientMap φ g j M))
    (internalAdjunction B g j ((scalarExtension φ S).obj L) ((scalarExtension φ X).obj M))
    (((derivedHom (ModuleCat B) X).map (compactComparison φ g j L).op).app
      ((scalarExtension φ X).obj M))
    (evaluationComparison φ X ((shriek A g j).obj L) M)
  exact pairingEquation_expanded φ g j L M (asIso
    (etaleShriekLocallyClosedCoefficientMap φ g j M)) hp

end AlgebraicGeometry.Etale.CoefficientPairingChange
