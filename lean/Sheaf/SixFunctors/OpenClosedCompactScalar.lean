/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ExceptionalCoefficientMaps
public import Sheaf.SixFunctors.EtaleOpenTensorDefs
public import Sheaf.Paper.EtaleCompactScalarCoherence

/-! # The compact-support coefficient square for two factorizations

Source: the finite dualizing proof, paragraphs 2--3
(blueprint: open-closed-compact-scalar-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- The left-adjoint coefficient square for an open and a closed factorization.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/
lem-coef-finite-dualizing.proof.md, paragraph 3, counit sentence
(blueprint: open-closed-compact-scalar-coherence).

Proof: compare the chosen compactification of j with (j,identity) and that of i
with (identity,i). Remove the identity proper or open functor, respectively.
Compose each normalization with the unbounded compact-support compositor for
j followed by f and i followed by p. The equality j f = i p then gives tA and tB.
The finite-Tor interval of W is preserved by exact open restriction and scalar
extension. Hence the input and its scalar extension are bounded below. Apply
etaleCompactScalarComposition to the two composites on that input and
etaleCompactScalarCoherence to the changes of compactification. The open
normalization is openIso, because its scalar comparison is the same exact
extension-by-zero comparison. The proper normalization is scalarMate, because
its identity-open comparison is the unit comparison. Pasting these four squares
and cancelling the common structural compactification comparison gives the
stated equation. No assertion about exceptional coefficient maps is used. The
identity and empty-open cases use the same identity/zero normalizations. -/
theorem openClosedCompactScalar_coherence
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X V P S : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian V] [IsNoetherian P] [IsNoetherian S]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f]
    (j : V ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (i : V ⟶ P) [IsClosedImmersion i]
    (p : P ⟶ S) [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    [HasCompactification p] (h : j ≫ f = i ≫ p)
    (W : DerivedCategoryModule A X)
    (hW : DerivedCategory.isBoundedConstructible A X W ∧
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A X a b W) :
    ∃ (tA : derivedExtension (A := A) j ⋙
          rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ≅
        rightDerivedLowerStar (ModuleCat.{u + 1} A) i ⋙
          rightDerivedLowerShriek (ModuleCat.{u + 1} A) p)
      (tB : derivedExtension (A := B) j ⋙
          rightDerivedLowerShriek (ModuleCat.{u + 1} B) f ≅
        rightDerivedLowerStar (ModuleCat.{u + 1} B) i ⋙
          rightDerivedLowerShriek (ModuleCat.{u + 1} B) p),
      let L := (derivedRestriction (A := A) j).obj W
      (scalarExtension φ S).map (tA.hom.app L) ≫
          (compactScalarChosenMap φ p).app
            ((rightDerivedLowerStar (ModuleCat.{u + 1} A) i).obj L) ≫
          (rightDerivedLowerShriek (ModuleCat.{u + 1} B) p).map
            ((scalarMate φ i).app L) =
        (compactScalarChosenMap φ f).app ((derivedExtension (A := A) j).obj L) ≫
          (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f).map
            ((ExceptionalCoefficients.openIso φ j).hom.app L) ≫
          tB.hom.app ((scalarExtension φ V).obj L) := by sorry

end AlgebraicGeometry.Etale
