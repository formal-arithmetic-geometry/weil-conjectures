/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Sheaf.AlgebraicGeometry.CurveCoefficientPair
import WeilConjectures.AlgebraicGeometry.Curve.Assertions
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Ring.ULift
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finite pushforward of the eight curve assertions

Source: Stacks Project, Etale Cohomology, Lemma 0A5D (59.83.5)
(blueprint: lem-weil-pbc-curve-assertions-finite-pushforward).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Finite pushforward preserves torsion and transfers each of the eight curve assertions
separately, and therefore their conjunction. Source: Stacks Project, Lemma 0A5D,
Section 03SB (blueprint: lem-weil-pbc-curve-assertions-finite-pushforward).

Abelian sheaves are viewed as modules over `ULift ℤ` through the inverse of the standard
forgetful equivalence, followed by restriction along `ULift.ringEquiv`. This is only a
change of coefficient category, and imposes no extra structure on the abelian sheaf.

Proof (the node's eight steps):
1. The finite stalk formula (lemma-weil-pbc-finite-stalk-formula) expresses a stalk of the
pushforward as a finite product of torsion stalks. The torsion characterizations
(lem-weil-pbc-torsion-sheaf-characterizations) then give torsion of the pushforward.
2. Each source stalk is a direct factor of the pushforward stalk over its image. Thus
p-primary torsion and torsion prime to the characteristic descend from the pushforward.
3. The finite cohomology edge map (lem-weil-pbc-finite-pushforward-cohomology) is an
isomorphism in every degree, identifying vanishing and finiteness on the two schemes.
4. Transfer C1 by this identification. For C2, affineness of Y implies affineness of X;
for C3 use step 2. These use lem-weil-pbc-finite-morphism-permanence.
5. Constructibility descends from the pushforward by
lem-weil-pbc-finite-pushforward-constructible-descent. Combine this with steps 2 and 3
for C4; for C5 also use that finite over proper is proper.
6. For C6 and C7, form the base-change square for an algebraically closed field extension.
Finite exchange (lemma-weil-pbc-finite-exchange) and the finite edge maps are isomorphisms.
Their compatibility (lem-weil-pbc-edge-map-base-change) identifies the two pullback maps.
Pasting identifies the source base change with its field extension; composition
(lem-weil-pbc-cohomology-pullback-functorial and lem-weil-pbc-inverse-image-composition)
transfers bijectivity. Apply step 2 for C6 and properness permanence for C7.
7. For an open immersion into Y, its pullback into X is open and the induced finite
morphism has the same exchange and edge isomorphisms. Compatibility gives a commuting
restriction square; lift the corresponding class by C8 on X and transport it back by
the inverse edge map. Injectivity of the comparison proves that it restricts to the
given class on the open of Y.
8. The eight separate implications give the implication between their conjunctions,
using def-weil-pbc-eight-curve-assertions. Together with step 1 this proves both clauses. -/
theorem IsCurve.finite_pushforward_assertions {k : Type u} [Field k] [IsAlgClosed k]
    (P : CurveCoefficientPair k) {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [IsCurve g] (f : P.C ⟶ Y) [IsFinite f]
    (hf : f ≫ g = P.toSpec) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    let FX := (sheafCompose P.C.smallEtaleTopology E).obj P.F
    let G := (Etale.lowerStar AddCommGrpCat.{u + 1} f).obj P.F
    let FY := (sheafCompose Y.smallEtaleTopology E).obj G
    Y.IsTorsionAbelianSheaf G ∧
      (IsCurve.VanishingAboveTwo (ULift.{u + 1} ℤ) FX →
        IsCurve.VanishingAboveTwo (ULift.{u + 1} ℤ) FY) ∧
      (IsCurve.VanishingAboveOneOfIsAffine (ULift.{u + 1} ℤ) FX →
        IsCurve.VanishingAboveOneOfIsAffine (ULift.{u + 1} ℤ) FY) ∧
      (IsCurve.VanishingAboveOneOfIsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) FX k →
        IsCurve.VanishingAboveOneOfIsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) FY k) ∧
      (IsCurve.FiniteOfInvertibleOrder (ULift.{u + 1} ℤ) FX k →
        IsCurve.FiniteOfInvertibleOrder (ULift.{u + 1} ℤ) FY k) ∧
      (IsCurve.FiniteOfIsProper (ULift.{u + 1} ℤ) P.toSpec FX →
        IsCurve.FiniteOfIsProper (ULift.{u + 1} ℤ) g FY) ∧
      (IsCurve.BaseChangeOfInvertibleOrder (ULift.{u + 1} ℤ) P.toSpec FX →
        IsCurve.BaseChangeOfInvertibleOrder (ULift.{u + 1} ℤ) g FY) ∧
      (IsCurve.BaseChangeOfIsProper (ULift.{u + 1} ℤ) P.toSpec FX →
        IsCurve.BaseChangeOfIsProper (ULift.{u + 1} ℤ) g FY) ∧
      (IsCurve.SurjectiveRestrictionTwo (ULift.{u + 1} ℤ) FX →
        IsCurve.SurjectiveRestrictionTwo (ULift.{u + 1} ℤ) FY) ∧
      (IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec FX →
        IsCurve.Assertions (ULift.{u + 1} ℤ) g FY) := by
  sorry

end AlgebraicGeometry
