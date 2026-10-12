/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.AlgebraicGeometry.ConstructibleTorsionCurveSheaf
public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift

/-!
# DenseOpenVanishingComparison

Source: Stacks Project, Lemma 0GJA.
(blueprint: lem-pbc-j2-dense-open-vanishing-comparison).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Source: Stacks Project, Lemma 0GJA, proof, with Lemma 095L.
(blueprint: lem-pbc-j2-dense-open-vanishing-comparison).

Proof: Give the closed complement Z its reduced induced scheme structure. Density excludes all
generic points, so Z is a finite set of k-rational closed points, also after intersecting
with any open. Apply the open-closed short exact sequence to F. Its third term i_* i^* F
has no positive cohomology: finite direct image is exact and its cohomology is the
cohomology on Z, a finite union of spectra of algebraically closed fields. The long exact
sequence gives the displayed additive equivalences in degrees q > 1, after identifying
the abelian sheaves with the ones obtained through the coefficient equivalence E.
For primary vanishing in the forward direction, primary torsion is inherited by the
subsheaf and quotient; both outer terms have vanishing cohomology above one. In the reverse
direction, if F is primary for the characteristic, use the same equivalences. If F has
invertible torsion and G is primary for a positive characteristic, every stalk of G has
both primary and invertible order and is zero. Geometric stalk conservativity makes G
zero, so its cohomology vanishes. In characteristic zero the primary assertion is vacuous.
-/
theorem IsCurve.dense_open_vanishing_comparison {k : Type u} [Field k] [IsAlgClosed k]
    (P : CurveCoefficientPair k) (hP : P.IsConstructible)
    (U : P.C.Opens) (hU : Dense (U : Set P.C)) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    let F := (sheafCompose P.C.smallEtaleTopology E).obj P.F
    let F' := (Etale.openImmersionLowerShriek AddCommGrpCat.{u + 1} U.ι).obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj P.F)
    let G := (sheafCompose P.C.smallEtaleTopology E).obj F'
    (∀ q : ℕ, 1 < q → Nonempty
      (Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
        AddCommGrpCat.{u + 1})).obj G) q ≃+
       Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
        AddCommGrpCat.{u + 1})).obj F) q)) ∧
    (IsCurve.VanishingAboveOneOfIsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) G k →
      IsCurve.VanishingAboveOneOfIsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) F k) ∧
    ((Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F ∨
      ∃ p : ℕ, p.Prime ∧ CharP k p ∧
        Scheme.IsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) F p) →
      IsCurve.VanishingAboveOneOfIsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) F k →
      IsCurve.VanishingAboveOneOfIsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) G k) := by sorry

end AlgebraicGeometry
