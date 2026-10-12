/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.CurveCoefficientPair
public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.Curve.FinitePushforwardConstructibleDescent
import Sheaf.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.SixFunctors.Finite.Stalk

/-! # Coefficient hypotheses for finite direct images

Source: Stacks Project, Lemma 0A5D and Tags 03QP, 095G, 09BH.
(blueprint: g1-finite-pushforward-coefficient-control)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Coefficient hypotheses descend from finite direct image.
Source: Stacks Project, Lemma 0A5D (lemma-finite-pushforward-statements), the primary-part
argument and the constructibility converse supplied by Tags 03QP, 095G and 09BH
(blueprint: g1-finite-pushforward-coefficient-control).

Proof:
1. The finite stalk formula identifies each source stalk with a direct factor of the
   direct-image stalk at its image. The projection is surjective: extend an element by
   zero in the other factors. Thus an annihilating power of p, or a positive integer
   invertible on Spec k, for the extended element also annihilates its projection.
   This proves the first and third clauses, including p = 0 and p = 1. For a separably
   closed point, extend its field to an algebraic closure; this purely inseparable
   extension induces the same geometric stalk, so the argument applies to the points
   used by the recorded predicates as well.
2. For constructibility, first forget the ULift Z action. A finitely generated torsion
   Z-module is finite, so finite local constancy in the module predicate is precisely
   finite local constancy of the underlying abelian sheaf. The equivalence with modules
   preserves pullback and these local trivializations. Use the same stratifications to
   identify this condition with CurveCoefficientPair.IsConstructible.
3. Apply CurveCoefficientPair.isConstructible_of_finite_pushforward to these abelian
   sheaves. Its torsion hypothesis holds by the finite stalk formula and the torsion
   characterization. Concretely, the counit is surjective on stalks, being projection
   to the selected factor, so the source sheaf is a quotient of the pullback of its
   constructible direct image. On Noetherian curves, pullback and torsion quotients
   preserve constructibility. Finally apply the coefficient equivalence to the source
   stratification to recover the module predicate. The equivalence adds no module data
   beyond the canonical Z action and preserves the underlying additive stalks. -/
theorem IsCurve.finite_pushforward_coefficient_control {k : Type u} [Field k] [IsAlgClosed k]
    (P : CurveCoefficientPair k) {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [IsCurve g] (f : P.C ⟶ Y) [IsFinite f]
    (hf : f ≫ g = P.toSpec) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    let FX := (sheafCompose P.C.smallEtaleTopology E).obj P.F
    let G := (Etale.lowerStar AddCommGrpCat.{u + 1} f).obj P.F
    let FY := (sheafCompose Y.smallEtaleTopology E).obj G
    (∀ p : ℕ, Scheme.IsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) FY p →
        Scheme.IsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) FX p) ∧
      (Scheme.IsConstructibleSheaf FY → Scheme.IsConstructibleSheaf FX) ∧
      (Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) FY →
        Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) FX) := by
  sorry

end AlgebraicGeometry
