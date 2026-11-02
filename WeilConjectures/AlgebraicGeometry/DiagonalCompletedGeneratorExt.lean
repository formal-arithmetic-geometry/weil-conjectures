/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalSupportedCoefficientLimit
import all WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalSupportedCoefficientLimit
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAbelianClosedCounit
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Supported.DiagonalTraceSupportedOrdinaryFiniteUnit

/-! # Detection by the integral generator on a finite supported target -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
open DiagonalTrace

/-- The supported integral generator detects maps to every finite-torsion supported sheaf.

Source: blueprint latest, diagonal coefficient changes (3), source-cone comparison;
the local integer approximation for completed coefficients.
(blueprint: lem-diagonal-completed-generator-ext).

Proof: identify the underlying completed source with closed direct image of the
additive completed coefficient sheaf. Closed direct image is fully faithful, so
the two maps are direct images of unique maps on the projective line. The generator
identity descends to equality after the integer-cast map. Evaluate it on the
constant integer one. The completed-coefficient extensionality lemma now applies:
locally a coefficient is an integer plus l^(n+1) times another coefficient, and the
second summand maps to zero. Apply closed direct image and transport back to the
original underlying source. The argument covers n=0 and the empty base. -/
theorem diagonalCompletedGenerator_hom_ext (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u}) (n : ℕ)
    (Q : Sheaf (Scheme.ProEt.topology (ProjectiveLine Y)) Ab.{u + 1})
    (hQ : ∀ (V : (ProjectiveLine Y).ProEtᵒᵖ) (y : Q.obj.obj V),
      l ^ (n + 1) • y = 0)
    (f g : (diagonalForget l (diagonalSurface Y)).obj
        ((diagonalCompletedRestriction l (diagonalSurface Y)).obj
          (diagonalCompletedSource l Y)) ⟶
      (lowerStar Ab.{u + 1} (diagonalImmersion Y)).obj Q)
    (h : diagonalCompletedGenerator l Y ≫ f = diagonalCompletedGenerator l Y ≫ g) :
    f = g := by
  let F := lowerStar Ab.{u + 1} (diagonalImmersion Y)
  have : IsIso (upperStarLowerStarAdjunction Ab.{u + 1}
      (diagonalImmersion Y)).counit := abelian_closed_counit _
  let ff := (upperStarLowerStarAdjunction Ab.{u + 1}
    (diagonalImmersion Y)).fullyFaithfulROfIsIsoCounit
  let : F.Full := ff.full
  let : F.Faithful := ff.faithful
  let e := completedUnderlyingIso l Y
  let a := diagonalCoefficientIntegerMap (ProjectiveLine Y)
    (Scheme.purTwistZlCompletion (ProjectiveLine Y) l)
  let f₀ := F.preimage (e.inv ≫ f)
  let g₀ := F.preimage (e.inv ≫ g)
  have hf : F.map f₀ = e.inv ≫ f := F.map_preimage _
  have hg : F.map g₀ = e.inv ≫ g := F.map_preimage _
  have hgen : a ≫ f₀ = a ≫ g₀ := by
    apply F.map_injective
    rw [F.map_comp, F.map_comp, hf, hg]
    have ha : F.map a = diagonalCompletedGenerator l Y ≫ e.hom :=
      (completedGenerator_eq l Y).symm
    rw [ha]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h
  have hfg : f₀ = g₀ := by
    apply completedMap_ext l (ProjectiveLine Y) n Q f₀ g₀ hQ
    intro V
    let η := toSheafify (Scheme.ProEt.topology (ProjectiveLine Y))
      ((Functor.const (ProjectiveLine Y).ProEtᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    have he := congrArg (fun t ↦ t.hom.app V (η.app V (ULift.up (1 : ℤ)))) hgen
    change f₀.hom.app V (a.hom.app V (η.app V (ULift.up (1 : ℤ)))) =
      g₀.hom.app V (a.hom.app V (η.app V (ULift.up (1 : ℤ)))) at he
    have ha : a.hom.app V (η.app V (ULift.up (1 : ℤ))) =
        (1 : (Scheme.purTwistZlCompletion (ProjectiveLine Y) l).obj.obj V) := by
      simpa only [Int.cast_one] using
        integerMap_sections (ProjectiveLine Y)
          (Scheme.purTwistZlCompletion (ProjectiveLine Y) l) V (1 : ℤ)
    simpa only [ha] using! he
  apply (cancel_epi e.inv).mp
  rw [← hf, ← hg, hfg]

end AlgebraicGeometry.ProEtale
