/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CurrentPurityConventions.Setting.CurrentPurityConventions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportFiniteLines

/-! # Transport of a finite Tate complement unit to native modules

Source: finite-coefficient comparison in native smooth-divisor bottom descent.
(blueprint: lem-pur-native-finite-restriction-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
namespace WeilConjectures.PurityFiniteSetting

/-- The actual finite Tate restriction unit is preserved by site and scalar comparison.
Source: blueprint smooth-divisor bottom descent, Step 2; Stacks Tags 03PK and 09A6.
Proof: compare the root-normalized finite native line with the section-action encoding
of the finite pro-etale Tate line. The finite root comparison identifies the latter
with inverse image of the etale Tate line. The qcqs direct-image comparison for j
is invertible and its mate equation identifies the image of the etale unit with the
pro-etale unit, followed by the inverse-image comparison. Thus that unit is invertible.
The exact section-action equivalence commutes with direct image by the identity on
sections. Its inverse-image comparison is the adjoint mate of that identity, hence
its unit equation carries this invertibility to the specified native unit. Naturality
transports along the root-normalized line comparison. This is valid for every finite
commutative ell-primary ring, including the zero ring; no flatness over Z/ell^N is used.
(blueprint: lem-pur-native-finite-restriction-unit). -/
theorem nativeFiniteRestrictionUnit_of_etaleUnit
    (ell : ℕ) [Fact ell.Prime] {V T : Scheme.{u}}
    (j : V ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (A : CommRingCat.{0}) (fin : Finite A) (n : ℕ)
    (hA : (ell ^ (n + 1) : A) = 0) (hT : IsUnit (ell : Γ(T, ⊤)))
    (hη : IsIso ((Etale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).unit.app
        (Scheme.finiteEtaleTateSheaf (ULift.{u + 1} A) (ell ^ (n + 1)) T
          (PurityTransport.finiteLiftAnnihilator ell A n hA) 1))) :
    IsIso ((supportPullbackAdjunction
      ((PurityTransport.Coefficient.finite A fin n hA).obj ell) j).unit.app
        ((PurityTransport.Coefficient.finite A fin n hA).firstLine ell T)) := by
  sorry

end WeilConjectures.PurityFiniteSetting
