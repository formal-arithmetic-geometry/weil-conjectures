/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.Paper.ProjectionFormulaBaseChangeNaturality
public import Sheaf.Paper.StrictPerfectPackageOnSite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.Paper.OpenImmersionTensorPiece
import Sheaf.Paper.ProEtaleProjectionFormulaArrows
import Sheaf.Paper.ProjectionCompactification
import Sheaf.Paper.ProjectionFormulaCompactified

/-!
# Identity compactification and the projection formula

Source: Weil conjectures blueprint, proper base change, order 1272, identity
compactification lemma; detailed proper_base_change.tex, lines 5600--5616
(blueprint: lemma-weil-pbc-projection-formula-identity-compactification).

We use the normalized presentation of the identity open immersion: its extension
by zero and its restriction are the identity functor, with identity unit and counit.
Thus the definition Rp_* j_! is the actual composite (identity functor) followed by
Rp_*, and the open tensor comparison and composition constraint are identities.
These definitions describe this specific compactification, not arbitrary shriek data.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.IdentityProjectionCompactification

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
  (aY : ProEtaleTensorModel Y R) (aX : ProEtaleTensorModel X S)
  (E : DerivedCategory (proEtaleRingModules X S))
  (Q : DerivedCategory (proEtaleRingModules Y R))

/-- Rp_* j_! for j=1_X, with the normalized exact identity extension by zero.
Source: blueprint order 1272
(blueprint: lemma-weil-pbc-projection-formula-identity-compactification). -/
abbrev directImage := 𝟭 _ ⋙ proEtaleRingDerivedDirectImage f R S c

/-- The open-piece tensor and composite-pullback identifications for the identity open.
Source: blueprint order 1272
(blueprint: lemma-weil-pbc-projection-formula-identity-compactification). -/
def theta := 𝟙 (aX.tensor.obj (E, (proEtaleRingDerivedPullback f R S c).obj Q))

/-- The ordered compactification composite, with its actual final Rp_* theta arrow.
Source: blueprint orders 1271--1272
(blueprint: lemma-weil-pbc-projection-formula-identity-compactification). -/
def forward :
    aY.tensor.obj ((directImage f R S c).obj E, Q) ⟶
      (directImage f R S c).obj
        (aX.tensor.obj (E, (proEtaleRingDerivedPullback f R S c).obj Q)) :=
  proEtaleProjectionFormulaMate f R S c aY aX E Q ≫
    (proEtaleRingDerivedDirectImage f R S c).map (theta f R S c aX E Q)

/-- The canonical mate is invertible at the perfect coefficient used in the formula.
Source: blueprint orders 1271--1272
(blueprint: lemma-weil-pbc-projection-formula-identity-compactification).
Proof: specialize the compactified perfect projection formula to (1_X,f).
The identity open-piece comparison and composite-pullback constraint are identities;
its ordered composite is the projection mate. Its invertibility is therefore exactly
that supplied by the compactified formula. No boundedness of E or global bound for Q
is used. -/
theorem mate_isIso [IsProper f] (hQ : SheafOfModules.IsPerfectOnSmallRingedSite R Q) :
    IsIso (proEtaleProjectionFormulaMate f R S c aY aX E Q) := sorry

variable [hf : IsProper f]

/-- The inverse rho of the same canonical mate, determined by its inverse identities.
Source: blueprint order 1272
(blueprint: lemma-weil-pbc-projection-formula-identity-compactification). -/
def rho (hQ : SheafOfModules.IsPerfectOnSmallRingedSite R Q) :=
  @inv _ _ _ _ (proEtaleProjectionFormulaMate f R S c aY aX E Q)
    (mate_isIso f R S c aY aX E Q hQ)

/-- The reverse ordered compactification composite, with theta inverse followed by rho.
Source: blueprint orders 1271--1272
(blueprint: lemma-weil-pbc-projection-formula-identity-compactification). -/
def backward (hQ : SheafOfModules.IsPerfectOnSmallRingedSite R Q) :=
  (proEtaleRingDerivedDirectImage f R S c).map
    (𝟙 (aX.tensor.obj (E, (proEtaleRingDerivedPullback f R S c).obj Q))) ≫
      rho f R S c aY aX E Q hQ

/-- Identity compactification identifies direct images, theta, the formula and its inverse.
Source: blueprint order 1272, detailed proper_base_change.tex lines 5600--5616
(blueprint: lemma-weil-pbc-projection-formula-identity-compactification).
Proof: (1) For j=1_X, j_! and Lj^* and their unit constraints are identities, so the
left unitor identifies Rp_* j_! with Rp_*. (2) The open tensor comparison and pullback
composition comparison are identities, hence theta=1. (3) Substitute theta=1 in the
ordered forward composite and use preservation of identities. (4) Do the same for
theta inverse in the reverse composite. The result is precisely pi and its rho. -/
theorem identity_compactification
    (hQ : SheafOfModules.IsPerfectOnSmallRingedSite R Q) :
    Nonempty (directImage f R S c ≅ proEtaleRingDerivedDirectImage f R S c) ∧
    theta f R S c aX E Q =
      𝟙 (aX.tensor.obj (E, (proEtaleRingDerivedPullback f R S c).obj Q)) ∧
    forward f R S c aY aX E Q = proEtaleProjectionFormulaMate f R S c aY aX E Q ∧
    backward f R S c aY aX E Q hQ = rho f R S c aY aX E Q hQ := sorry

end AlgebraicGeometry.Scheme.IdentityProjectionCompactification
