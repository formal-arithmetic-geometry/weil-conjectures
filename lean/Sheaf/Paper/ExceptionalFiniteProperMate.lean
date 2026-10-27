/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F8
-/
module

public import Sheaf.Paper.ExceptionalSystemInterfaces

/-! # The finite proper direct-image mate in the strict coefficient presentation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory SheafOfModules
namespace AlgebraicGeometry

/-- The proper mate is invertible on bounded-below finite etale coefficient objects.
Source: Stacks 099R and 0B65; the canonical finite-coefficient direct-image comparison;
Zheng Lemma 4.10 and Construction 5.15.
(blueprint: lem-sf-exceptional-finite-proper-mate).

Proof: identify modules over the constant finite quotient-ring sheaf with sheaves
of modules over that ring on each site. The ordinary lifts in the comparison
records have their specified geometric underlying pullbacks and their specified
constant scalar actions, so these identifications intertwine their inverse images.
Their universal exact localizations and right-derived direct images are uniquely
identified with the fixed-coefficient derived operations. The representative
normalization of the supplied proper square identifies its localized square with
the usual inverse-image comparison. Taking mates therefore identifies the displayed
map, including its units and counits, with the canonical fixed-coefficient proper
comparison. The latter is invertible for a proper (hence qcqs) morphism on bounded-
below inputs. Transport its inverse back through those identifications. Finiteness
is used for the etale/pro-etale comparison. No open-extension or exceptional-right-
adjoint property is part of this assertion. -/
theorem exceptionalFiniteProperMate
    {O : Type (u + 1)} [CommRing O] {ell : O}
    [∀ n : ℕ, Finite (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {S : StrictEtaleCompactSupport O ell c}
    {CX : ExceptionalSystemSiteComparison O ell X S.PX}
    {CY : ExceptionalSystemSiteComparison O ell Y S.PY}
    {CZ : ExceptionalSystemSiteComparison O ell c.Z S.PZ}
    {P : ExceptionalProCompactSupport O ell c
      CX.proEvaluation CY.proEvaluation CZ.proEvaluation}
    (R : ExceptionalSystemCompactificationComparison S CX CY CZ P)
    (n : ℕ) (M : DerivedCategory (strictEtaleLevel c.Z O ell n))
    (hM : ∃ a : ℤ, M.IsGE a) :
    IsIso ((mateEquiv (S.properDerived.level n).adjunction
      (P.val.properDerived.level n).adjunction
      (.mk _ _ _ _ (R.properSquare.derivedLevel n).hom)).app M) := by sorry

end AlgebraicGeometry
