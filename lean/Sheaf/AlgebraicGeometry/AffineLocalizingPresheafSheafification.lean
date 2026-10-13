/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Module.LocalizedModule.Away

/-! # Sheafification on affine opens of a localizing module presheaf

Source: Stacks Project, Tags 01HV and 009Q, applied to the principal-open basis.
(blueprint: lem-pc-affine-localizing-presheaf-sheafification).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- A module presheaf whose principal restrictions on every affine open are
localizations already has the correct sections on affine opens after sheafification.
Source: Stacks Project, Tags 01HV and 009Q.
(blueprint: lem-pc-affine-localizing-presheaf-sheafification).

Proof: Fix an affine W = Spec A and put N = P(W). For each a in A, the hypothesis
identifies P(D(a)) with N[1/a], carrying restriction from W to the numerator map.
For D(c) contained in D(a), naturality of P and uniqueness of the map from a
localization show that its restriction is the standard localization restriction.
Thus on the principal-open basis of W, P agrees with the associated module sheaf
of N (01HV). In particular it satisfies the sheaf condition on that basis,
including the empty cover since localization at zero is zero. The sheaf-on-basis
extension theorem (009Q) extends this agreement uniquely. Restriction of
sheafification to W is the sheaf associated to the restricted presheaf: both
are universal for maps to sheaves and their stalks agree. Since the basis
presheaf is already a sheaf on a basis, its extension agrees with the associated
sheaf, with the canonical unit giving the agreement on basis opens. W itself
is D(1), so the unit on W is bijective and hence an isomorphism of modules.
The argument only uses affine intersections inside W; T need not be separated.
For empty W, a = 0 = 1 forces P(W) = 0, so the same assertion holds. -/
theorem isIso_sheafificationUnit_app_of_affine_localizing
    (T : Scheme.{u}) (P : _root_.PresheafOfModules.{u} T.ringCatSheaf.obj)
    (hP : ∀ (W : T.Opens), IsAffineOpen W → ∀ a : Γ(T, W),
      IsLocalizedModule.Away a (P.map (homOfLE (T.basicOpen_le a)).op).hom)
    (W : T.Opens) (hW : IsAffineOpen W) :
    IsIso (((PresheafOfModules.sheafificationAdjunction
      (𝟙 T.ringCatSheaf.obj)).unit.app P).app (op W)) := by sorry

end AlgebraicGeometry.Scheme.Modules
