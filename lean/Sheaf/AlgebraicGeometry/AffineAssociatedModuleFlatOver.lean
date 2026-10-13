/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic

/-! # The affine-section flatness of an associated flat module

Source: Stacks Project, Tags 01I9 (affine sections and pullbacks) and 00HT (flatness).
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- A flat global-ring module gives an associated module flat over the affine base itself.
This is an affine module/sheaf fact, with no cover, complex or cohomology.
Source: Stacks Project, Tags 01I9 and 00HT.
(blueprint: lem-pc-affine-associated-module-flat-over).

Proof: Write A=Gamma(T,O). The affine chart T -> Spec A is an isomorphism. On an
affine open W of T, the sections of the chart pullback of M tilde identify with
Gamma(W,O) tensor_A M, by the affine pullback formula and the section formula for
tilde. This module is flat over Gamma(W,O) by base change of flat modules. Given
affine W contained in affine Z, the inclusion is a flat morphism, and hence
Gamma(W,O) is flat over Gamma(Z,O). Transitivity gives flatness of the same sections
over Gamma(Z,O). Naturality of the affine pullback formula identifies the action
with the restriction map appearing in IsFlatOver of the identity. These are all
the affine pairs required by that predicate. On empty affine opens the ring and
section module are zero and the same argument applies; zero M is also included.
No quasi-coherence-to-flatness converse for arbitrary sheaves is assumed. -/
theorem flatOver_affineAssociatedModule (T : Scheme.{u}) [IsAffine T]
    (M : ModuleCat.{u} Γ(T, ⊤)) (hM : Module.Flat Γ(T, ⊤) M) :
    ((Modules.pullback T.toSpecΓ).obj ((tilde.functor Γ(T, ⊤)).obj M)).IsFlatOver
      (𝟙 T) := by sorry

end AlgebraicGeometry.Scheme.Modules
