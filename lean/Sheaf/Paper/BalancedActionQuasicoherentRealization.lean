/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.AlgebraicGeometry.RelativeSpecBaseChange
import Sheaf.AlgebraicGeometry.AffineModuleCorrespondence

/-! # Realization of a balanced algebra action

Source: Stacks Project, Tags 01LX and 01SB, as used in Tag 0897.
(blueprint: lem-weil-pbc-balanced-action-quasicoherent-realization).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry

/-- A quasi-coherent module with a balanced action of `B` comes from the base change
by `Spec B`, with an identification respecting every scalar in `B`.

Source: Stacks Project, Tags 01LX and 01SB; Tag 0897, relative-spectrum paragraph.
(blueprint: lem-weil-pbc-balanced-action-quasicoherent-realization).

Proof: On an affine open U = Spec C, take N = M(U). The ring map rho gives a
B-action on N. Each rho(b) is O_X-linear, so this action commutes with C. The
scalar hypothesis identifies the two A-actions, and therefore defines a
C tensor_A B-module by (c tensor b)n = c rho(b)n. Quasi-coherence of M identifies
N localized at c with M(D(c)). Naturality of rho makes the B-actions on these
localizations agree with restriction. These modules glue over affine overlaps
(refined by basic affine opens) to a module over f^*(B tilde), with underlying
O_X-module M. Relative-spectrum base change (01LX) identifies that algebra
with pi_* O_Y and its relative spectrum with Y. The final assertion of 01SB
identifies quasi-coherence over pi_* O_Y with quasi-coherence of the underlying
O_X-module, so the constructed algebra module is quasi-coherent. The equivalence
in 01SB then realizes it as pi_* F for a quasi-coherent F. Its
algebra-linear unit is the required isomorphism e. Under the algebra identification,
b is the section fB^sharp(b), so algebra-linearity gives the displayed equality.
No finite generation or noetherian hypothesis is used. For M = 0 the construction
gives F = 0; for empty X all modules and maps are the unique ones. -/
theorem balancedAction_quasicoherent_realization
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (M : X.Modules) (hM : M.IsQuasicoherent)
    (rho : B →+* End M)
    (hscalar : ∀ a : A, rho (algebraMap A B a) =
      M.smulHom (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a)) :
    let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
    let Y := pullback f g
    let pi : Y ⟶ X := pullback.fst f g
    let fB : Y ⟶ Spec (.of B) := pullback.snd f g
    ∃ (F : Y.Modules), F.IsQuasicoherent ∧
      ∃ (e : M ≅ (Scheme.Modules.pushforward pi).obj F),
        ∀ b : B, rho b ≫ e.hom = e.hom ≫
          (Scheme.Modules.pushforward pi).map
            (F.smulHom (((Scheme.ΓSpecIso (.of B)).inv ≫ fB.appTop).hom b)) := by sorry

end AlgebraicGeometry
