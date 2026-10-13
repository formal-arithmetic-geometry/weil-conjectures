/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.ModuleFiniteTypeSubmoduleExtension
import Sheaf.AlgebraicGeometry.NoetherianQuasicoherentSubmodules
import Sheaf.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine

/-! # Extending a quasi-coherent section from an ideal power

Source: Stacks Project, Tag 01YB, lemma-homs-over-open, structure-module case.
(blueprint: lem-pc-quasicoherent-open-section-ideal-extension)
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- A section on the complement of an ideal support extends from an ideal power.
Source: Stacks Project, Tag 01YB, lemma-homs-over-open, first part of the proof.
(blueprint: lem-pc-quasicoherent-open-section-ideal-extension)

Proof: The image of the section map O_U -> E|U is quasi-coherent of finite type.
Extend it to a finite-type quasi-coherent submodule G of E by 01PF. Since X is
Noetherian, G is coherent. Its increasing quasi-coherent submodules annihilated
by I^r stabilize, say at T = G_r. Artin-Rees gives c such that
I^(r+c)G intersects T trivially. Put G' = I^(r+c)G. On U the ideal is the unit
ideal, so G'|U = G|U. Every I-power annihilator of G' is zero: it lies both in
G' and in T, by stabilization. The sections comparison of 01PQ now identifies
colim Hom(I^n,G') with sections of G' on U, without a quotient by torsion.
Choose a representative for the prescribed section and compose with G' -> E.
On U, I^n is O_U; a linear map from it is multiplication by its value at 1.
This gives the displayed equality on every smaller open, by naturality.
Ideal-sheaf-data powers agree with recursive image powers by the affine power
formula, including n=0. If U is empty the zero map works; the unit ideal,
zero ideal, and zero module obey the same argument. -/
theorem quasicoherent_open_section_ideal_extension
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (E : X.Modules) [E.IsQuasicoherent] (U : X.Opens)
    (hI : (I.support : Set X) = (U : Set X)ᶜ) (s : E.val.obj (op U)) :
    ∃ (n : ℕ) (α : (I ^ n).toModules ⟶ E),
      ∀ (W : X.Opens) (h : W ≤ U) (a : (I ^ n).toModules.val.obj (op W)),
        α.val.app (op W) a =
          (I ^ n).toModulesι.val.app (op W) a • E.val.map (homOfLE h).op s := by
  sorry

end AlgebraicGeometry.Scheme.Modules
