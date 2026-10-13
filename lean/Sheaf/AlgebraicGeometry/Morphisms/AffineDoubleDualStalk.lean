/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.LinearAlgebra.Dual.Defs

import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Localization.Finiteness

/-! # Localization of an affine finite double dual

Source: Stacks Project, Tags 01HV and 0583, as used in Tag 0EY6.
-/

@[expose] public section

universe u
open CategoryTheory Opposite TopCat.Presheaf
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem dual_stalk_iso
    (A : CommRingCat.{u}) [IsNoetherianRing A] (M : ModuleCat.{u} A)
    [Module.Finite A M] (x : Spec A) :
    Nonempty
      (TopCat.Presheaf.stalk (C := Ab.{u})
          (tilde (ModuleCat.of A (Module.Dual A M))).val.presheaf x
        ≃ₗ[(Spec A).presheaf.stalk x]
          Module.Dual ((Spec A).presheaf.stalk x)
            (TopCat.Presheaf.stalk (C := Ab.{u}) (tilde M).val.presheaf x)) := by
  let R := (Spec A).presheaf.stalk x
  let : Algebra A R := (StructureSheaf.toStalk A x).hom.toAlgebra
  have : IsLocalization x.asIdeal.primeCompl R :=
    inferInstanceAs (IsLocalization x.asIdeal.primeCompl
      ((structurePresheafInCommRingCat A).stalk x))
  have : IsScalarTower A R
      (TopCat.Presheaf.stalk (C := Ab.{u}) (X := PrimeSpectrum.Top A)
        (moduleStructurePresheaf A M).presheaf x) :=
    .of_algebraMap_smul (fun _ _ ↦ rfl)
  have : IsScalarTower A R
      (TopCat.Presheaf.stalk (C := Ab.{u}) (X := PrimeSpectrum.Top A)
        (moduleStructurePresheaf A (Module.Dual A M)).presheaf x) :=
    .of_algebraMap_smul (fun _ _ ↦ rfl)
  have : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  let h := IsLocalizedModule.mapExtendScalars x.asIdeal.primeCompl
    (StructureSheaf.toStalkₗ A M x) (Algebra.linearMap A R) R
  have : IsLocalizedModule x.asIdeal.primeCompl h := inferInstance
  let e := IsLocalizedModule.linearEquiv x.asIdeal.primeCompl
    (StructureSheaf.toStalkₗ A (Module.Dual A M) x) h
  exact ⟨e.extendScalarsOfIsLocalization x.asIdeal.primeCompl R⟩

/-- The stalk of the actual double dual is the double dual of the finite stalk.
Source: Stacks Project, Tags 01HV (associated sheaf stalks) and 0583
(localization of Hom for finite presentations), used in Tag 0EY6.
(blueprint: new-affine-double-dual-stalk)

Proof: Identify the stalk of tilde M at x with the localization M_x over A_x.
Finite generators of M localize to generators, proving finiteness of this stalk.
Both M and Hom_A(M,A) are finitely presented since A is Noetherian. Apply the
localization-Hom isomorphism first to M and then to Hom_A(M,A); composing these
with the associated-sheaf stalk identification gives an A_x-linear isomorphism
between the displayed stalk and Hom_{A_x}(Hom_{A_x}(M_x,A_x),A_x). The algebra
structure and scalar action on A_x are the structure sheaf's canonical ones.
All isomorphisms are canonical; the finiteness witness is a proposition.
For M = 0 both sides are zero; an empty spectrum has no point x. -/
theorem affine_double_dual_stalk
    (A : CommRingCat.{u}) [IsNoetherianRing A] (M : ModuleCat.{u} A)
    [Module.Finite A M] (x : Spec A) :
    ∃ hfinite : Module.Finite ((Spec A).presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) (tilde M).val.presheaf x),
      letI := hfinite
      Nonempty
        (TopCat.Presheaf.stalk (C := Ab.{u})
            (tilde (ModuleCat.of A (Module.Dual A (Module.Dual A M)))).val.presheaf x
          ≃ₗ[(Spec A).presheaf.stalk x]
            Module.Dual ((Spec A).presheaf.stalk x)
              (Module.Dual ((Spec A).presheaf.stalk x)
                (TopCat.Presheaf.stalk (C := Ab.{u}) (tilde M).val.presheaf x))) := by
  let R := (Spec A).presheaf.stalk x
  let : Algebra A R := (StructureSheaf.toStalk A x).hom.toAlgebra
  have : IsLocalization x.asIdeal.primeCompl R :=
    inferInstanceAs (IsLocalization x.asIdeal.primeCompl
      ((structurePresheafInCommRingCat A).stalk x))
  have : IsScalarTower A R
      (TopCat.Presheaf.stalk (C := Ab.{u}) (X := PrimeSpectrum.Top A)
        (moduleStructurePresheaf A M).presheaf x) :=
    .of_algebraMap_smul (fun _ _ ↦ rfl)
  have hfinite : Module.Finite R
      (TopCat.Presheaf.stalk (C := Ab.{u}) (X := PrimeSpectrum.Top A)
        (moduleStructurePresheaf A M).presheaf x) :=
    Module.Finite.of_isLocalizedModule x.asIdeal.primeCompl (StructureSheaf.toStalkₗ A M x)
  refine ⟨hfinite, ?_⟩
  obtain ⟨e₁⟩ := dual_stalk_iso A M x
  obtain ⟨e₂⟩ := dual_stalk_iso A (ModuleCat.of A (Module.Dual A M)) x
  exact ⟨e₂.trans e₁.dualMap.symm⟩

end AlgebraicGeometry.Scheme
