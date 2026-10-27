/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Flat.TorsionFree
import Sheaf.TraceFormula.ValuationFiniteTypeModulePresentation

/-!
# Finite presentation of a flat finite module over a valuation algebra

Source: Stacks Project, `more-algebra.tex`, Lemma Tag 0GSE
(lemma-valuation-ring-flat-essentially-finite-type),
part (2), statement and proof at lines 6005--6044 (blueprint:
lem-trf-valuation-flat-finite-module-presentation).

## Main statement

* `valuation_flat_finite_module_presentation` states that a finite module over a local
  essentially finite type algebra over a valuation ring is finitely presented when it is flat
  over the valuation ring.

This stage-2 statement is recorded by group Q130.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Algebra

/--
A finite module over a local essentially finite type algebra over a valuation ring is finitely
presented when it is flat over the valuation ring.

Source: Stacks Project, `more-algebra.tex`, Lemma Tag 0GSE
(lemma-valuation-ring-flat-essentially-finite-type), part (2), statement and proof at lines
6005--6044 (blueprint: lem-trf-valuation-flat-finite-module-presentation).

Proof: Choose a finite type subalgebra `C` of `B` and a submonoid `W` with
`B` the localization of `C` at `W`. The `C`-span `N` of a finite set of `B`-module
generators of `M` is finite over `C`. As a submodule of the flat `A`-module `M`, it is
torsion-free over `A`, hence flat over the valuation ring. Thus
`valuation_finite_type_module_presentation` makes `N` finitely presented over `C`.
Localizing `N` inside `M` gives the `B`-span of the chosen generators, namely all of `M`.
Finite presentation is preserved by this localization, yielding the result.
-/
theorem valuation_flat_finite_module_presentation
    (A : Type u) (B : Type v) (M : Type w)
    [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
    [AddCommGroup M] [Module B M] [Module A M]
    [IsScalarTower A B M] [Module.Finite B M] [Module.Flat A M] :
    Module.FinitePresentation B M := by
  classical
  -- Use a finite type subalgebra directly, avoiding the polynomial quotient.
  let C := EssFiniteType.subalgebra A B
  let W := EssFiniteType.submonoid A B
  let : Module C M := Module.compHom M (algebraMap C B)
  have : IsScalarTower C B M := IsScalarTower.of_compHom C B M
  have : IsScalarTower A C M := IsScalarTower.of_algebraMap_smul fun a m ↦ by
    change (algebraMap C B (algebraMap A C a)) • m = a • m
    rw [← IsScalarTower.algebraMap_apply A C B, algebraMap_smul B]
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := B) (M := M)
  let N : Submodule C M := Submodule.span C (s : Set M)
  have : Module.Finite C N := Module.Finite.of_fg ⟨s, rfl⟩
  have : Module.Flat A N :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr
      (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)
  have : Module.FinitePresentation C N :=
    valuation_finite_type_module_presentation A C N
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  -- Localizing the span of the chosen generators gives the whole B-module.
  let f : M →ₗ[C] M := LinearMap.id
  have : IsLocalizedModule W f := isLocalizedModule_id W M B
  let L := N.localized' B W f
  have hL : L = ⊤ := by
    change (Submodule.span C (s : Set M)).localized' B W f = ⊤
    rw [Submodule.localized'_span]
    simpa [f] using hs
  have : Module.FinitePresentation B L :=
    FinitePresentation.of_isBaseChange (N.toLocalized' B W f)
      (IsLocalizedModule.isBaseChange W B _)
  have : Module.FinitePresentation B (⊤ : Submodule B M) := hL ▸ ‹_›
  exact Module.FinitePresentation.of_equiv Submodule.topEquiv

end Algebra

end
