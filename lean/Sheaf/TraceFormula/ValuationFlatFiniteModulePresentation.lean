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
import Sheaf.RingTheory.FinitelyPresentedOverSubring
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
set_option warn.sorry false

universe u v w

namespace Algebra

/--
A finite module over a local essentially finite type algebra over a valuation ring is finitely
presented when it is flat over the valuation ring.

Source: Stacks Project, `more-algebra.tex`, Lemma Tag 0GSE
(lemma-valuation-ring-flat-essentially-finite-type), part (2), statement and proof at lines
6005--6044 (blueprint: lem-trf-valuation-flat-finite-module-presentation).

Proof: (1) Express the essentially finite type algebra as a localization of a finite type
polynomial algebra and localize at the inverse image of the maximal ideal, obtaining a
surjection from a local polynomial algebra. (2) Pull back the kernel of a finite presentation
of the module to the polynomial algebra; the resulting finite submodule is torsion-free,
hence flat over the valuation ring, and therefore finitely presented. (3) Localize this
presentation and transfer finite presentation across the finite type algebra map, using
`lem-trf-module-submodule-localization`, `lem-trf-flat-module-torsionfree-domain`,
`lem-trf-valuation-torsionfree-flat`, `lem-trf-valuation-finite-type-module-presentation`,
`lem-trf-localization-preserves-finite-presentation`, `lem-weil-pbc-localization-module-exact`,
and `lem-trf-finitely-presented-over-subring`.
-/
theorem valuation_flat_finite_module_presentation
    (A : Type u) (B : Type v) (M : Type w)
    [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
    [AddCommGroup M] [Module B M] [Module A M]
    [IsScalarTower A B M] [Module.Finite B M] [Module.Flat A M] :
    Module.FinitePresentation B M := by
  sorry

end Algebra

end
