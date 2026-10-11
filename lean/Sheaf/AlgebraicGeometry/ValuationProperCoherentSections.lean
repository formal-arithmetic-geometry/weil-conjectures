/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Algebra.Module.FinitePresentation
public import Sheaf.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-!
# Global sections of an invertible module over a valuation ring

Source: Stacks Project, More on Morphisms, Tag 0EX8, proof of
Lemma `lemma-triviality-generic-fibre-valuation-ring`
(blueprint: lem-sc-valuation-proper-coherent-sections).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Degree-zero cohomology of an invertible module on a proper, flat, finitely presented
scheme over a valuation ring is finitely presented over that ring. Scalars act through
`A ≅ Γ(Spec A, O) → Γ(X, O_X)`.
Source: Stacks Project, More on Morphisms, Tag 0EX8, general-case proof
(blueprint: lem-sc-valuation-proper-coherent-sections).

Proof:
1. By def-sc-invertible-module, `F` is locally free of rank one. It therefore meets the
   finite locally free hypothesis of def-amb-finite-locally-free-module with rank `1`.
2. Apply lem-sc-valuation-proper-coherent-higher-direct-images in degree `0`. Its conclusion
   gives finite presentation of `H^0(X, F)` over `A`, which is precisely the assertion. -/
theorem finitePresentation_moduleCohomology_zero_of_valuationRing
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsInvertible] :
    Module.FinitePresentation A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        ((RingedSpace.moduleCohomology X.toRingedSpace 0).obj F)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
