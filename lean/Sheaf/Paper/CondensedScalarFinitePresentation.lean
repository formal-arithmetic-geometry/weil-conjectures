/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.Paper.FlatCondensedScalarRealization

/-! # Finitely presented scalar modules in the two module conventions

Source: Hemo--Richarz--Scholbach, Theorem 6.2(2), equation (6.2), and Section 3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Ordinary scalar realization and the internal scalar-extension construction have
exactly the same finitely presented essential image. This is a change of module
convention, with no flatness or regularity hypothesis on the condensed ring.

Source: HRS Section 3, (3.1), and Theorem 6.2(2), equation (6.2)
(blueprint: lem-zl-condensed-scalar-finite-presentation).

Proof: evaluation of Λ at the terminal profinite set reconstructs the same scalar
ring as the ring object `scalarRingObj Λ.X`. The equivalence between internal modules
in abelian groups and ordinary modules sends the regular module to the regular
module, hence sends every finite free module to the corresponding finite free module.
It is exact and fully faithful, so it identifies cokernels of maps between these
modules. Thus internal finite presentation is exactly ordinary finite presentation.
Constant module realization in both conventions is the sheafification of the same
constant module presheaf. The coefficient counit in both constructions sends a
constant scalar to that scalar times the unit section of Λ. The tensor universal
property therefore gives a natural isomorphism between their ordinary scalar
extensions; its inverse sends each pure tensor to the identical pure tensor.
Apply the section-module equivalence and inverse image to X. Transport a finite
presentation and its cokernel isomorphism in either direction along these equivalences.
This proves both essential-image inclusions, including zero presentations and zero
rings. No choice of uniform ranks or module on different cover members is made. -/
theorem ordinaryScalarRealization_finitePresentation
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)) :
    (∃ N : ModuleCat.{u + 1} (scalarRing Λ), Module.FinitePresentation (scalarRing Λ) N ∧
      Nonempty (M ≅ (ordinaryScalarRealization Λ X).obj N)) ↔
    (∃ P : Mod Ab.{u + 1} (scalarRingObj Λ.X),
      Mod.IsFinitelyPresented (scalarRingObj Λ.X) P ∧
      Nonempty (M ≅ (finiteConstantScalarExtension Λ.X X).obj P)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
