/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.CokernelEndPowTower
public import WeilConjectures.CategoryTheory.ModuleObjects.Linear
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LisseLatticeValues

/-!
# Constant scalars and the reductions `M/ϖⁿM` of `𝒪_{E,X}`-modules

Let `ℓ` be a prime and `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`. For
a scheme `W`, the elements of `𝒪_E` (resp. `E`) are global sections of `𝒪_{E,W}` (resp. `E_W`),
the constant functions (`AlgebraicGeometry.ProEtale.padicIntegersConstSection`,
`AlgebraicGeometry.ProEtale.padicSubfieldConstSection`). They act on module objects
(`AlgebraicGeometry.ProEtale.padicIntegersSmul`), and the reductions `M/ϖⁿM` of an
`𝒪_{E,X}`-module `M` modulo the powers of an element `ϖ ∈ 𝒪_E` (a uniformiser) are the cokernels
of the powers of the multiplication by `ϖ`, with their tower and cone of projections
(`CategoryTheory.Limits.cokernelEndPowTower`, `CategoryTheory.Limits.cokernelEndPowTowerCone`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)

/-- The constant global sections `𝒪_E →+* Γ(𝒪_{E,W})`. -/
noncomputable def padicIntegersConstSection (W : Scheme.{u}) :
    integers ℓ E.1 →+* Γ (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) W) :=
  letI := normedFieldOfAlgebra ℓ E.1
  (continuousMapCoefficientSectionRingHom W (integers ℓ E.1)).comp ContinuousMap.C

/-- The constant global sections `E →+* Γ(E_W)`. -/
noncomputable def padicSubfieldConstSection (W : Scheme.{u}) :
    E.1 →+* Γ (condensedRingObj (Profinite.continuousMapRingObj E.1) W) :=
  (continuousMapCoefficientSectionRingHom W E.1).comp ContinuousMap.C

variable {ℓ E}

/-- The multiplication `M ⟶ M` by a constant `c ∈ 𝒪_E` on an `𝒪_{E,X}`-module `M`. -/
noncomputable def padicIntegersSmul {X : Scheme.{u}} (c : integers ℓ E.1)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) : End M :=
  (Mod.smulNatTrans (padicIntegersConstSection ℓ E X c).hom).app M

end AlgebraicGeometry.ProEtale
