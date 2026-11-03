/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalHomDualTorAmplitude
public import WeilConjectures.Algebra.Homology.Monoidal.Dual
import WeilConjectures.TraceFormula.CategoricalTraceBiproduct

/-! # Duals of finite projective condensed modules

The point-module step of the locally constant perfect dual argument: a chosen right dual of
a finite-free retract is again a finite-free retract.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- A chosen right dual of a finite projective condensed module is again finite projective.
Source: internal-Hom stability proof, paragraph 3.
(blueprint: lem-sfb-dual-term-finite-projective).

Proof: express the module as a retract `i ≫ p = 𝟙` of the finite free module `Λ^n`.
The finite free module `Λ^n`, a biproduct of copies of the unit, is paired with itself
by the biproduct of the unit pairings. Dualize the retract maps by right-adjoint mates:
`pᘁ : Mᘁ ⟶ Λ^n` and `iᘁ : Λ^n ⟶ Mᘁ`. Mates reverse composition and preserve identities,
so `pᘁ ≫ iᘁ = (i ≫ p)ᘁ = 𝟙`. The zero-rank case is included by the same calculation. -/
theorem dualTerm_finiteProjective
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (M : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (hM : FiniteProjectiveCondensedModule (Mon.mk Λ) M)
    [HasRightDual M] :
    FiniteProjectiveCondensedModule (Mon.mk Λ) Mᘁ := by
  obtain ⟨n, i, p, hip⟩ := hM
  let B := fun _ : Fin n ↦ 𝟙_ (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
  let _ (j : Fin n) : ExactPairing (B j) (B j) :=
    inferInstanceAs (ExactPairing (𝟙_ _) (𝟙_ _))
  let : HasRightDual (Mod.finiteFree (Mon.mk Λ).X n) :=
    { rightDual := Mod.finiteFree (Mon.mk Λ).X n
      exact := Bicone.exactPairing (V := B) (W := B)
        (biproduct.isBilimit B) (biproduct.isBilimit B) }
  refine ⟨n, pᘁ, iᘁ, ?_⟩
  rw [← comp_rightAdjointMate, hip, rightAdjointMate_id]

end AlgebraicGeometry.ProEtale
