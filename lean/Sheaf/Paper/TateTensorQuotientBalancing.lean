/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CondensedTateIntegralTowerData
import Sheaf.Paper.TateTensorGeneratorIsIso

/-! Ordinary projection-normalized quotients of the integral Tate tensor.

Source: smooth-purity transport, normalized Tate tower, Step 1.
(blueprint: lem-pur-tate-tensor-quotient-balancing)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped ChangeOfRings
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

private theorem pbcTensorSection_mul (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : pbcModules T R) (U : T.ProEtᵒᵖ) (r z : S.obj.obj U) (x : M.val.obj U) :
    pbcTensorSection φ M U (r * z) x = r • pbcTensorSection φ M U z x := by
  change completedAdicChangeTensor T φ M U (r * z) x =
    r • completedAdicChangeTensor T φ M U z x
  let η := ((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (R := (sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
    (𝟙 _)).unit.app (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M)).app U
  let e := eqToHom ((completedAdicChangeData T φ).choose_spec.choose M).symm
  change e.val.app U (η ((r * z) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) =
    r • e.val.app U (η (z ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
  clear_value e η
  have ht := ModuleCat.ExtendScalars.smul_tmul (φ.hom.app U).hom r z x
  have hη := η.hom.map_smul r (z ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)
  have he := (e.val.app U).hom.map_smul r
    (η (z ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
  exact (congrArg (fun w ↦ e.val.app U (η w)) ht.symm).trans
    ((congrArg (fun w ↦ e.val.app U w) hη).trans he)

/-- At a single finite level, ordinary scalar extension of the actual ordered integral
root tensor is the realized finite root tensor, with its prescribed generator formula.
This statement concerns sheaves, not derived objects or towers.

Source: current blueprint, sec-smooth-purity/sk-thm-purity-transport, Step 2;
lem-pur-normalized-tate-tensor-reductions, proof Step 1.
(blueprint: lem-pur-tate-tensor-quotient-balancing)

Proof: use the common covering with compatible primitive roots from Tate local
freeness. The limit of the free rank-one coefficient modules is free on the compatible
root family: the inverse sends a compatible root section to its compatible scalar
coordinates. The completed coefficient comparison is fixed by its projections, so
quotienting this line sends its chosen generator to the finite root generator.
At degree zero, use multiplication of the coefficient unit. Induct on d, applying
ordinary tensor/scalar balancing to the previous tensor and the last root line.
In each local coordinate the map and its inverse are multiplication and insertion
of unit factors; tensor balancing proves that both composites are identities.
The quotient scalar t and the constant scalar a multiply to t times scalars(a),
which is precisely ProjectionBalanced. The formulas commute with restriction and
with changes of the primitive root basis, so the local maps glue. Sheafification
extends the formula from the displayed generators to arbitrary local sections.
No nonemptiness is needed; the empty tensor and the empty scheme obey the same
unit and sheafification universal properties. -/
theorem tateTensorQuotient_balancing
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (n d : ℕ) :
    ∃ b : (realization T ell n).obj (finiteSheaf T ell n d) ≅ quotientLine T ell n d,
      ProjectionBalanced T ell n d b := by
  obtain ⟨f, hf⟩ := tateTensorQuotient_generator_map T ell hT n d
  let := tateTensorQuotient_generator_isIso T ell hT n d f hf
  let b := asIso f
  refine ⟨b, ?_⟩
  intro U W v a t z x hx
  have hgen := hf U W v a z x hx
  rw [map_smul]
  simp only [one_smul] at hgen
  change t • f.val.app W _ = _
  rw [hgen, pbcTensorSection_mul]

end AlgebraicGeometry.Scheme.PurityIntegralTower
