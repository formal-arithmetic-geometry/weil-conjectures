/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLineTensorOrdinaryData
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLineOrdinaryEvaluation

/-! # Completed scalar tensor sections and the base action

Source: blueprint sk-def-sp-tate-twist-locally-free, Proof (3).
(blueprint: lem-pur-completed-line-scalar-base-smul)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct MonoidalCategory
universe t u
namespace WeilConjectures
namespace CompletedLineTensor
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted completedCoefficientMap
  completedOrdinaryScalarExtension completedScalarTensorSection
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] F)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsSiteSmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

private local instance (W : AlgebraicGeometry.Scheme.{t}) :
    EssentiallySmall.{max u (t + 1)} W.ProEt :=
  essentiallySmallSelf.{u, t, t + 1} _

private local instance (W : AlgebraicGeometry.Scheme.{t}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)} :=
  integralCoefficientAbSheafify.{t, u} W

private local instance (W : AlgebraicGeometry.Scheme.{t}) :
    (AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} :=
  integralCoefficientAbLocallyBijective.{t, u} W

open scoped ChangeOfRings in
/-- A sheafified pure tensor of a change of rings, transported along an equality with
`changeOfRings`, is the scalar multiple of the pure tensor with first factor `1`.
Source: Stacks 03EK.
Proof: in the sectionwise extension of scalars `s ⊗ x = (s * 1) ⊗ x = s • (1 ⊗ x)`, and the
sheafification unit is linear over the target sections. -/
private theorem changeOfRings_toSheafify_tmul_eq_smul (W : AlgebraicGeometry.Scheme.{t})
    {R S : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}}
    (φ : R ⟶ S)
    (M : SheafOfModules.{max u (t + 1)}
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology W)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R))
    (A : SheafOfModules.{max u (t + 1)}
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology W)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj S))
    (hA : A = SheafOfModules.changeOfRings.{t, t + 1, max u (t + 1)} φ M)
    (U : W.ProEtᵒᵖ) (a : S.obj.obj U) (x : M.val.obj U) :
    (eqToHom hA.symm).val.app U
        ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} φ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x)) =
      a • ((eqToHom hA.symm).val.app U
        ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} φ M).presheaf).app U
            ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x))) := by
  subst A
  let k := ((PresheafOfModules.sheafificationAdjunction.{max u (t + 1)}
    (𝟙 ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj S).obj)).unit.app
    (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} φ M)).app U ≫
      (ModuleCat.restrictScalarsId (S.obj.obj U)).hom.app _
  change k (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x) =
    a • k ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x)
  have ht : a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x =
      a • ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x) := by
    change a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x =
      (a * 1) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x
    rw [mul_one]
  rw [ht]
  exact k.hom.map_smul a _

/-- Completed scalar tensor sections are multiples of those with first factor `1`.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-scalar-base-smul). -/
theorem completedScalarTensorSection_eq_smul (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U) (x : M.val.obj U) :
    completedScalarTensorSection l E F ι X M U s x =
      smul l F X ((completedOrdinaryScalarExtension l E F ι X).obj M) U s
        (completedScalarTensorSection l E F ι X M U 1 x) := by
  unfold smul completedScalarTensorSection completedOrdinaryScalarExtension
  exact changeOfRings_toSheafify_tmul_eq_smul X (completedCoefficientMap l E F ι X) M _
    ((completedScalarChangeData l E F ι X).choose_spec.choose M) U s x

/-- Scalar tensor sections respect the coefficient-module action: for the completed
coefficient map `φ`, `s ⊗ (r • x) = φ(r) • (s ⊗ x)` in the ordinary extension.
Source: Stacks 03EK; blueprint
literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an/sk-def-sp-tate-twist-locally-free.md,
Proof (3), scalar compatibility
(blueprint: lem-pur-completed-line-scalar-base-smul).
Proof: `completedScalarTensorSection` is the sheafification image of the presheaf pure
tensor `s ⊗ₜ x` over the ring map `φ_U`, transported along the canonical equality of
the ordinary extension with `changeOfRings`. In the extension of scalars the tensor is
balanced, so `s ⊗ₜ (r • x) = (s * φ_U r) ⊗ₜ x = φ_U r • (s ⊗ₜ x)`. The sheafification
unit and the `eqToHom` transport are module maps over the target coefficient sections,
hence they carry this identity to the stated one. -/
theorem completed_scalar_base_smul (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
    (r : (completedIntegralCommRingSheafUnrestricted l E X).obj.obj U)
    (x : M.val.obj U) :
    completedScalarTensorSection l E F ι X M U s (smul l E X M U r x) =
      smul l F X ((completedOrdinaryScalarExtension l E F ι X).obj M) U
        ((completedCoefficientMap l E F ι X).hom.app U r)
        (completedScalarTensorSection l E F ι X M U s x) := by
  have h1 := scalarTensorSection_smul l E X F ι M U r x
  rw [completedScalarTensorSection_eq_smul l E X F ι M U s (smul l E X M U r x),
    completedScalarTensorSection_eq_smul l E X F ι M U s x, ← h1]
  unfold smul
  exact (smul_smul _ _ _).trans ((congrArg (· • completedScalarTensorSection l E F ι X M U 1 x)
    (mul_comm (G := ↑((completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)) s
      ((completedCoefficientMap l E F ι X).hom.app U r))).trans (smul_smul _ _ _).symm)

end CompletedLineTensor
end WeilConjectures
