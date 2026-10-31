/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RegularQuotientConeBasic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Division by a regular scalar on sections of an injective module sheaf

Source: Stacks Tags 03D7 and 079P; the free lifted representable test for injectivity and the
elementary divisibility property of injectives for a regular scalar.
(blueprint: lem-sf-regular-scalar-injective-divisibility). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules.RegularQuotientCone

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasSheafify J AddCommGrpCat.{max u v}]
  (R : Sheaf J CommRingCat.{max u v})
  (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)

private def presheafScalar (M : PresheafOfModules.{max u v}
    (derivedChangeRingIndependentCoefficients J R).obj) : M ⟶ M where
  app U := ModuleCat.ofHom (LinearMap.lsmul (R.obj.obj U) (M.obj U) (t.val U))
  naturality {U V} f := by
    ext x
    change t.val V • M.map f x = M.map f (t.val U • x)
    rw [M.map_smul]
    congr 1
    exact (t.property f).symm

/-- A sectionwise regular compatible scalar divides every section of an injective
module sheaf. The free lifted representable detects each section; regularity makes
scalar multiplication on it monic, and injectivity extends across that monomorphism.
Source: Stacks Tags 03D7 and 079P; the free lifted representable test for injectivity and the
elementary divisibility property of injectives for a regular scalar.
(blueprint: lem-sf-regular-scalar-injective-divisibility). -/
theorem regularScalar_injective_surjective
    (ht : ∀ U : Cᵒᵖ, Function.Injective
      (fun x : R.obj.obj U ↦ (@id (R.obj.obj U) (t.val U)) * x))
    (I : Modules R) [Injective I] (U : Cᵒᵖ) :
    Function.Surjective (fun x : I.val.obj U ↦ (@id (R.obj.obj U) (t.val U)) • x) := by
  let R₀ := derivedChangeRingIndependentCoefficients J R
  let adj := PresheafOfModules.sheafificationAdjunction.{max u v} (𝟙 R₀.obj)
  let M := (SheafOfModules.forget R₀ ⋙
    PresheafOfModules.restrictScalars (𝟙 R₀.obj)).obj I
  have : Injective M := Injective.injective_of_adjoint adj I
  let P := (PresheafOfModules.free R₀.obj).obj (uliftYoneda.{u}.obj U.unop)
  let μ := presheafScalar R t P
  have : Mono μ := PresheafOfModules.mono_of_injective (fun {V} ↦ by
    intro x y h
    apply Finsupp.ext
    intro z
    apply ht V
    exact congrArg
      (fun p : (uliftYoneda.{u}.obj U.unop).obj V →₀ R.obj.obj V ↦ p z) h)
  let e : (P ⟶ M) ≃ M.obj U :=
    PresheafOfModules.freeHomEquiv.trans uliftYonedaEquiv
  intro s
  let f := e.symm s
  let g := Injective.factorThru f μ
  refine ⟨e g, ?_⟩
  have h := congrArg e (Injective.comp_factorThru f μ)
  change e (μ ≫ g) = e (e.symm s) at h
  rw [e.apply_symm_apply] at h
  rw [← h]
  change (@id (R.obj.obj U) (t.val U)) •
      g.app U (ModuleCat.freeMk (ULift.up (𝟙 U.unop))) =
    g.app U ((μ.app U) (ModuleCat.freeMk (ULift.up (𝟙 U.unop))))
  exact ((g.app U).hom.map_smul (t.val U) _).symm

end SheafOfModules.RegularQuotientCone
