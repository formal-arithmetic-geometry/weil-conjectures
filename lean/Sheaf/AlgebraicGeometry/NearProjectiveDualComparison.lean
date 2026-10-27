/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.AssociatedModule
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Sheaf.AlgebraicGeometry.AssociatedModuleHom
import Mathlib.RingTheory.Noetherian.Basic
import Sheaf.AlgebraicGeometry.AssociatedModulePullback

/-!
# Dual comparison for a finite near-projective module

Source: Stacks Project, local-cohomology.tex, Tag 0GAB (remark-duals), and
more-algebra.tex, Tag 0G96 (lemma-dual-near-projective).
(blueprint: lem-per-near-projective-dual-comparison)

The auxiliary definitions only name the associated-module construction, its canonical
sections, and the structure-sheaf comparison. The theorem characterizes the comparison
uniquely by evaluation on local generators, so its existential arrow is canonical.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.NearProjectiveDualComparison

/-- The associated sheaf on `Spec A`, using the recorded associated-module functor.
Restriction along `Γ(Spec A) ≅ A` retains the underlying elements of the module.
Source: Stacks 01BH (3), 01BI; 0GAB
(blueprint: lem-per-near-projective-dual-comparison). -/
noncomputable def associated (A : CommRingCat.{u}) : ModuleCat.{u} A ⥤ (Spec A).Modules :=
  ModuleCat.restrictScalars (Scheme.ΓSpecIso A).hom.hom ⋙
    associatedModuleFunctor (Spec A).toLocallyRingedSpace.toSheafedSpace

/-- The actual pulled-back canonical section, restricted to an arbitrary open.
Source: Stacks 01BH (3), 0096; 0GAB
(blueprint: lem-per-near-projective-dual-comparison). -/
noncomputable def pulledSection (A : CommRingCat.{u}) {Z : Scheme.{u}} (g : Z ⟶ Spec A)
    (M : ModuleCat.{u} A) (U : Z.Opens) (m : M) :
    Γ((Scheme.Modules.tensorPullback g).obj ((associated A).obj M), U) :=
  ((Scheme.Modules.tensorPullback g).obj ((associated A).obj M)).val.map U.leTop.op
    (((Scheme.Modules.tensorPullbackSectionAdjunction g).unit.app
      ((associated A).obj M)).app ⊤
        (associatedModuleCanonicalSection (Spec A).toLocallyRingedSpace.toSheafedSpace
          ((ModuleCat.restrictScalars (Scheme.ΓSpecIso A).hom.hom).obj M) m))

/-- The image of a base scalar in the functions on an open of `Z`.
Source: Stacks 0GAB, ordinary pullback scalar action
(blueprint: lem-per-near-projective-dual-comparison). -/
noncomputable def scalar (A : CommRingCat.{u}) {Z : Scheme.{u}} (g : Z ⟶ Spec A)
    (U : Z.Opens) (a : A) : Γ(Z, U) :=
  Z.presheaf.map U.leTop.op (g.appTop ((Scheme.ΓSpecIso A).inv a))

/-- The inverse affine global-section identification as a linear map over `Γ(Spec A)`.
Source: Stacks 01BH (3), 01I7; 0GAB
(blueprint: lem-per-near-projective-dual-comparison). -/
noncomputable def structureLinear (A : CommRingCat.{u}) :
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso A).hom.hom).obj (ModuleCat.of A A) ⟶
      (SheafOfModules.unit (Spec A).ringCatSheaf).val.obj (op (⊤ : (Spec A).Opens)) :=
  ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars (Scheme.ΓSpecIso A).hom.hom).obj (ModuleCat.of A A))
    (Y := (SheafOfModules.unit (Spec A).ringCatSheaf).val.obj (op ⊤))
    { toFun := (Scheme.ΓSpecIso A).inv
      map_add' := (Scheme.ΓSpecIso A).inv.hom.map_add
      map_smul' := fun r a ↦ by
        change (Scheme.ΓSpecIso A).inv ((Scheme.ΓSpecIso A).hom r * (@id A a)) =
          r * (Scheme.ΓSpecIso A).inv (@id A a)
        rw [map_mul]
        simp }

/-- The associated sheaf of `A` maps to the structure sheaf by the inverse of the
associated-module Hom bijection, applied to the affine global-section identification.
This uses a genuine bijection, rather than choosing an unspecified comparison.
Source: Stacks 01BH (4); 0GAB
(blueprint: lem-per-near-projective-dual-comparison). -/
noncomputable def structureMap (A : CommRingCat.{u}) :
    (associated A).obj (ModuleCat.of A A) ⟶ SheafOfModules.unit (Spec A).ringCatSheaf :=
  (Equiv.ofBijective _ (associatedModuleHom_bijective
    (Spec A).toLocallyRingedSpace.toSheafedSpace
    ((ModuleCat.restrictScalars (Scheme.ΓSpecIso A).hom.hom).obj (ModuleCat.of A A))
    (SheafOfModules.unit (Spec A).ringCatSheaf))).symm (structureLinear A)

/-- Pull back the associated-to-structure map and apply the canonical tensor-unit map.
Source: Stacks 0096, 01BH; 0GAB
(blueprint: lem-per-near-projective-dual-comparison). -/
noncomputable def pullbackStructureMap (A : CommRingCat.{u}) {Z : Scheme.{u}}
    (g : Z ⟶ Spec A) :
    (Scheme.Modules.tensorPullback g).obj ((associated A).obj (ModuleCat.of A A)) ⟶
      SheafOfModules.unit Z.ringCatSheaf :=
  (Scheme.Modules.tensorPullback g).map (structureMap A) ≫
    Scheme.Modules.tensorPullbackObjUnitToUnit g

/-- The pullback of the associated sheaf of `M`.
Source: Stacks 0GAB (blueprint: lem-per-near-projective-dual-comparison). -/
noncomputable abbrev pulled (A : CommRingCat.{u}) {Z : Scheme.{u}} (g : Z ⟶ Spec A)
    (M : ModuleCat.{u} A) : Z.Modules :=
  (Scheme.Modules.tensorPullback g).obj ((associated A).obj M)

/-- The sheaf Hom from the pullback of `M` to the structure sheaf.
Source: Stacks 0GAB (blueprint: lem-per-near-projective-dual-comparison). -/
noncomputable abbrev dualSheaf (A : CommRingCat.{u}) {Z : Scheme.{u}} (g : Z ⟶ Spec A)
    (M : ModuleCat.{u} A) : Z.Modules :=
  SheafOfModules.homObj (R := Z.sheaf) (pulled A g M)
    (SheafOfModules.unit Z.ringCatSheaf)

/-- The scalar extension of the linear evaluation `λ ↦ λ(m)`.
Source: Stacks 0GAB, final evaluation compatibility
(blueprint: lem-per-near-projective-dual-comparison). -/
noncomputable def pulledEvaluation (A : CommRingCat.{u}) {Z : Scheme.{u}}
    (g : Z ⟶ Spec A) (M : ModuleCat.{u} A) (m : M) :
    pulled A g (ModuleCat.of A (Module.Dual A M)) ⟶
      SheafOfModules.unit Z.ringCatSheaf :=
  (Scheme.Modules.tensorPullback g).map
    ((associated A).map (ModuleCat.ofHom (LinearMap.applyₗ (R := A) (M₂ := A) m))) ≫
      pullbackStructureMap A g

/-- Dual finiteness, scalar factorization, and the canonical sheaf dual comparison.
Source: Stacks local-cohomology.tex, Tag 0GAB (remark-duals), and more-algebra.tex,
Tag 0G96 (lemma-dual-near-projective)
(blueprint: lem-per-near-projective-dual-comparison).

Proof:
1. Choose finitely many generators of M. Their evaluation embeds its dual in A^s.
   Noetherian submodule finiteness (lem-weil-pbc-noetherian-submodule-finite) gives
   finiteness of the dual.
2. Write the assumed factorization of a as sum_i λ_i(-)m_i. Dualizing gives
   aλ = sum_i λ(m_i)λ_i, the required finite-free factorization on the dual.
3. Use the associated-module Hom bijection and its pullback description
   (lem-weil-pbc-associated-module-hom and lem-weil-pbc-associated-module-pullback)
   to define the unique evaluation comparison on the canonical local generators.
   Its value on bλ and b'm is bb'g-sharp(λ(m)). Restrictions preserve this formula.
4. For each a define β(φ) = sum_i φ(m_i)λ_i on every open. It commutes with
   restriction. Evaluation on each generating m shows αβ = a on the sheaf dual.
5. The dual factorization from step 2 gives βα = a on the pulled-back dual.
   Thus a kills the kernel and the sectionwise cokernel, and hence the sheafified
   cokernel (def-weil-sheaf-of-modules-category). All local combinations of a in J
   also kill these sheaves, giving annihilation by the extended ideal.
6. On each canonical λ, evaluation at the pulled-back m agrees with pullback of
   λ ↦ λ(m), by naturality and normalization of the associated-module pullback.
   The generators determine maps, proving the last equation. No tensor-exactness
   or flatness has been used. -/
theorem nearProjective_dual_comparison (A : CommRingCat.{u}) [IsNoetherianRing A]
    (J : Ideal A) (M : ModuleCat.{u} A) [Module.Finite A M]
    (hM : ∀ a ∈ J, ∃ (r : ℕ) (f : M →ₗ[A] (Fin r → A))
      (h : (Fin r → A) →ₗ[A] M), h.comp f = a • LinearMap.id) :
    Module.Finite A (Module.Dual A M) ∧
      (∀ a ∈ J, ∃ (r : ℕ) (f : Module.Dual A M →ₗ[A] (Fin r → A))
        (h : (Fin r → A) →ₗ[A] Module.Dual A M), h.comp f = a • LinearMap.id) ∧
      ∀ (Z : Scheme.{u}) (g : Z ⟶ Spec A),
        ∃! α : pulled A g (ModuleCat.of A (Module.Dual A M)) ⟶ dualSheaf A g M,
          (∀ (U : Z.Opens) (b b' : Γ(Z, U)) (l : Module.Dual A M) (m : M),
            PresheafOfModules.homObjEvalId (R := Z.sheaf.obj)
              (pulled A g M).val (SheafOfModules.unit Z.ringCatSheaf).val U
              (α.app U (b • pulledSection A g (ModuleCat.of A (Module.Dual A M)) U l))
              (b' • pulledSection A g M U m) = b * b' * scalar A g U (l m)) ∧
          (∀ (U : Z.Opens) (a : A), a ∈ J →
            ∀ x : Γ(kernel α, U), scalar A g U a • x = 0) ∧
          (∀ (U : Z.Opens) (a : A), a ∈ J →
            ∀ x : Γ(cokernel α, U), scalar A g U a • x = 0) ∧
          (∀ (m : M) (U : Z.Opens)
              (x : Γ(pulled A g (ModuleCat.of A (Module.Dual A M)), U)),
            PresheafOfModules.homObjEvalId (R := Z.sheaf.obj)
              (pulled A g M).val (SheafOfModules.unit Z.ringCatSheaf).val U
              (α.app U x) (pulledSection A g M U m) = (pulledEvaluation A g M m).app U x) := by
  sorry

end AlgebraicGeometry.NearProjectiveDualComparison
