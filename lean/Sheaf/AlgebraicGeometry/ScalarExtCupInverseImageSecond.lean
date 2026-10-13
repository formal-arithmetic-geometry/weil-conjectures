/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
import Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! # ScalarExtCupInverseImageSecond

Source: Stacks Project, Cohomology, Tags 01F7, 01FD, 07MB and 0FKV.
-/

@[expose] public section

universe w
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

attribute [local instance] Sheaf.monoidalCategory HasExt.standard

private lemma exactFunctor_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasExt.{w + 1} C] [HasExt.{w + 1} D] [EnoughInjectives C]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    (τ : F ⟶ G) {M N : C} {n : ℕ} (x : Abelian.Ext.{w + 1} M N n) :
    (x.mapExactFunctor F).comp (Abelian.Ext.mk₀ (τ.app N)) (add_zero n) =
      (Abelian.Ext.mk₀ (τ.app M)).comp (x.mapExactFunctor G) (zero_add n) := by
  induction n generalizing N with
  | zero =>
    obtain ⟨f, rfl⟩ := (Abelian.Ext.mk₀_bijective M N).2 x
    simp only [Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀]
    exact congrArg Abelian.Ext.mk₀ (τ.naturality f)
  | succ n ih =>
    let S := ShortComplex.mk (Injective.ι N) (Limits.cokernel.π (Injective.ι N))
      (Limits.cokernel.condition (Injective.ι N))
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
    obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₁ M hS x
      (Abelian.Ext.eq_zero_of_injective _) rfl
    subst x
    let f : S.map F ⟶ S.map G :=
      { τ₁ := τ.app S.X₁
        τ₂ := τ.app S.X₂
        τ₃ := τ.app S.X₃
        comm₁₂ := (τ.naturality S.f).symm
        comm₂₃ := (τ.naturality S.g).symm }
    have hn := (hS.map_of_exact F).extClass_naturality (hS.map_of_exact G) f
    simp only [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_extClass]
    rw [Abelian.Ext.comp_assoc _ _ _ rfl (add_zero 1) (by omega), hn,
      ← Abelian.Ext.comp_assoc _ _ _ (add_zero n) (zero_add 1) rfl, ih,
      Abelian.Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)]

private lemma mapExactFunctor_composite
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasExt.{w + 1} C] [HasExt.{w + 1} D] [HasExt.{w + 1} E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    {M N : C} {n : ℕ} (x : Abelian.Ext.{w + 1} M N n) :
    x.mapExactFunctor (F ⋙ G) = (x.mapExactFunctor F).mapExactFunctor G := by
  let := Limits.comp_preservesFiniteLimits F G
  let := Limits.comp_preservesFiniteColimits F G
  simpa using Abelian.Ext.exactFunctorCompositionComparison F G (F ⋙ G) (Iso.refl _) x

set_option maxHeartbeats 800000 in
-- Ext transport elaborates the exact tensor and sheaf inverse-image instances repeatedly.
/-- Compatibility of the second tensor transport with exact inverse image.
Source: Stacks Project, Cohomology, Tags 01FD, 07MB and 0FKV.
(blueprint: lem-sc-scalar-ext-cup-inverse-image-second).

Proof: Put T = scalarInverseImage t and u = scalarInverseUnitIso t. For fixed A,
the components δ_{A,M}
form a natural transformation from tensorLeft A followed by T to T followed by tensorLeft (TA),
by δ_natural_right. The morphisms φ tensor id form a second natural transformation from
tensorLeft (TA) to tensorLeft A'. Apply these transformations termwise to complexes. Exactness
of all functors ensures that they descend through quasi-isomorphism localization; the termwise
maps commute with shifts. Naturality on the shifted morphism representing b therefore gives
T(tensorLeft A b), postcomposed by δ_{A,B} and φ tensor id, equal to δ_{A,1_X} followed by φ
tensor id, then tensorLeft A' of Tb, in Ext. Postcompose by A' tensor ψ. Tensor functors
preserve degree-zero maps and Ext composition. Insert u.hom followed by u.inv = id at the
intermediate factor T1_X: after tensorLeft A', this places u.hom in the source comparison and
u.inv before Tb. Associativity of Ext composition gives exactly the displayed formula, with no
use of a or p or the first-factor formula. Every inserted map has degree zero. In q=0 the
calculation is ordinary δ naturality, tensor bifunctoriality, and u.hom_inv_id; for zero sheaves
or empty schemes the same identities hold.
-/
theorem scalarExtCup_inverseImage_second (t : Y ⟶ X)
    (A B : KSheaf X k) (A' B' : KSheaf Y k)
    (φ : (scalarInverseImage t).obj A ⟶ A')
    (ψ : (scalarInverseImage t).obj B ⟶ B') (q : ℕ)
    (b : Abelian.Ext.{w + 1} (𝟙_ (KSheaf X k)) B q) :
    ((b.mapExactFunctor (tensorLeft A)).mapExactFunctor (scalarInverseImage t)).comp
      (Abelian.Ext.mk₀ (((Opens.map t.base).sheafAdjunctionContinuous (ModuleCat.{w} k)
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).leftAdjointOplaxMonoidal.δ
        A B ≫ (φ ⊗ₘ ψ))) (add_zero q) =
    (Abelian.Ext.mk₀ (((Opens.map t.base).sheafAdjunctionContinuous (ModuleCat.{w} k)
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).leftAdjointOplaxMonoidal.δ
      A (𝟙_ (KSheaf X k)) ≫ (φ ⊗ₘ (scalarInverseUnitIso t).hom))).comp
      ((((Abelian.Ext.mk₀ (scalarInverseUnitIso t).inv).comp
        (b.mapExactFunctor (scalarInverseImage t)) (zero_add q)).comp
          (Abelian.Ext.mk₀ ψ) (add_zero q)).mapExactFunctor (tensorLeft A'))
            (zero_add q) := by
  let : MonoidalCategory (KSheaf X k) := inferInstance
  let : MonoidalCategory (KSheaf Y k) := inferInstance
  let : Abelian (KSheaf X k) := inferInstance
  let : Abelian (KSheaf Y k) := inferInstance
  let T := scalarInverseImage (k := k) t
  let : T.OplaxMonoidal := ((Opens.map t.base).sheafAdjunctionContinuous (ModuleCat.{w} k)
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).leftAdjointOplaxMonoidal
  let τ : tensorLeft A ⋙ T ⟶ T ⋙ tensorLeft A' :=
    { app := fun M ↦ Functor.OplaxMonoidal.δ T A M ≫ (φ ⊗ₘ 𝟙 (T.obj M))
      naturality := by
        intro M N f
        change T.map (A ◁ f) ≫ Functor.OplaxMonoidal.δ T A N ≫ (φ ⊗ₘ 𝟙 (T.obj N)) =
          (Functor.OplaxMonoidal.δ T A M ≫ (φ ⊗ₘ 𝟙 (T.obj M))) ≫ A' ◁ T.map f
        rw [← Functor.OplaxMonoidal.δ_natural_right_assoc]
        simp only [Category.assoc, tensorHom_def, whiskerLeft_id, Category.comp_id]
        congr 1
        exact whisker_exchange φ (T.map f) }
  let := Limits.comp_preservesFiniteLimits (tensorLeft A) T
  let := Limits.comp_preservesFiniteColimits (tensorLeft A) T
  let := Limits.comp_preservesFiniteLimits T (tensorLeft A')
  let := Limits.comp_preservesFiniteColimits T (tensorLeft A')
  have hn := exactFunctor_naturality (tensorLeft A ⋙ T) (T ⋙ tensorLeft A') τ b
  simp only [mapExactFunctor_composite] at hn
  dsimp only [τ] at hn
  let u : T.obj (𝟙_ (KSheaf X k)) ≅ 𝟙_ (KSheaf Y k) := scalarInverseUnitIso t
  have hm : (Functor.OplaxMonoidal.δ T A B ≫ (φ ⊗ₘ ψ)) =
      (Functor.OplaxMonoidal.δ T A B ≫ (φ ⊗ₘ 𝟙 (T.obj B))) ≫ (tensorLeft A').map ψ := by
    change _ = _ ≫ A' ◁ ψ
    simp only [tensorHom_def, whiskerLeft_id, Category.comp_id, Category.assoc]
  have hu : (Functor.OplaxMonoidal.δ T A (𝟙_ (KSheaf X k)) ≫
      (φ ⊗ₘ 𝟙 (T.obj (𝟙_ (KSheaf X k))))) =
      (Functor.OplaxMonoidal.δ T A (𝟙_ (KSheaf X k)) ≫ (φ ⊗ₘ u.hom)) ≫
        (tensorLeft A').map u.inv := by
    change _ = _ ≫ A' ◁ u.inv
    rw [Category.assoc, ← id_tensorHom, tensorHom_comp_tensorHom,
      u.hom_inv_id, Category.comp_id]
  change ((b.mapExactFunctor (tensorLeft A)).mapExactFunctor T).comp
    (Abelian.Ext.mk₀ (Functor.OplaxMonoidal.δ T A B ≫ (φ ⊗ₘ ψ))) (add_zero q) = _
  rw [hm, ← Abelian.Ext.mk₀_comp_mk₀,
    ← Abelian.Ext.comp_assoc_of_second_deg_zero, hn]
  simp only [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
  change _ = (Abelian.Ext.mk₀
    (Functor.OplaxMonoidal.δ T A (𝟙_ (KSheaf X k)) ≫ (φ ⊗ₘ u.hom))).comp
    (((Abelian.Ext.mk₀ ((tensorLeft A').map u.inv)).comp
      ((b.mapExactFunctor T).mapExactFunctor (tensorLeft A')) (zero_add q)).comp
        (Abelian.Ext.mk₀ ((tensorLeft A').map ψ)) (add_zero q)) (zero_add q)
  rw [← Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀_assoc, ← hu]

end
end AlgebraicGeometry.Scheme.Modules
