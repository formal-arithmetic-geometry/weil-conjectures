/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J9
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.Algebra.Homology.SitePerfectModelRestriction
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-! # Local lifting from finite projective module sheaves

Source: Stacks Project, Cohomology on Sites, Tag 08FN.
(blueprint: lem-sf-site-finite-projective-lift).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 512
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

private theorem finite_intersection_covering
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {U : C} {I : Type*} (s : Finset I) (S : I → Sieve U)
    (hS : ∀ i ∈ s, S i ∈ J U) : s.inf S ∈ J U := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.inf_insert]
    exact J.intersection_covering (hS i (by simp))
      (ih (fun j hj ↦ hS j (by simp [hj])))

/-- Local lifting on a fixed slice, expressed as a cover of its base object.
Source: Stacks Project, Tag 08FN
Proof: apply local surjectivity at the terminal object of the slice to each generator,
intersect the image sieves, and assemble their lifts by the preserved biproduct.
(blueprint: lem-sf-site-finite-projective-lift). -/
theorem exists_local_lift_overMap_from_finiteFree
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max u v}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (R : Sheaf J RingCat.{max u v}) (U : C)
    (M N : SheafOfModules.{max u v} (R.over U))
    (p : M ⟶ N) [Epi p] (n : ℕ)
    (g : (⨁ fun _ : Fin n ↦ unit (R.over U)) ⟶ N) :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (f : V ⟶ U), S f →
      ∃ h : (overMap.{max u v} R f).obj
          (⨁ fun _ : Fin n ↦ unit (R.over U)) ⟶ (overMap R f).obj M,
        h ≫ (overMap R f).map p = (overMap R f).map g := by
  classical
  let q := (toSheaf.{max u v} (R.over U)).map p
  have : PreservesFiniteColimits (toSheaf.{max u v} (R.over U)) :=
    (moduleSheaves_colimits_forgetful (R.over U)).2.2.1
  have : Epi q := (toSheaf.{max u v} (R.over U)).map_epi p
  have : Sheaf.IsLocallySurjective q := (Sheaf.isLocallySurjective_iff_epi' _ q).2 inferInstance
  let Z : Over U := Over.mk (𝟙 U)
  let x (i : Fin n) := (N.unitHomEquiv
    (biproduct.ι (fun _ : Fin n ↦ unit (R.over U)) i ≫ g)).val (op Z)
  let T (i : Fin n) := Presheaf.imageSieve q.hom (x i)
  let S := Finset.univ.inf T
  have hS : S ∈ (J.over U) Z :=
    finite_intersection_covering (J.over U) _ T (fun i _ ↦
      Presheaf.imageSieve_mem (J.over U) q.hom (x i))
  refine ⟨Sieve.overEquiv Z S, hS, ?_⟩
  intro V f hf
  have hfi (i : Fin n) : T i (Over.homMk f : Over.mk (f ≫ 𝟙 U) ⟶ Z) := by
    exact (Finset.inf_le (s := Finset.univ) (f := T)
      (by simp : i ∈ Finset.univ)) _ ((Sieve.overEquiv_iff _ _).1 hf)
  have hlift (i : Fin n) :
      ∃ t : M.val.obj (op (Over.mk (f ≫ 𝟙 U))),
        p.val.app _ t = N.val.map (Over.homMk f).op (x i) := hfi i
  choose t ht using hlift
  let F := overMap.{max u v} R f
  have : PreservesFiniteLimits F := (overMap_exact_ofUniverses R f).1
  have : PreservesFiniteColimits F := (overMap_exact_ofUniverses R f).2
  let k (W : (Over V)ᵒᵖ) : Over.mk (W.unop.hom ≫ f) ⟶ Over.mk (f ≫ 𝟙 U) :=
    Over.homMk W.unop.hom (by simp)
  let s (i : Fin n) : (F.obj M).sections :=
    PresheafOfModules.sectionsMk (fun W ↦ M.val.map (k W).op (t i)) (by
      intro W Z a
      change M.val.map ((Over.map f).map a.unop).op
        (M.val.map (k W).op (t i)) = M.val.map (k Z).op (t i)
      have he₀ : ((Over.map f).map a.unop) ≫ k W = k Z := by
        apply Over.OverMorphism.ext
        exact Over.w a.unop
      have he : (k W).op ≫ ((Over.map f).map a.unop).op = (k Z).op := by
        exact congrArg Quiver.Hom.op he₀
      exact (M.val.map_comp_apply (k W).op ((Over.map f).map a.unop).op (t i)).symm.trans
        (M.val.congr_map_apply he (t i)))
  let hc := isColimitOfPreserves F
    (biproduct.isColimit (fun _ : Fin n ↦ unit (R.over U)))
  let c : Cocone (Discrete.functor (fun _ : Fin n ↦ unit (R.over U)) ⋙ F) :=
    { pt := F.obj M
      ι := Discrete.natTrans (fun i ↦ (F.obj M).unitHomEquiv.symm (s i.as)) }
  refine ⟨hc.desc c, ?_⟩
  apply hc.hom_ext
  intro j
  rw [← Category.assoc, hc.fac c j]
  let i : Fin n := j.as
  change (F.obj M).unitHomEquiv.symm (s i) ≫ F.map p =
    F.map (biproduct.ι (fun _ : Fin n ↦ unit (R.over U)) i) ≫ F.map g
  rw [← F.map_comp]
  apply (F.obj N).unitHomEquiv.injective
  rw [unitHomEquiv_symm_comp, Equiv.apply_symm_apply]
  apply PresheafOfModules.sections_ext
  intro W
  change (p.val.app (op (Over.mk (W.unop.hom ≫ f))))
    (M.val.map (k W).op (t i)) = _
  rw [PresheafOfModules.naturality_apply]
  have hti : p.val.app (op (Over.mk (f ≫ 𝟙 U))) (t i) =
      N.val.map (Over.homMk f : Over.mk (f ≫ 𝟙 U) ⟶ Z).op (x i) := ht i
  rw [hti, ← PresheafOfModules.map_comp_apply]
  exact (N.val.sections_property
    (N.unitHomEquiv (biproduct.ι (fun _ : Fin n ↦ unit (R.over U)) i ≫ g))
    (Over.homMk (W.unop.hom ≫ f) : Over.mk (W.unop.hom ≫ f) ⟶ Z).op)

/-- Local splitting on a fixed slice for a finite-free retract target.
Source: Stacks Project, Tag 08FN
Proof: convert the finite product to its biproduct, lift the retraction, then compose
with its inclusion and cancel the displayed splitting.
(blueprint: lem-sf-site-finite-projective-section). -/
theorem exists_local_section_overMap_of_finiteFree_retract
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max u v}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (R : Sheaf J RingCat.{max u v}) (U : C)
    {M N : SheafOfModules.{max u v} (R.over U)} (p : M ⟶ N) [Epi p]
    (n : ℕ) (i : N ⟶ ∏ᶜ fun _ : Fin n ↦ unit (R.over U))
    (q : (∏ᶜ fun _ : Fin n ↦ unit (R.over U)) ⟶ N) (hi : i ≫ q = 𝟙 N) :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (f : V ⟶ U), S f →
      ∃ s : (overMap.{max u v} R f).obj N ⟶ (overMap R f).obj M,
        s ≫ (overMap R f).map p = 𝟙 _ := by
  let e := biproduct.isoProduct (fun _ : Fin n ↦ unit (R.over U))
  obtain ⟨S, hS, h⟩ := exists_local_lift_overMap_from_finiteFree R U M N p n (e.hom ≫ q)
  refine ⟨S, hS, ?_⟩
  intro V f hf
  obtain ⟨t, ht⟩ := h V f hf
  let F := overMap.{max u v} R f
  refine ⟨F.map i ≫ F.map e.inv ≫ t, ?_⟩
  rw [Category.assoc, Category.assoc, ht, ← F.map_comp, ← F.map_comp]
  have he : i ≫ e.inv ≫ e.hom ≫ q = 𝟙 N := by
    simp only [Iso.inv_hom_id_assoc, hi]
  rw [he, F.map_id]

end SheafOfModules
