/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Topology.ContinuousMapCondensedRingMap
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-!
# Continuous sections with finite discrete quotient

Source: blueprint `sk-lem-pe-derived-nakayama-resolution.proof.md`, On the point and Triangles.
(blueprint: lem-pe-profinite-sections-finite-quotient)

The condensed coefficient sheaves use the existing universe-general continuous coefficient
construction. The scalar map is the recorded continuous-map postcomposition, and the restricted
regular module specifies the pointwise module structures. Both conclusions characterize their
arrows by postcomposition on sections.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Profinite

/-- Continuous T-valued sections as internal modules over the continuous A-valued ring:
restrict the regular module along the given continuous scalar homomorphism. The scalar map
is the recorded postcomposition `continuousMapRingSheafMapOfUniverse` of
def-sfb-continuous-map-condensed-ring-map; `continuousCoefficientRingSheaf` is definitionally
that node's `continuousMapRingSheafOfUniverse.{u, u}`.
Source: blueprint derived Nakayama resolution, On the point, pointwise scalar action.
(blueprint: lem-pe-profinite-sections-finite-quotient) -/
noncomputable def continuousSectionsModule
    (A T : Type u) [CommRing A] [CommRing T]
    [TopologicalSpace A] [TopologicalSpace T]
    [IsTopologicalRing A] [IsTopologicalRing T]
    [Algebra A T] [ContinuousSMul A T] :
    Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (continuousCoefficientRingObj A) :=
  (Mod.comap ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (continuousMapRingSheafMapOfUniverse.{u, u} (algebraMap A T) (continuous_algebraMap A T) :
        continuousCoefficientRingSheaf A ⟶ continuousCoefficientRingSheaf T))).obj
    (Mod.regular (continuousCoefficientRingObj T))

private def sectionsLinear
    {A T U : Type u} [CommRing A] [CommRing T] [CommRing U]
    [TopologicalSpace A] [TopologicalSpace T] [TopologicalSpace U]
    [IsTopologicalRing A] [IsTopologicalRing T] [IsTopologicalRing U]
    [Algebra A T] [Algebra A U] [ContinuousSMul A T] [ContinuousSMul A U]
    (f : T →L[A] U) (S : Profinite.{u}) :
    C(S, T) →ₗ[C(S, A)] C(S, U) where
  toFun a := (⟨fun x ↦ f x, f.continuous⟩ : C(T, U)).comp a
  map_add' a b := by ext s; exact map_add f _ _
  map_smul' a b := by ext s; exact f.map_smul (a s) (b s)

private theorem sectionsLinear_apply
    {A T U : Type u} [CommRing A] [CommRing T] [CommRing U]
    [TopologicalSpace A] [TopologicalSpace T] [TopologicalSpace U]
    [IsTopologicalRing A] [IsTopologicalRing T] [IsTopologicalRing U]
    [Algebra A T] [Algebra A U] [ContinuousSMul A T] [ContinuousSMul A U]
    (f : T →L[A] U) (S : Profinite.{u})
    (a : C(S, T)) (s : S) : sectionsLinear f S a s = f (a s) := rfl

open CategoryTheory.MonoidalCategory in
private noncomputable def sectionsMap
    {A T U : Type u} [CommRing A] [CommRing T] [CommRing U]
    [TopologicalSpace A] [TopologicalSpace T] [TopologicalSpace U]
    [IsTopologicalRing A] [IsTopologicalRing T] [IsTopologicalRing U]
    [Algebra A T] [Algebra A U] [ContinuousSMul A T] [ContinuousSMul A U]
    (f : T →L[A] U) :
    continuousSectionsModule A T ⟶ continuousSectionsModule A U := by
  letI : MonObj (continuousCoefficientRingObj T).obj :=
    (continuousCoefficientRingSheaf T).obj.monObjCompForget₂
  letI : MonObj (continuousCoefficientRingObj U).obj :=
    (continuousCoefficientRingSheaf U).obj.monObjCompForget₂
  let k : continuousCoefficientRingObj T ⟶ continuousCoefficientRingObj U :=
    ⟨{ app S := AddCommGrpCat.ofHom
         { toFun a := ULift.up ((sectionsLinear f S.unop) a.down)
           map_zero' := congrArg ULift.up (map_zero (sectionsLinear f S.unop))
           map_add' a b := congrArg ULift.up (map_add (sectionsLinear f S.unop) _ _) }
       naturality _ _ _ := by
         ext a
         apply ULift.ext
         ext s
         rfl }⟩
  refine Mod.homMk k ?_
  let aT : continuousCoefficientRingObj A ⟶ continuousCoefficientRingObj T :=
    (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
      (continuousMapRingSheafMapOfUniverse.{u, u} (algebraMap A T)
        (continuous_algebraMap A T) :
        continuousCoefficientRingSheaf A ⟶ continuousCoefficientRingSheaf T)
  let aU : continuousCoefficientRingObj A ⟶ continuousCoefficientRingObj U :=
    (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
      (continuousMapRingSheafMapOfUniverse.{u, u} (algebraMap A U)
        (continuous_algebraMap A U) :
        continuousCoefficientRingSheaf A ⟶ continuousCoefficientRingSheaf U)
  change (aT ▷ _ ≫ MonObj.mul) ≫ k =
    _ ◁ k ≫ (aU ▷ _ ≫ MonObj.mul)
  apply Sheaf.tensor_hom_ext
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.LaxMonoidal.μ_natural_left_assoc,
    ← Functor.LaxMonoidal.μ_natural_right_assoc,
    ← Functor.LaxMonoidal.μ_natural_left_assoc]
  have hT := Sheaf.μ_comp_map_mul (continuousCoefficientRingObj T)
  have hU := Sheaf.μ_comp_map_mul (continuousCoefficientRingObj U)
  simp only [reassoc_of% hT, hU]
  ext S : 2
  apply AddCommGrpCat.hom_ext_toIntLinearMap
  apply TensorProduct.ext'
  intro a b
  change (k.hom.app S)
      ((MonObj.mul : (continuousCoefficientRingObj T).obj ⊗
        (continuousCoefficientRingObj T).obj ⟶ _).app S
          ((aT.hom.app S) a ⊗ₜ[ℤ] b)) =
    (MonObj.mul : (continuousCoefficientRingObj U).obj ⊗
      (continuousCoefficientRingObj U).obj ⟶ _).app S
        ((aU.hom.app S) a ⊗ₜ[ℤ] (k.hom.app S) b)
  apply ULift.ext
  ext s
  change f (algebraMap A T (a.down s) * b.down s) =
    algebraMap A U (a.down s) * f (b.down s)
  simpa only [Algebra.smul_def] using f.map_smul (a.down s) (b.down s)

private theorem sectionsMap_apply
    {A T U : Type u} [CommRing A] [CommRing T] [CommRing U]
    [TopologicalSpace A] [TopologicalSpace T] [TopologicalSpace U]
    [IsTopologicalRing A] [IsTopologicalRing T] [IsTopologicalRing U]
    [Algebra A T] [Algebra A U] [ContinuousSMul A T] [ContinuousSMul A U]
    (f : T →L[A] U) (S : Profinite.{u})
    (a : ULift.{u + 1} C(S, T)) :
    ((sectionsMap f).hom.hom.app (op S)) a =
      ULift.up (sectionsLinear f S a.down) := by
  rfl

/-- Continuous sections preserve this short exact topological module sequence, both on each
profinite set and as condensed internal modules. The section formulas uniquely specify the
postcomposition arrows, rather than allowing arbitrary arrows witnessing short exactness.

Source: blueprint derived Nakayama resolution, On the point and Triangles.
(blueprint: lem-pe-profinite-sections-finite-quotient)

Proof plan:
1. Pointwise addition and scalar multiplication make C(S,T_i) into C(S,A)-modules;
   composition with the continuous A-linear maps is C(S,A)-linear.
2. Injectivity is checked at each point; range f = ker g gives the zero composite.
3. A section killed by g lands continuously in its subspace kernel. The inverse of the
   prescribed homeomorphism onto this kernel gives its continuous preimage under f.
4. Choose a preimage in T_1 for each value in the finite discrete T_2. Composing this
   continuous map from a discrete space with a section lifts that section.
5. The continuous-function sheaves of sk-def-sfb-condensed-ring carry the pointwise actions,
   compatible with precomposition restrictions. The module objects are those of
   sk-def-sfb-module-objects. The sheaf tensor and sheaf-tensor-closed nodes supply the
   monoidal setting; def-weil-pbc-internal-abelian-sheaf-module-equivalence identifies these
   with sectionwise modules without changing sections or restrictions.
6. By def-weil-sheaf-of-modules-category, kernels are sectionwise and cokernels are
   sheafifications of sectionwise cokernels. Steps 2--4 give a kernel and zero cokernel.
   The equivalence in step 5 transports this short exactness to internal module objects. -/
theorem continuousSections_finiteDiscrete_shortExact
    (A T₀ T₁ T₂ : Type u) [CommRing A] [CommRing T₀] [CommRing T₁] [CommRing T₂]
    [TopologicalSpace A] [TopologicalSpace T₀] [TopologicalSpace T₁] [TopologicalSpace T₂]
    [IsTopologicalRing A] [IsTopologicalRing T₀]
    [IsTopologicalRing T₁] [IsTopologicalRing T₂]
    [Algebra A T₀] [Algebra A T₁] [Algebra A T₂]
    [ContinuousSMul A T₀] [ContinuousSMul A T₁] [ContinuousSMul A T₂]
    (f : T₀ →L[A] T₁) (g : T₁ →L[A] T₂)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : LinearMap.range f.toLinearMap = LinearMap.ker g.toLinearMap)
    [Finite T₂] [DiscreteTopology T₂]
    (hker : ∃ e : T₀ ≃ₜ LinearMap.ker g.toLinearMap,
      ∀ t : T₀, (e t).val = f t) :
    (∀ S : Profinite.{u},
      ∃ (F : C(S, T₀) →ₗ[C(S, A)] C(S, T₁))
        (G : C(S, T₁) →ₗ[C(S, A)] C(S, T₂)),
        (∀ a : C(S, T₀), ∀ s : S, F a s = f (a s)) ∧
        (∀ a : C(S, T₁), ∀ s : S, G a s = g (a s)) ∧
        Function.Injective F ∧ Function.Exact F G ∧ Function.Surjective G) ∧
    (∃ (F : continuousSectionsModule A T₀ ⟶ continuousSectionsModule A T₁)
       (G : continuousSectionsModule A T₁ ⟶ continuousSectionsModule A T₂)
       (h : F ≫ G = 0),
       (∀ (S : Profinite.{u}) (a : ULift.{u + 1} C(S, T₀)) (s : S),
         ((F.hom.hom.app (op S)) a).down s = f (a.down s)) ∧
       (∀ (S : Profinite.{u}) (a : ULift.{u + 1} C(S, T₁)) (s : S),
         ((G.hom.hom.app (op S)) a).down s = g (a.down s)) ∧
       (ShortComplex.mk F G h).ShortExact) := by
  classical
  let F := fun S : Profinite.{u} ↦ sectionsLinear f S
  let G := fun S : Profinite.{u} ↦ sectionsLinear g S
  have hgf (t : T₀) : g (f t) = 0 := by
    have ht : f t ∈ LinearMap.range f.toLinearMap := ⟨t, rfl⟩
    rw [hex] at ht
    exact ht
  obtain ⟨e, he⟩ := hker
  have hinj (S : Profinite.{u}) : Function.Injective (F S) := by
    intro a b hab
    ext s
    apply hf
    have hs := congrArg (fun c : C(S, T₁) ↦ c s) hab
    change f (a s) = f (b s) at hs
    exact hs
  have hexa (S : Profinite.{u}) : Function.Exact (F S) (G S) := by
    intro a
    constructor
    · intro ha
      have hz (s : S) : a s ∈ LinearMap.ker g.toLinearMap := by
        change g (a s) = 0
        have hs := congrArg (fun c : C(S, T₂) ↦ c s) ha
        change g (a s) = 0 at hs
        exact hs
      let b : C(S, LinearMap.ker g.toLinearMap) :=
        ⟨fun s ↦ ⟨a s, hz s⟩, a.continuous.subtype_mk hz⟩
      refine ⟨(⟨e.symm, e.symm.continuous⟩ : C(LinearMap.ker g.toLinearMap, T₀)).comp b, ?_⟩
      ext s
      exact (he _).symm.trans (congrArg Subtype.val (e.apply_symm_apply (b s)))
    · rintro ⟨b, rfl⟩
      ext s
      change g (f (b s)) = 0
      exact hgf (b s)
  have hsurj (S : Profinite.{u}) : Function.Surjective (G S) := by
    let r : C(T₂, T₁) := ⟨Function.surjInv hg, continuous_of_discreteTopology⟩
    intro a
    refine ⟨r.comp a, ?_⟩
    ext s
    change g (Function.surjInv hg (a s)) = a s
    exact Function.surjInv_eq hg (a s)
  refine ⟨fun S ↦ ⟨F S, G S, fun _ _ ↦ rfl, fun _ _ ↦ rfl,
    hinj S, hexa S, hsurj S⟩, ?_⟩
  let FF := sectionsMap f
  let GG := sectionsMap g
  have hcomp : FF ≫ GG = 0 := by
    apply Mod.hom_ext
    ext S a
    apply ULift.ext
    ext s
    change (sectionsLinear g S.unop ((sectionsLinear f S.unop) a.down)) s = 0
    rw [sectionsLinear_apply, sectionsLinear_apply]
    exact hgf (a.down s)
  refine ⟨FF, GG, hcomp, ?_, ?_, ?_⟩
  · intro S a s
    dsimp only [FF]
    rw [sectionsMap_apply]
    rfl
  · intro S a s
    dsimp only [GG]
    rw [sectionsMap_apply]
    rfl
  · let M := ShortComplex.mk FF GG hcomp
    let U := Mod.forget (D := Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (continuousCoefficientRingObj A)
    change M.ShortExact
    apply ShortExact.reflects_shortExact_of_faithful U
    let P := sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
    let N := (M.map U).map P
    have hN (S : Profinite.{u}ᵒᵖ) :
        (N.map ((evaluation _ Ab.{u + 1}).obj S)).ShortExact := by
      have hi : Function.Injective ((N.f.app S)) := by
        intro a b hab
        apply ULift.ext
        exact hinj S.unop (congrArg ULift.down hab)
      have hs : Function.Surjective ((N.g.app S)) := by
        intro a
        obtain ⟨b, hb⟩ := hsurj S.unop a.down
        exact ⟨ULift.up b, congrArg ULift.up hb⟩
      have hx : Function.Exact (N.f.app S) (N.g.app S) := by
        intro a
        constructor
        · intro ha
          obtain ⟨b, hb⟩ := (hexa S.unop a.down).1 (congrArg ULift.down ha)
          exact ⟨ULift.up b, congrArg ULift.up hb⟩
        · rintro ⟨b, rfl⟩
          apply ULift.ext
          exact (hexa S.unop ((F S.unop) b.down)).2 ⟨b.down, rfl⟩
      exact ShortComplex.ShortExact.mk' ((ShortComplex.ab_exact_iff_function_exact _).2 hx)
        ((AddCommGrpCat.mono_iff_injective _).2 hi)
        ((AddCommGrpCat.epi_iff_surjective _).2 hs)
    have hNN : N.ShortExact := by
      have : Mono N.f := by
        rw [NatTrans.mono_iff_mono_app]
        exact fun S ↦ (hN S).mono_f
      have : Epi N.g := by
        rw [NatTrans.epi_iff_epi_app]
        exact fun S ↦ (hN S).epi_g
      refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
      rw [ShortComplex.exact_iff_evaluation]
      exact fun S ↦ (hN S).exact
    exact ShortComplex.shortExact_of_iso
      (ShortComplex.mapNatIso (M.map U)
        (sheafificationNatIso (coherentTopology Profinite.{u}) Ab.{u + 1})).symm
      (hNN.map_of_exact (presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))

end Profinite
