/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal

/-!
# Condensed rings of finite free extensions of topological rings

Let `T → T'` be a continuous homomorphism of commutative topological rings making `T'` a free
`T`-module with a basis `b` whose coordinate functionals are continuous. Then the condensed ring
`T̲' = C(-, T')`, regarded as a module object over `T̲ = C(-, T)`, is finite free:
`C(S, T') ≅ C(S, T)ᵈ` naturally in the profinite set `S`
(`Profinite.comapRegularIsoFiniteFree`).

The linearity of sectionwise defined morphisms of abelian sheaves between rings is checked on
presheaves (`CategoryTheory.Sheaf.whiskerRight_mul_comp_eq_of_app`).
-/

@[expose] public section

universe w u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) [HasWeakSheafify J Ab.{w}]
  [(J.W (A := Ab.{w})).IsMonoidal] [J.HasSheafCompose (forget₂ RingCat.{w} Ab.{w})]

attribute [local instance] Sheaf.monoidalCategory

open Functor.LaxMonoidal Functor.OplaxMonoidal

omit [(J.W (A := Ab.{w})).IsMonoidal] in
/- This is `CategoryTheory.Sheaf.sheafToPresheaf_map_sheafifyRingPresheafIso_inv` of
`WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear`, repeated to avoid importing
that file. -/
private lemma sheafToPresheaf_map_sheafifyRingPresheafIso_inv' (S : Sheaf J RingCat.{w}) :
    (sheafToPresheaf J Ab.{w}).map (sheafifyRingPresheafIso J S).inv =
      (sheafificationAdjunction J Ab.{w}).unit.app (S.obj ⋙ forget₂ RingCat.{w} Ab.{w}) := by
  rw [← cancel_mono ((sheafToPresheaf J Ab.{w}).map (sheafifyRingPresheafIso J S).hom),
    ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id]
  exact ((sheafificationAdjunction J Ab.{w}).right_triangle_components _).symm

/- This is `CategoryTheory.Sheaf.μ_sheafToPresheaf_comp_map_mul_sheafCompose` of
`WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear`, repeated to avoid importing
that file. -/
private lemma μ_sheafToPresheaf_comp_map_mul_sheafCompose' (S : Sheaf J RingCat.{w}) :
    Functor.LaxMonoidal.μ (sheafToPresheaf J Ab.{w})
        ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S)
        ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S) ≫
      (sheafToPresheaf J Ab.{w}).map μ[(sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S] =
    μ[S.obj ⋙ forget₂ RingCat.{w} Ab.{w}] := by
  let adj := sheafificationAdjunction J Ab.{w}
  have h := adj.unit_app_tensor_comp_map_δ (S.obj ⋙ forget₂ RingCat.{w} Ab.{w})
    (S.obj ⋙ forget₂ RingCat.{w} Ab.{w})
  have he : adj.unit.app (S.obj ⋙ forget₂ RingCat.{w} Ab.{w}) ≫
      (sheafToPresheaf J Ab.{w}).map (sheafifyRingPresheafIso J S).hom = 𝟙 _ :=
    adj.right_triangle_components _
  erw [MonObj.ofIso_mul, Functor.obj.μ_def]
  rw [Functor.map_comp, ← μ_natural_assoc,
    sheafToPresheaf_map_sheafifyRingPresheafIso_inv',
    Functor.map_comp, Functor.map_comp, ← reassoc_of% h, Category.assoc,
    ← Functor.map_comp_assoc,
    Functor.Monoidal.δ_μ, Functor.map_id, Category.id_comp]
  erw [← adj.unit.naturality_assoc, he, Category.comp_id]
  rfl

/-- **Linearity of sectionwise linear maps of sheaves of rings.** Let `f₁ : A ⟶ N₁` and
`f₂ : A ⟶ N₂` be morphisms of sheaves of rings and `g : N₁ ⟶ N₂` a morphism of the underlying
abelian sheaves which is `A`-linear on sections: `g (f₁ a * x) = f₂ a * g x`. Then `g` is
compatible with the actions of the ring object `A` on `N₁` and `N₂` through `f₁` and `f₂`. -/
lemma whiskerRight_mul_comp_eq_of_app {A N₁ N₂ : Sheaf J RingCat.{w}} (f₁ : A ⟶ N₁)
    (f₂ : A ⟶ N₂)
    (g : (sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj N₁ ⟶
      (sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj N₂)
    (hg : ∀ (U : Cᵒᵖ) (a : A.obj.obj U) (x : N₁.obj.obj U),
      (g.hom.app U).hom (f₁.hom.app U a * x) =
        @HMul.hMul (N₂.obj.obj U) (N₂.obj.obj U) (N₂.obj.obj U) instHMul (f₂.hom.app U a)
          ((g.hom.app U).hom x)) :
    ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).map f₁ ▷ _ ≫
        μ[(sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj N₁]) ≫ g =
      _ ◁ g ≫ (sheafCompose J (forget₂ RingCat.{w} Ab.{w})).map f₂ ▷ _ ≫
        μ[(sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj N₂] := by
  refine Sheaf.hom_ext_of_μ_comp ?_
  simp only [Functor.map_comp, Category.assoc]
  rw [← μ_natural_left_assoc, reassoc_of% (μ_sheafToPresheaf_comp_map_mul_sheafCompose' J N₁),
    ← μ_natural_right_assoc, ← μ_natural_left_assoc,
    μ_sheafToPresheaf_comp_map_mul_sheafCompose']
  ext U : 2
  refine AddCommGrpCat.hom_ext_toIntLinearMap (TensorProduct.ext' fun a x ↦ ?_)
  exact hg U a x

end CategoryTheory.Sheaf

namespace Profinite

section FiniteFree

variable {T T' : Type} [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [TopologicalSpace T'] [CommRing T'] [IsTopologicalRing T']

/-- Postcomposition with a continuous additive map `ψ : T →+ T'`, as a morphism
`C(-, T) ⟶ C(-, T')` of the abelian sheaves underlying the condensed rings. -/
noncomputable def continuousMapAbMap (ψ : T →+ T') (hψ : Continuous ψ) :
    continuousMapRingObj.{u} T ⟶ continuousMapRingObj T' :=
  ⟨{ app _ := AddCommGrpCat.ofHom
        { toFun x := ULift.up ((⟨ψ, hψ⟩ : C(T, T')).comp x.down)
          map_zero' := congrArg ULift.up (ContinuousMap.ext fun _ ↦ map_zero ψ)
          map_add' _ _ := congrArg ULift.up (ContinuousMap.ext fun _ ↦ map_add ψ _ _) }
     naturality _ _ _ := rfl }⟩

lemma continuousMapAbMap_app_apply (ψ : T →+ T') (hψ : Continuous ψ) (S : Profinite.{u}ᵒᵖ)
    (x : ULift.{u + 1} C(S.unop, T)) :
    ((continuousMapAbMap ψ hψ).hom.app S).hom x =
      ULift.up ((⟨ψ, hψ⟩ : C(T, T')).comp x.down) :=
  rfl

variable [Algebra T T'] (hφ : Continuous (algebraMap T T'))

/-- The morphism `T̲ ⟶ T̲'` of ring objects of condensed abelian groups induced by the continuous
structure map `algebraMap T T'`. -/
noncomputable abbrev continuousMapRingObjAlgebraMap :
    continuousMapRingObj.{u} T ⟶ continuousMapRingObj T' :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (continuousMapRingSheafMap (algebraMap T T') hφ)

/-- The `T̲`-linear map `T̲ ⟶ T̲'`, `x ↦ x • t`, for an element `t : T'`. -/
noncomputable def continuousMapSMulRightHom (t : T') :
    Mod.regular (continuousMapRingObj.{u} T) ⟶
      (Mod.comap (continuousMapRingObjAlgebraMap hφ)).obj
        (Mod.regular (continuousMapRingObj.{u} T')) :=
  Mod.homMk (continuousMapAbMap ((AddMonoidHom.mulRight t).comp (algebraMap T T').toAddMonoidHom)
    ((hφ).mul continuous_const)) (by
    have h := Sheaf.whiskerRight_mul_comp_eq_of_app (coherentTopology Profinite.{u})
      (𝟙 (continuousMapRingSheaf.{u} T)) (continuousMapRingSheafMap (algebraMap T T') hφ)
      (continuousMapAbMap ((AddMonoidHom.mulRight t).comp (algebraMap T T').toAddMonoidHom)
        ((hφ).mul continuous_const)) (fun _ a x ↦ congrArg ULift.up (ContinuousMap.ext fun s ↦
          (congrArg (· * t) (map_mul (algebraMap T T') (a.down s) (x.down s))).trans
            (mul_assoc _ _ _)))
    rw [CategoryTheory.Functor.map_id, id_whiskerRight, Category.id_comp] at h
    exact h)

/-- The `T̲`-linear map `T̲' ⟶ T̲` given by postcomposition with a continuous `T`-linear map
`c : T' →ₗ[T] T`. -/
noncomputable def continuousMapLinearMapHom (c : T' →ₗ[T] T) (hc : Continuous c) :
    (Mod.comap (continuousMapRingObjAlgebraMap hφ)).obj
        (Mod.regular (continuousMapRingObj.{u} T')) ⟶
      Mod.regular (continuousMapRingObj.{u} T) :=
  Mod.homMk (continuousMapAbMap c.toAddMonoidHom hc) (by
    have h := Sheaf.whiskerRight_mul_comp_eq_of_app (coherentTopology Profinite.{u})
      (continuousMapRingSheafMap (algebraMap T T') hφ) (𝟙 (continuousMapRingSheaf.{u} T))
      (continuousMapAbMap c.toAddMonoidHom hc) (fun _ a x ↦ congrArg ULift.up
        (ContinuousMap.ext fun s ↦ (congrArg c (Algebra.smul_def (a.down s) (x.down s)).symm).trans
          (c.map_smul (a.down s) (x.down s))))
    rw [CategoryTheory.Functor.map_id, id_whiskerRight, Category.id_comp] at h
    exact h)

variable {d : ℕ} (b : Module.Basis (Fin d) T T') (hb : ∀ i, Continuous (b.coord i))

lemma continuousMapSMulRightHom_comp_linearMapHom_coord (i j : Fin d) :
    continuousMapSMulRightHom.{u} hφ (b i) ≫ continuousMapLinearMapHom hφ (b.coord j) (hb j) =
      if i = j then 𝟙 _ else 0 := by
  have key (r : T) : b.coord j (algebraMap T T' r * b i) = if i = j then r else 0 := by
    rw [← Algebra.smul_def, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply, smul_eq_mul, mul_ite, _root_.mul_one, MulZeroClass.mul_zero]
  refine Mod.hom_ext _ _ ?_
  ext S x
  refine ULift.ext _ _ (ContinuousMap.ext fun s ↦ (key (x.down s)).trans ?_)
  split_ifs <;> rfl

/-- The coordinates `T̲' ⟶ T̲ᵈ` of the basis `b` followed by the linear combination `T̲ᵈ ⟶ T̲'`
with coefficients in `b` is the identity of `T̲ᵈ`. -/
lemma desc_continuousMapSMulRightHom_comp_lift :
    ((biproduct.desc fun i ↦ continuousMapSMulRightHom.{u} hφ (b i)) ≫
      biproduct.lift fun i ↦ continuousMapLinearMapHom hφ (b.coord i) (hb i)) = 𝟙 _ := by
  refine biproduct.hom_ext _ _ fun j ↦ biproduct.hom_ext' _ _ fun i ↦ ?_
  simp only [Category.assoc, Category.id_comp, biproduct.ι_desc_assoc, biproduct.lift_π,
    continuousMapSMulRightHom_comp_linearMapHom_coord, biproduct.ι_π]
  split_ifs with h
  · subst h
    rfl
  · rfl

/-- The coordinates `T̲' ⟶ T̲ᵈ` of the basis `b` form a monomorphism: a section of `T̲'` all of
whose coordinates vanish is zero. -/
lemma mono_lift_continuousMapLinearMapHom :
    Mono (biproduct.lift fun i ↦ continuousMapLinearMapHom.{u} hφ (b.coord i) (hb i)) := by
  refine Preadditive.mono_of_cancel_zero _ fun {W} z hz ↦ ?_
  have hj (j : Fin d) : z ≫ continuousMapLinearMapHom hφ (b.coord j) (hb j) = 0 := by
    rw [← biproduct.lift_π (fun i ↦ continuousMapLinearMapHom.{u} hφ (b.coord i) (hb i)) j,
      ← Category.assoc, hz, zero_comp]
  refine Mod.hom_ext _ _ ?_
  ext S w
  refine (ULift.ext _ 0 (ContinuousMap.ext fun s ↦ b.ext_elem fun j ↦ ?_)).trans rfl
  have h : b.coord j ((((z.hom.hom.app S).hom w) : ULift.{u + 1} C(S.unop, T')).down s) = 0 :=
    congrArg (fun φ : W ⟶ Mod.regular (continuousMapRingObj T) ↦
      (((φ.hom.hom.app S).hom w) : ULift.{u + 1} C(S.unop, T)).down s) (hj j)
  rw [Module.Basis.coord_apply] at h
  rw [h, ULift.zero_down, ContinuousMap.zero_apply, map_zero, Finsupp.zero_apply]

/-- **`T̲'` is finite free over `T̲`.** If `T'` is a free `T`-module with a basis `b` of `d`
elements whose coordinate functionals are continuous, then `C(S, T') ≅ C(S, T)ᵈ` naturally in the
profinite set `S`, `T̲`-linearly: the condensed ring `T̲'`, regarded as a `T̲`-module, is free of
rank `d`. -/
noncomputable def comapRegularIsoFiniteFree :
    (Mod.comap (continuousMapRingObjAlgebraMap.{u} hφ)).obj
        (Mod.regular (continuousMapRingObj T')) ≅
      Mod.finiteFree (continuousMapRingObj.{u} T) d where
  hom := biproduct.lift fun i ↦ continuousMapLinearMapHom hφ (b.coord i) (hb i)
  inv := biproduct.desc fun i ↦ continuousMapSMulRightHom hφ (b i)
  hom_inv_id := by
    have := mono_lift_continuousMapLinearMapHom.{u} hφ b hb
    rw [← cancel_mono (biproduct.lift fun i ↦ continuousMapLinearMapHom hφ (b.coord i) (hb i)),
      Category.assoc, desc_continuousMapSMulRightHom_comp_lift, Category.comp_id,
      Category.id_comp]
  inv_hom_id := desc_continuousMapSMulRightHom_comp_lift hφ b hb

end FiniteFree

end Profinite
