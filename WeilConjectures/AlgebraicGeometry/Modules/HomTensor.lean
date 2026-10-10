/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Dual

/-!
# `Hom(M, N) ≅ Mᵛ ⊗ N` for an invertible `N`

For sheaves of modules `M`, `N` on a scheme there is a natural morphism
`Mᵛ ⊗ N ⟶ Hom(M, N)`, `φ ⊗ n ↦ (m ↦ φ(m) n)`. If `N` is invertible it is an isomorphism: it is
the sheafification of a morphism of presheaves of modules which is bijective on sections over
every open on which `N` is trivial.

## Main definitions and results

- `PresheafOfModules.dualTensorHom`: the morphism `Hom(M, R) ⊗ P ⟶ Hom(M, P)` of presheaves of
  modules, and `PresheafOfModules.dualTensorHom_app_bijective`: it is bijective on sections
  over an object on which `P` is free of rank one.
- `AlgebraicGeometry.Scheme.Modules.dualTensorHom`: the morphism `Mᵛ ⊗ N ⟶ Hom(M, N)` of sheaves
  of modules on a scheme.
- `AlgebraicGeometry.Scheme.Modules.isIso_dualTensorHom`: it is an isomorphism if `N` is
  invertible.
- `AlgebraicGeometry.Scheme.Modules.isIso_dualTensorHom_of_isFiniteLocallyFree`: it is an
  isomorphism if `M` is finite locally free.
- `AlgebraicGeometry.Scheme.Modules.dualTensorHom_naturality_right`: it is natural in `N`.
- `AlgebraicGeometry.Scheme.Modules.dualTensorHomIso`: the natural isomorphism
  `Mᵛ ⊗ N ≅ Hom(M, N)` for an invertible `N`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Opposite

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (M P : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

/-- The morphism `Hom(M, R) ⊗ P ⟶ Hom(M, P)` of presheaves of modules, sending `φ ⊗ p` to
`m ↦ φ(m) • p`. -/
noncomputable def dualTensorHom : homObj M (unit _) ⊗ P ⟶ homObj M P :=
  tensorHomCurry ((α_ M (homObj M (unit _)) P).inv ≫ tensorHomUncurry (𝟙 _) ▷ P ≫ (λ_ P).hom)

/-- `Hom(M, R) ⊗ P ⟶ Hom(M, P)` sends `φ ⊗ p` to `m ↦ φ(m) • p`. -/
lemma dualTensorHom_app_tmul_app_apply {U : C} (φ : (homObj M (unit _)).obj (op U))
    (p : P.obj (op U)) (W : (Over U)ᵒᵖ) (m : M.obj (op W.unop.left)) :
    (((dualTensorHom M P).app (op U) (φ ⊗ₜ p)).app W) m =
      (show R.obj (op W.unop.left) from (φ.app W) m) • P.map W.unop.hom.op p := by
  refine (?_ : _ = (show R.obj (op W.unop.left) from
    (φ.app (op (Over.mk (𝟙 W.unop.left ≫ W.unop.hom)))) m) • P.map W.unop.hom.op p).trans ?_
  · rfl
  · rw [restrictOver_hom_app_congr φ (Category.id_comp W.unop.hom) m]
    rfl

variable {M P} in
/-- The morphism `Hom(M, R) ⊗ P ⟶ Hom(M, P)` is bijective on sections over `U` if `P` is free of
rank one over `U`, with basis `p₀` and coordinate `φ₀`. -/
lemma dualTensorHom_app_bijective {U : C} (p₀ : P.obj (op U))
    (φ₀ : (restrictOver R U).obj P ⟶ (restrictOver R U).obj (unit _))
    (hφ₀ : ∀ (V : (Over U)ᵒᵖ) (r : R.obj (op V.unop.left)),
      (φ₀.app V) (r • P.map V.unop.hom.op p₀) = r)
    (hgen : ∀ (V : (Over U)ᵒᵖ) (x : P.obj (op V.unop.left)),
      ∃ r : R.obj (op V.unop.left), x = r • P.map V.unop.hom.op p₀) :
    Function.Bijective ((dualTensorHom M P).app (op U)) := by
  have hp₀ : ∀ p : P.obj (op U), ∃ r : (R ⋙ forget₂ CommRingCat RingCat).obj (op U),
      p = r • p₀ := fun p ↦ by
    obtain ⟨r, hr⟩ := hgen (op (Over.mk (𝟙 U))) p
    refine ⟨r, hr.trans (congrArg (fun q : P.obj (op U) ↦ r • q) ?_)⟩
    change P.map (𝟙 (op U)) p₀ = p₀
    rw [PresheafOfModules.map_id]
    rfl
  have key (t : ((homObj M (unit _)) ⊗ P).obj (op U)) :
      ∃ φ : (homObj M (unit _)).obj (op U), t = φ ⊗ₜ p₀ := by
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul φ p =>
      obtain ⟨a, rfl⟩ := hp₀ p
      exact ⟨a • φ, (TensorProduct.smul_tmul _ _ _).symm⟩
    | add t t' ht ht' =>
      obtain ⟨φ, rfl⟩ := ht
      obtain ⟨φ', rfl⟩ := ht'
      exact ⟨φ + φ', (TensorProduct.add_tmul _ _ _).symm⟩
  refine ⟨?_, fun ψ ↦ ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨φ, rfl⟩ := key t
    suffices hφ : φ = 0 by rw [hφ, TensorProduct.zero_tmul]
    refine hom_ext fun V ↦ ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)
    have h := congrArg (fun ξ : (restrictOver R U).obj M ⟶ (restrictOver R U).obj P ↦
      φ₀.app V (ξ.app V m)) ht
    simp only at h
    rw [dualTensorHom_app_tmul_app_apply, hφ₀] at h
    exact h.trans (map_zero (φ₀.app V).hom)
  · refine ⟨(ψ ≫ φ₀) ⊗ₜ p₀, hom_ext fun V ↦ ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)⟩
    rw [dualTensorHom_app_tmul_app_apply]
    obtain ⟨r, hr⟩ := hgen V (ψ.app V m)
    change (φ₀.app V (ψ.app V m)) • _ = _
    rw [hr, hφ₀]

variable {M P} in
/-- **`Hom(M, R) ⊗ P ≅ Hom(M, P)` for `M` free of finite rank.** If `M|_U` is a finite direct sum
of copies of `R|_U`, with inclusions `s i` and projections `c i`, then `Hom(M, R) ⊗ P ⟶ Hom(M, P)`
is bijective on sections over `U`: both sides are `⨁ᵢ P(U)`, through `ψ ↦ (ψ(s i 1))ᵢ` and
`∑ᵢ c i ⊗ pᵢ ↤ (pᵢ)ᵢ`. -/
lemma dualTensorHom_app_bijective_of_free {U : C} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ((restrictOver R U).obj (unit _) ⟶ (restrictOver R U).obj M))
    (c : ι → ((restrictOver R U).obj M ⟶ (restrictOver R U).obj (unit _)))
    (hsc : ∀ i j, s j ≫ c i = if j = i then 𝟙 _ else 0)
    (htot : ∑ i, c i ≫ s i = 𝟙 _) :
    Function.Bijective ((dualTensorHom M P).app (op U)) := by
  let T : (Over U)ᵒᵖ := op (Over.mk (𝟙 U))
  let m : ι → M.obj (op U) := fun i ↦ (s i).app T (1 : R.obj (op U))
  -- Every section of `M` over `W ⟶ U` is a combination of the restrictions of the `m i`.
  have hspan (W : (Over U)ᵒᵖ) (x : M.obj (op W.unop.left)) :
      x = ∑ i, (show R.obj (op W.unop.left) from (c i).app W x) •
        (show M.obj (op W.unop.left) from M.map W.unop.hom.op (m i)) := by
    have h : ∑ i, (c i ≫ s i).app W x = x :=
      (sum_app_apply Finset.univ (fun i ↦ c i ≫ s i) W x).symm.trans
        (congrArg (fun f ↦ f.app W x) htot)
    exact h.symm.trans (Finset.sum_congr rfl fun i _ ↦ app_unit_eq_smul (s i) W _)
  have hcm (i j : ι) : (c i).app T (m j) = if j = i then (1 : R.obj (op U)) else 0 := by
    have h := congrArg (fun f ↦ f.app T (1 : R.obj (op U))) (hsc i j)
    refine h.trans ?_
    split_ifs <;> rfl
  -- A morphism out of `M|_U` is determined by its values on the `m i`.
  have hval {Q : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}
      (ψ : (restrictOver R U).obj M ⟶ (restrictOver R U).obj Q) (W : (Over U)ᵒᵖ)
      (x : M.obj (op W.unop.left)) :
      ψ.app W x = ∑ i, (show R.obj (op W.unop.left) from (c i).app W x) •
        (show Q.obj (op W.unop.left) from Q.map W.unop.hom.op (ψ.app T (m i))) := by
    refine (congrArg (ψ.app W) (hspan W x)).trans ?_
    refine (map_sum (ψ.app W).hom _ _).trans (Finset.sum_congr rfl fun i _ ↦ ?_)
    refine ((ψ.app W).hom.map_smul _ _).trans (congrArg (_ • ·) ?_)
    exact naturality_apply ψ
      (Over.homMk W.unop.hom (Category.comp_id _) : W.unop ⟶ Over.mk (𝟙 U)).op (m i)
  let c' : ι → (homObj M (unit _)).obj (op U) := c
  let a (φ : (homObj M (unit _)).obj (op U)) (i : ι) :
      (R ⋙ forget₂ CommRingCat RingCat).obj (op U) :=
    (show R.obj (op U) from φ.app T (m i))
  -- Every dual element is a combination of the `c i`.
  have hdual (φ : (homObj M (unit _)).obj (op U)) : φ = ∑ i, a φ i • c' i := by
    refine hom_ext (M₁ := (restrictOver R U).obj M) (M₂ := (restrictOver R U).obj (unit _))
      fun W ↦ ?_
    ext y
    refine (hval φ W y).trans ?_
    refine Eq.trans ?_ (sum_app_apply _ _ W y).symm
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    refine Eq.trans ?_ (restrictOver_smul_app_apply _ (c i) W y).symm
    change (show R.obj (op W.unop.left) from (c i).app W y) *
        (show R.obj (op W.unop.left) from R.map W.unop.hom.op (φ.app T (m i))) =
      R.map W.unop.hom.op (φ.app T (m i)) * (show R.obj (op W.unop.left) from (c i).app W y)
    exact mul_comm _ _
  -- Every element of `Hom(M, R) ⊗ P` over `U` is `∑ i, c i ⊗ pᵢ`.
  have key (t : ((homObj M (unit _)) ⊗ P).obj (op U)) :
      ∃ p : ι → P.obj (op U), t = ∑ i, c' i ⊗ₜ p i := by
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul φ q =>
      refine ⟨fun i ↦ a φ i • q, ?_⟩
      conv_lhs => rw [hdual φ]
      rw [TensorProduct.sum_tmul]
      exact Finset.sum_congr rfl fun i _ ↦ TensorProduct.smul_tmul _ _ _
    | add t t' ht ht' =>
      obtain ⟨p, rfl⟩ := ht
      obtain ⟨p', rfl⟩ := ht'
      exact ⟨p + p', by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]⟩
  have hsingle (i j : ι) (p : P.obj (op U)) :
      ((dualTensorHom M P).app (op U) (c' i ⊗ₜ p)).app T (m j) = if j = i then p else 0 := by
    rw [dualTensorHom_app_tmul_app_apply, hcm]
    split_ifs
    · exact (one_smul _ _).trans (P.map_id_apply' p)
    · exact zero_smul _ _
  -- The image of `∑ i, c i ⊗ pᵢ` sends `m j` to `p j`.
  have himage (p : ι → P.obj (op U)) (j : ι) :
      ((dualTensorHom M P).app (op U) (∑ i, c' i ⊗ₜ p i)).app T (m j) = p j := by
    rw [map_sum, sum_app_apply]
    simp only [hsingle]
    simp
  constructor
  · rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨p, rfl⟩ := key t
    have hp (j : ι) : p j = 0 := by
      rw [← himage p j, ht]
      rfl
    simp [hp]
  · intro ψ
    refine ⟨∑ i, c' i ⊗ₜ ψ.app T (m i), ?_⟩
    refine hom_ext (M₁ := (restrictOver R U).obj M) (M₂ := (restrictOver R U).obj P)
      fun W ↦ ?_
    ext x
    rw [map_sum, sum_app_apply, hval ψ W x]
    exact Finset.sum_congr rfl fun i _ ↦ dualTensorHom_app_tmul_app_apply M P _ _ W x

variable {M P} in
/-- If `M` is free of finite rank on `U`, then `Hom(M, R) ⊗ P ⟶ Hom(M, P)` is bijective on
sections over every `V ⟶ U`. -/
lemma dualTensorHom_app_bijective_of_hom {U : C} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ((restrictOver R U).obj (unit _) ⟶ (restrictOver R U).obj M))
    (c : ι → ((restrictOver R U).obj M ⟶ (restrictOver R U).obj (unit _)))
    (hsc : ∀ i j, s j ≫ c i = if j = i then 𝟙 _ else 0)
    (htot : ∑ i, c i ≫ s i = 𝟙 _) {V : C} (g : V ⟶ U) :
    Function.Bijective ((dualTensorHom M P).app (op V)) := by
  refine dualTensorHom_app_bijective_of_free (fun i ↦ restrictOverMap g (s i))
    (fun i ↦ restrictOverMap g (c i)) (fun i j ↦ ?_) ?_
  · change restrictOverMap g (s j ≫ c i) = _
    rw [hsc]
    split_ifs
    · exact restrictOverMap_id (R := R) (M := unit _) (N := unit _) (𝟙 _)
    · rfl
  · change ∑ i, restrictOverMap g (c i ≫ s i) = _
    rw [← restrictOverMap_sum, htot]
    rfl

variable {M} in
/-- `Hom(M, R) ⊗ P ⟶ Hom(M, P)` is natural in `M`: for `f : M ⟶ M'` the square
```
  Hom(M', R) ⊗ P ---> Hom(M', P)
        |                  |
  f^* ⊗ P                 f^*
        v                  v
  Hom(M, R) ⊗ P  ---> Hom(M, P)
```
commutes. -/
lemma dualTensorHom_naturality {M' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (f : M ⟶ M') :
    homObjMap f (𝟙 (unit _)) ▷ P ≫ dualTensorHom M P =
      dualTensorHom M' P ≫ homObjMap f (𝟙 P) := by
  ext U : 1
  refine ModuleCat.MonoidalCategory.tensor_ext fun φ p ↦ ?_
  refine hom_ext fun W ↦ ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)
  exact (dualTensorHom_app_tmul_app_apply M P _ p W m).trans
    (dualTensorHom_app_tmul_app_apply M' P φ p W _).symm


variable {P} in
/-- `Hom(M, R) ⊗ P ⟶ Hom(M, P)` is natural in `P`: for `g : P ⟶ P'` the square
```
  Hom(M, R) ⊗ P  ---> Hom(M, P)
        |                 |
  Hom(M, R) ⊗ g          g_*
        v                 v
  Hom(M, R) ⊗ P' ---> Hom(M, P')
```
commutes. -/
lemma dualTensorHom_naturality_right {P' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}
    (g : P ⟶ P') :
    homObj M (unit _) ◁ g ≫ dualTensorHom M P' = dualTensorHom M P ≫ homObjMap (𝟙 M) g := by
  ext U : 1
  refine ModuleCat.MonoidalCategory.tensor_ext fun φ p ↦ ?_
  refine hom_ext fun W ↦ ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)
  refine (dualTensorHom_app_tmul_app_apply M P' φ (g.app _ p) W m).trans ?_
  change _ = g.app (op W.unop.left) ((((dualTensorHom M P).app U (φ ⊗ₜ p)).app W) m)
  rw [dualTensorHom_app_tmul_app_apply, (g.app _).hom.map_smul, naturality_apply]
end PresheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

set_option maxHeartbeats 1000000 in
-- The rewrites through the localized monoidal structure on sheaves of modules are slow.
/-- The identification `M ⊗ P ≅ a(M ⊗ P)` of the tensor product of sheaves of modules with the
sheafification of the tensor product of presheaves is natural in `M`: for `f : M ⟶ M'` the square
```
  M ⊗ P  ---------> a(M ⊗ P)
    |                  |
  f ⊗ P             a(f ⊗ P)
    v                  v
  M' ⊗ P ---------> a(M' ⊗ P)
```
commutes. -/
lemma whiskerRight_tensorObjIsoSheafification_hom {M M' : X.Modules} (f : M ⟶ M')
    (P : X.Modules) :
    f ▷ P ≫ (SheafOfModules.tensorObjIsoSheafification (R := X.sheaf) M' P).hom =
      (SheafOfModules.tensorObjIsoSheafification (R := X.sheaf) M P).hom ≫
        (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (f.val ▷ P.val) := by
  let := SheafOfModules.sheafificationMonoidal X.sheaf
  simp only [SheafOfModules.tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom,
    Functor.Monoidal.μIso_hom, Category.assoc]
  erw [← Functor.LaxMonoidal.μ_natural_left]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  simp only [tensorIso_inv, Iso.app_inv, asIso_inv]
  rw [← tensorHom_id (C := X.Modules), ← tensorHom_id (C := X.Modules),
    tensorHom_comp_tensorHom (C := X.Modules), tensorHom_comp_tensorHom (C := X.Modules)]
  erw [Category.id_comp]
  congr 1
  exact (inv (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).naturality
    f

/-- The morphism `Mᵛ ⊗ N ⟶ Hom(M, N)`, `φ ⊗ n ↦ (m ↦ φ(m) n)`, of sheaves of modules: the
sheafification of the corresponding morphism of presheaves of modules. -/
noncomputable def dualTensorHom (M N : X.Modules) : Mᵛ ⊗ N ⟶ homObj M N :=
  (SheafOfModules.tensorObjIsoSheafification (R := X.sheaf) Mᵛ N).hom ≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModules.dualTensorHom M.val N.val) ≫
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app (homObj M N)

/-- If `N` is trivial on an open `U`, then `Mᵛ ⊗ N ⟶ Hom(M, N)` is bijective on sections of
the underlying presheaves over every open `V ⊆ U`. -/
lemma presheafDualTensorHom_app_bijective {M N : X.Modules} {U V : X.Opens} (g : V ⟶ U)
    (E : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    Function.Bijective ((PresheafOfModules.dualTensorHom M.val N.val).app (op V)) := by
  have hE (W : Over V) : N.val.map W.hom.op (E.inv.val.app (op (Over.mk g)) (1 : Γ(X, V))) =
      E.inv.val.app (op (Over.mk (W.hom ≫ g))) (1 : Γ(X, W.left)) := by
    refine (PresheafOfModules.naturality_apply E.inv.val
      (Over.homMk W.hom (Subsingleton.elim _ _) : Over.mk (W.hom ≫ g) ⟶ Over.mk g).op
      (1 : Γ(X, V))).symm.trans ?_
    exact congrArg (E.inv.val.app (op (Over.mk (W.hom ≫ g))))
      (PresheafOfModules.unit_map_one (R := X.ringCatSheaf.obj) W.hom.op)
  refine PresheafOfModules.dualTensorHom_app_bijective
    (E.inv.val.app (op (Over.mk g)) (1 : Γ(X, V)))
    { app W := E.hom.val.app (op (Over.mk (W.unop.hom ≫ g)))
      naturality {A B} f := E.hom.val.naturality (Over.homMk f.unop.left (Subsingleton.elim _ _) :
        Over.mk (B.unop.hom ≫ g) ⟶ Over.mk (A.unop.hom ≫ g)).op } (fun W r ↦ ?_) (fun W x ↦ ?_)
  · have h1 : E.hom.val.app (op (Over.mk (W.unop.hom ≫ g)))
        (E.inv.val.app (op (Over.mk (W.unop.hom ≫ g))) (1 : Γ(X, W.unop.left))) =
          (1 : Γ(X, W.unop.left)) :=
      congrArg (fun f ↦ f.val.app (op (Over.mk (W.unop.hom ≫ g))) (1 : Γ(X, W.unop.left)))
        E.inv_hom_id
    erw [hE W.unop, (E.hom.val.app _).hom.map_smul, h1]
    exact mul_one r
  · refine ⟨E.hom.val.app (op (Over.mk (W.unop.hom ≫ g))) x, ?_⟩
    have h2 : E.inv.val.app (op (Over.mk (W.unop.hom ≫ g)))
        (E.hom.val.app (op (Over.mk (W.unop.hom ≫ g))) x) = x :=
      congrArg (fun f ↦ f.val.app (op (Over.mk (W.unop.hom ≫ g))) x) E.hom_inv_id
    erw [hE W.unop, ← (E.inv.val.app _).hom.map_smul, smul_eq_mul, mul_one, h2]

/-- **`Hom(M, N) ≅ Mᵛ ⊗ N` for an invertible `N`.** The morphism `Mᵛ ⊗ N ⟶ Hom(M, N)` is an
isomorphism if `N` is invertible: it is the sheafification of a morphism of presheaves which is
bijective on sections over every open on which `N` is trivial. -/
instance isIso_dualTensorHom (M N : X.Modules) [N.IsInvertible] : IsIso (dualTensorHom M N) := by
  choose U hU e using fun x : X ↦ IsInvertible.exists_isoUnit (M := N) x
  have hcov : (Opens.grothendieckTopology X).CoversTop U := by
    rw [Opens.coversTop_iff]
    exact TopologicalSpace.IsOpenCover.mk
      (eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hU x⟩)
  have hW : (Opens.grothendieckTopology X).W.inverseImage
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj)
      (PresheafOfModules.dualTensorHom M.val N.val) :=
    (GrothendieckTopology.W_iff_isLocallyBijective _ _).2
      ⟨Presheaf.isLocallyInjective_of_coversTop hcov _ fun V x g ↦
        (presheafDualTensorHom_app_bijective g (overIsoUnitOfPullbackIotaIso (e x).some)).1,
      Presheaf.isLocallySurjective_of_coversTop hcov _ fun V x g ↦
        (presheafDualTensorHom_app_bijective g (overIsoUnitOfPullbackIotaIso (e x).some)).2⟩
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (𝟙 X.ringCatSheaf.obj)] at hW
  have : IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (PresheafOfModules.dualTensorHom M.val N.val)) := hW
  have hc : IsIso ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app
    (homObj M N)) := inferInstance
  exact IsIso.comp_isIso' (Iso.isIso_hom _) (IsIso.comp_isIso' this hc)

/-- `Mᵛ ⊗ N ⟶ Hom(M, N)` is natural in `M`: for `f : M ⟶ M'` the square
```
  M'ᵛ ⊗ N ---> Hom(M', N)
     |              |
  fᵛ ⊗ N           f^*
     v              v
  Mᵛ ⊗ N  ---> Hom(M, N)
```
commutes. -/
lemma dualTensorHom_naturality {M M' : X.Modules} (f : M ⟶ M') (N : X.Modules) :
    dualMap f ▷ N ≫ dualTensorHom M N =
      dualTensorHom M' N ≫ SheafOfModules.homObjMap (R := X.sheaf) f (𝟙 N) := by
  simp only [dualTensorHom]
  rw [← Category.assoc, whiskerRight_tensorObjIsoSheafification_hom, Category.assoc,
    ← Functor.map_comp_assoc]
  erw [PresheafOfModules.dualTensorHom_naturality]
  rw [Functor.map_comp_assoc]
  erw [(PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.naturality
    (SheafOfModules.homObjMap (R := X.sheaf) f (𝟙 N))]
  rfl

/-- **`Hom(M, N) ≅ Mᵛ ⊗ N` for an invertible `N`**, naturally in `M`. -/
noncomputable def dualTensorHomIso (N : X.Modules) [N.IsInvertible] :
    dualFunctor X ⋙ tensorRight N ≅ (SheafOfModules.homFunctor X.sheaf).flip.obj N :=
  NatIso.ofComponents (fun M ↦ asIso (dualTensorHom M.unop N)) fun f ↦
    dualTensorHom_naturality f.unop N

end AlgebraicGeometry.Scheme.Modules

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})] {R : Sheaf J CommRingCat.{u}}

-- The underlying sheaf of rings of the sheaf of commutative rings `R`.
set_option hygiene false in
local notation "𝓡" => (sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R

variable {U : C} in
/-- If `M` is free of finite rank on `U`, then `Hom(M, R) ⊗ N ⟶ Hom(M, N)` is bijective on
sections over every `V ⟶ U`. -/
lemma dualTensorHom_app_bijective_of_iso_free [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] (M N : SheafOfModules.{u} 𝓡)
    {I : Type u} [Finite I] (e : free I ≅ M.over U) {V : C} (g : V ⟶ U) :
    Function.Bijective ((PresheafOfModules.dualTensorHom M.val N.val).app (op V)) := by
  classical
  let := Fintype.ofFinite I
  let S (j : I) : (unit 𝓡).over U ⟶ M.over U := Sigma.ι (fun _ ↦ unit _) j ≫ e.hom
  let Cc (j : I) : M.over U ⟶ (unit 𝓡).over U :=
    e.inv ≫ Sigma.desc (fun k ↦ if k = j then 𝟙 (unit _) else 0)
  have hsc (i j : I) : S j ≫ Cc i = if j = i then 𝟙 _ else 0 := by
    simp only [S, Cc, Category.assoc, Iso.hom_inv_id_assoc, Sigma.ι_desc]
    rfl
  have hsum : ∑ i, Sigma.desc (fun k ↦ if k = i then 𝟙 (unit _) else 0) ≫
      Sigma.ι (fun _ : I ↦ unit ((𝓡).over U)) i = 𝟙 (free I) := by
    refine Sigma.hom_ext _ _ fun k ↦ ?_
    rw [Preadditive.comp_sum, Finset.sum_eq_single k (fun b _ hb ↦ by simp [Ne.symm hb])
      (by simp)]
    simp only [Sigma.ι_desc_assoc]
    exact (Category.comp_id _).symm
  have htot : ∑ i, Cc i ≫ S i = 𝟙 _ := by
    calc ∑ i, Cc i ≫ S i = e.inv ≫ (∑ i, Sigma.desc (fun k ↦ if k = i then 𝟙 (unit _) else 0) ≫
          Sigma.ι (fun _ : I ↦ unit ((𝓡).over U)) i) ≫ e.hom := by
          simp only [Cc, S, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
          rfl
      _ = 𝟙 _ := by rw [hsum, Category.id_comp, Iso.inv_hom_id]
  refine PresheafOfModules.dualTensorHom_app_bijective_of_hom (P := N.val) (U := U)
    (fun j ↦ toRestrictOverHom (S j)) (fun j ↦ toRestrictOverHom (Cc j)) (fun i j ↦ ?_) ?_ g
  · refine (congrArg toRestrictOverHom (hsc i j)).trans ?_
    split_ifs
    · exact toRestrictOverHom_id _
    · exact toRestrictOverHom_zero _ _
  · exact (toRestrictOverHom_sum Finset.univ (fun i ↦ Cc i ≫ S i)).symm.trans
      ((congrArg toRestrictOverHom htot).trans (toRestrictOverHom_id M))

end SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

set_option maxHeartbeats 1000000 in
-- The rewrites through the localized monoidal structure on sheaves of modules are slow.
/-- The identification `M ⊗ P ≅ a(M ⊗ P)` of the tensor product of sheaves of modules with the
sheafification of the tensor product of presheaves is natural in `P`. -/
lemma whiskerLeft_tensorObjIsoSheafification_hom (M : X.Modules) {P P' : X.Modules}
    (g : P ⟶ P') :
    M ◁ g ≫ (SheafOfModules.tensorObjIsoSheafification (R := X.sheaf) M P').hom =
      (SheafOfModules.tensorObjIsoSheafification (R := X.sheaf) M P).hom ≫
        (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (M.val ◁ g.val) := by
  let := SheafOfModules.sheafificationMonoidal X.sheaf
  simp only [SheafOfModules.tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom,
    Functor.Monoidal.μIso_hom, Category.assoc]
  erw [← Functor.LaxMonoidal.μ_natural_right]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  simp only [tensorIso_inv, Iso.app_inv, asIso_inv]
  rw [← id_tensorHom (C := X.Modules), ← id_tensorHom (C := X.Modules),
    tensorHom_comp_tensorHom (C := X.Modules), tensorHom_comp_tensorHom (C := X.Modules)]
  erw [Category.id_comp]
  congr 1
  exact (inv (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).naturality
    g

/-- `Mᵛ ⊗ N ⟶ Hom(M, N)` is natural in `N`. -/
lemma dualTensorHom_naturality_right (M : X.Modules) {N N' : X.Modules} (g : N ⟶ N') :
    Mᵛ ◁ g ≫ dualTensorHom M N' =
      dualTensorHom M N ≫ SheafOfModules.homObjMap (R := X.sheaf) (𝟙 M) g := by
  simp only [dualTensorHom]
  rw [← Category.assoc, whiskerLeft_tensorObjIsoSheafification_hom, Category.assoc,
    ← Functor.map_comp_assoc]
  erw [PresheafOfModules.dualTensorHom_naturality_right]
  rw [Functor.map_comp_assoc]
  erw [(PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.naturality
    (SheafOfModules.homObjMap (R := X.sheaf) (𝟙 M) g)]
  rfl

/-- **`Hom(M, N) ≅ Mᵛ ⊗ N` for a finite locally free `M`.** The morphism
`Mᵛ ⊗ N ⟶ Hom(M, N)` is an isomorphism if `M` is finite locally free: it is the sheafification
of a morphism of presheaves which is bijective on sections over every open on which `M` is
free of finite rank. -/
instance isIso_dualTensorHom_of_isFiniteLocallyFree (M N : X.Modules)
    [M.IsFiniteLocallyFree] : IsIso (dualTensorHom M N) := by
  obtain ⟨q, hq, hf⟩ := SheafOfModules.IsFiniteLocallyFree.exists_localGeneratorsData (M := M)
  have hb (V : X.Opens) (i : q.I) (g : V ⟶ q.X i) :
      Function.Bijective ((PresheafOfModules.dualTensorHom M.val N.val).app (op V)) := by
    have := (hf.isFiniteType i).finite
    have := hq.isIso i
    exact SheafOfModules.dualTensorHom_app_bijective_of_iso_free (R := X.sheaf) M N
      (asIso (q.generators i).π) g
  have hW : (Opens.grothendieckTopology X).W.inverseImage
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj)
      (PresheafOfModules.dualTensorHom M.val N.val) :=
    (GrothendieckTopology.W_iff_isLocallyBijective _ _).2
      ⟨Presheaf.isLocallyInjective_of_coversTop q.coversTop _ fun V i g ↦ (hb V i g).1,
        Presheaf.isLocallySurjective_of_coversTop q.coversTop _ fun V i g ↦ (hb V i g).2⟩
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (𝟙 X.ringCatSheaf.obj)] at hW
  have : IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (PresheafOfModules.dualTensorHom M.val N.val)) := hW
  have hc : IsIso ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app
    (homObj M N)) := inferInstance
  exact IsIso.comp_isIso' (Iso.isIso_hom _) (IsIso.comp_isIso' this hc)

end AlgebraicGeometry.Scheme.Modules
