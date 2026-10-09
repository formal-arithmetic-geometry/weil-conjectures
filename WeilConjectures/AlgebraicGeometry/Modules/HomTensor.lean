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
