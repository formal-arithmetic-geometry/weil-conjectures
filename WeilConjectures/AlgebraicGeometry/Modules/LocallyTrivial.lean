/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Sheaves.LocallySurjective
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Category

/-!
# An invertible sheaf of modules is locally isomorphic to the structure sheaf
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite TensorProduct

universe v₁ u₁ u

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {R : Sheaf J CommRingCat.{u}}

variable (F G : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))

/-- The underlying presheaf of modules of a sheaf of modules, spelled as a presheaf of modules
over the underlying presheaf of rings of `R`, so that the monoidal structure of
`PresheafOfModules` is found by instance resolution. -/
abbrev presheafOfModules : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  (SheafOfModules.forget _).obj F

/-- The sheafification of the underlying presheaf of modules of a sheaf of modules is that
sheaf of modules; this is the counit of the sheafification adjunction. -/
noncomputable def sheafificationObjIso : (sheafification R).obj (presheafOfModules F) ≅ F :=
  (asIso (PresheafOfModules.sheafificationAdjunction
    (𝟙 (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj))).counit).app F

/-- **The tensor product of two sheaves of modules is the sheafification of the sectionwise
tensor product** of the underlying presheaves of modules. -/
noncomputable def tensorSheafificationIso :
    (sheafification R).obj (presheafOfModules F ⊗ presheafOfModules G) ≅ F ⊗ G :=
  (Functor.Monoidal.μIso (sheafification R) _ _).symm ≪≫
    tensorIso (sheafificationObjIso F) (sheafificationObjIso G)

/-- The canonical morphism from the sectionwise tensor product of the underlying presheaves of
modules of `F` and `G` to the underlying presheaf of modules of `F ⊗ G`. -/
noncomputable def tensorPresheafHom :
    presheafOfModules F ⊗ presheafOfModules G ⟶
      (PresheafOfModules.restrictScalars
        (𝟙 (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj))).obj
          (presheafOfModules (F ⊗ G)) :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj))).homEquiv _ _
      (tensorSheafificationIso F G).hom

lemma toPresheaf_map_tensorPresheafHom :
    (PresheafOfModules.toPresheaf _).map (tensorPresheafHom F G) =
      CategoryTheory.toSheafify J (presheafOfModules F ⊗ presheafOfModules G).presheaf ≫
        (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
          (tensorSheafificationIso F G).hom := rfl

/-- The comparison morphism from the sectionwise tensor product to the tensor product becomes an
isomorphism after sheafification; in particular it is locally bijective. -/
lemma w_toPresheaf_map_tensorPresheafHom :
    J.W ((PresheafOfModules.toPresheaf _).map (tensorPresheafHom F G)) := by
  have h : J.W ((SheafOfModules.forget
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      PresheafOfModules.toPresheaf _).map (tensorSheafificationIso F G).hom) :=
    J.W.of_isIso _
  rw [toPresheaf_map_tensorPresheafHom]
  exact J.W.comp_mem _ _ (J.W_toSheafify _) h

end SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

instance (U : X.Opens) (M : X.Modules) :
    Module Γ(X, U) ((SheafOfModules.presheafOfModules M).obj (op U)) :=
  inferInstanceAs (Module Γ(X, U) Γ(M, U))

variable (e : M ⊗ N ≅ SheafOfModules.unit X.ringCatSheaf)

set_option backward.isDefEq.respectTransparency false in
/-- The pairing of sections of `M` and of `N` over an open `U` determined by an isomorphism
`M ⊗ N ≅ 𝒪_X`: a section of `M` and a section of `N` over `U` have a product in `Γ(X, U)`,
obtained by pushing their tensor product through the comparison morphism
`SheafOfModules.tensorPresheafHom` and then through `e`. -/
noncomputable def tensorPairing (U : X.Opens) :
    Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) →ₗ[Γ(X, U)] Γ(X, U) :=
  LinearMap.compr₂ (TensorProduct.mk Γ(X, U) Γ(M, U) Γ(N, U))
    { toFun := fun t ↦ Hom.app e.hom U (((SheafOfModules.tensorPresheafHom M N).app (op U)).hom t)
      map_add' := fun t t' ↦ by rw [map_add, map_add]
      map_smul' := fun r t ↦ by rw [RingHom.id_apply, _root_.map_smul, Hom.app_smul] }

variable {e}

lemma tensorPairing_apply (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) :
    tensorPairing e U m n =
      Hom.app e.hom U (((SheafOfModules.tensorPresheafHom M N).app (op U)).hom
        (m ⊗ₜ[Γ(X, U)] n)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma tensorPairing_tmul (U : X.Opens) (t : Γ(M, U) ⊗[Γ(X, U)] Γ(N, U)) :
    Hom.app e.hom U (((SheafOfModules.tensorPresheafHom M N).app (op U)).hom t) =
      TensorProduct.lift (tensorPairing e U) t := by
  induction t with
  | zero => simp
  | tmul m n => rfl
  | add t t' h h' => rw [map_add, map_add, map_add, h, h']

set_option backward.isDefEq.respectTransparency false in
/-- The pairing of sections is compatible with restriction to a smaller open subset. -/
lemma map_tensorPairing {U V : X.Opens} (i : V ⟶ U) (m : Γ(M, U)) (n : Γ(N, U)) :
    X.presheaf.map i.op (tensorPairing e U m n) =
      tensorPairing e V (M.presheaf.map i.op m) (N.presheaf.map i.op n) := by
  rw [tensorPairing_apply, tensorPairing_apply]
  have h₁ := CategoryTheory.congr_fun ((Hom.mapPresheaf e.hom).naturality i.op)
    (((SheafOfModules.tensorPresheafHom M N).app (op U)).hom (m ⊗ₜ[Γ(X, U)] n))
  have h₂ := PresheafOfModules.naturality_apply (SheafOfModules.tensorPresheafHom M N) i.op
    (m ⊗ₜ[Γ(X, U)] n)
  simp only [ConcreteCategory.comp_apply, mapPresheaf_app] at h₁
  refine h₁.symm.trans ?_
  exact congrArg (ConcreteCategory.hom (Hom.app e.hom V)) h₂.symm

set_option backward.isDefEq.respectTransparency false in
/-- **Any point has a neighbourhood on which `M` and `N` have sections pairing to `1`.** -/
lemma exists_tensorPairing_eq_one (x : X) :
    ∃ (V : X.Opens) (_ : x ∈ V) (m : Γ(M, V)) (n : Γ(N, V)), tensorPairing e V m n = 1 := by
  have h1 : TopCat.Presheaf.IsLocallySurjective
      ((PresheafOfModules.toPresheaf _).map (SheafOfModules.tensorPresheafHom M N)) :=
    (SheafOfModules.w_toPresheaf_map_tensorPresheafHom M N).isLocallySurjective
  obtain ⟨V, hVle, ⟨s, hs⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff _).1 h1 ⊤ (Hom.app e.inv ⊤ (1 : Γ(X, ⊤))) x trivial
  have key : TensorProduct.lift (tensorPairing e V) s = 1 := by
    rw [← tensorPairing_tmul]
    have hs' : ((SheafOfModules.tensorPresheafHom M N).app (op V)).hom s =
        (M ⊗ N).presheaf.map (homOfLE hVle).op (Hom.app e.inv ⊤ (1 : Γ(X, ⊤))) := hs
    have hnat := CategoryTheory.congr_fun ((Hom.mapPresheaf e.hom).naturality (homOfLE hVle).op)
      (Hom.app e.inv ⊤ (1 : Γ(X, ⊤)))
    simp only [ConcreteCategory.comp_apply, mapPresheaf_app] at hnat
    have hone : Hom.app e.hom ⊤ (Hom.app e.inv ⊤ (1 : Γ(X, ⊤))) = (1 : Γ(X, ⊤)) := by
      rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, e.inv_hom_id, Hom.id_app,
        ConcreteCategory.id_apply]
    rw [hs', hnat, hone]
    exact (X.presheaf.map (homOfLE hVle).op).hom.map_one
  obtain ⟨t, key⟩ : ∃ t : Γ(M, V) ⊗[Γ(X, V)] Γ(N, V),
      TensorProduct.lift (tensorPairing e V) t = 1 := ⟨s, key⟩
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset t
  rw [hS, map_sum] at key
  simp only [TensorProduct.lift.tmul] at key
  have hgerm : IsUnit (∑ p ∈ S, X.presheaf.germ V x hxV (tensorPairing e V p.1 p.2)) := by
    rw [← map_sum, key, map_one]
    exact isUnit_one
  obtain ⟨p, -, hp⟩ := IsLocalRing.exists_of_isUnit_sum hgerm
  have hunit : IsUnit (X.presheaf.map
      (homOfLE (X.basicOpen_le (tensorPairing e V p.1 p.2))).op (tensorPairing e V p.1 p.2)) :=
    X.toRingedSpace.isUnit_res_basicOpen _
  obtain ⟨u, hu⟩ := hunit
  refine ⟨X.basicOpen (tensorPairing e V p.1 p.2),
    (Scheme.mem_basicOpen X _ x hxV).2 hp,
    M.presheaf.map (homOfLE (X.basicOpen_le _)).op p.1,
    ((u⁻¹ : (Γ(X, X.basicOpen (tensorPairing e V p.1 p.2)))ˣ) :
      Γ(X, X.basicOpen (tensorPairing e V p.1 p.2))) •
      N.presheaf.map (homOfLE (X.basicOpen_le _)).op p.2, ?_⟩
  rw [_root_.map_smul, ← map_tensorPairing, ← hu, smul_eq_mul]
  exact u.inv_mul

end AlgebraicGeometry.Scheme.Modules
