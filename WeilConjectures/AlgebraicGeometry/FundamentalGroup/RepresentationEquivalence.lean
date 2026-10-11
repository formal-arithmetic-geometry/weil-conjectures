/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Representation
public import WeilConjectures.CategoryTheory.Sites.Point.FreeYoneda

/-!
# The Galois correspondence for finite locally constant sheaves of modules

Let `Y` be a connected scheme with a geometric point `s`, let `G = π₁(Y, s)` be a fundamental
group of the fibre functor at `s` and let `Λ` be a finite ring. The geometric stalk at `s` is an
equivalence between finite locally constant sheaves of `Λ`-modules on the small étale site of
`Y` and finite `Λ`-modules with a continuous `G`-action.

## Strategy

For a finite étale `Y`-scheme `P`, the free sheaf `Λ[P]` is finite locally constant, with stalk
the permutation representation `Λ[P_s]`. Morphisms out of `Λ[P]` correspond to sections over
`P`, i.e. to morphisms of sheaves of sets out of `Hom_Y(-, P)`, and these correspond to
`G`-equivariant maps out of `P_s`: so the stalk functor is bijective on morphisms out of free
sheaves. Every finite locally constant sheaf of modules `F` is a quotient of a free sheaf
`Λ[P]` (take `P` representing the underlying sheaf of sets of `F`), with finite locally constant
kernel; together with the faithfulness of the stalk functor this gives full faithfulness.
Every finite continuous representation `V` is the cokernel of a map `Λ[K] ⟶ Λ[V]` of permutation
representations, which comes from a map of free sheaves; its cokernel is a finite locally
constant sheaf with stalk `V`, as the stalk functor is right exact.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteLocallyConstantModule

variable {Y : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

variable (Λ) in
/-- The free sheaf `Λ[P]` on a finite étale `Y`-scheme `P`, a finite locally constant sheaf of
`Λ`-modules. -/
noncomputable def free (P : Y.FiniteEtale) : Y.FiniteLocallyConstantModule Λ :=
  ⟨Sheaf.freeYoneda Y.smallEtaleTopology P.obj (ModuleCat.of Λ Λ),
    have : IsFinite P.obj.hom := P.property
    Etale.isFiniteLocallyConstantSheaf_freeYoneda_of_isFinite P.obj⟩

variable (Λ) in
/-- The generating section of `Λ[P]` over `P`, as a morphism of sheaves of sets
`Hom_Y(-, P) ⟶ Λ[P]`. -/
noncomputable def unit (P : Y.FiniteEtale) :
    (FiniteEtale.toFiniteLocallyConstant Y).obj P ⟶ (forget Y Λ).obj (free Λ P) :=
  ObjectProperty.homMk (ObjectProperty.homMk
    (uliftYonedaEquiv.symm
      (GrothendieckTopology.Point.sheafFreeYonedaGen (J := Y.smallEtaleTopology) Λ P.obj)))


section Sections

variable {F F' : Y.FiniteLocallyConstantModule Λ}

/-- The map on sections over `U` of a morphism of the underlying sheaves of sets. -/
abbrev sectionMap (f : (forget Y Λ).obj F ⟶ (forget Y Λ).obj F') (U : Y.Etaleᵒᵖ) :
    F.obj.obj.obj U → F'.obj.obj.obj U :=
  fun a ↦ f.hom.hom.app U a

/-- A morphism of the underlying sheaves of sets which is `Λ`-linear on sections is a morphism
of sheaves of `Λ`-modules. -/
noncomputable def homOfForget (f : (forget Y Λ).obj F ⟶ (forget Y Λ).obj F')
    (hadd : ∀ U (a b : F.obj.obj.obj U),
      sectionMap f U (a + b) = sectionMap f U a + sectionMap f U b)
    (hsmul : ∀ U (c : Λ) (a : F.obj.obj.obj U),
      sectionMap f U (c • a) = c • sectionMap f U a) :
    F ⟶ F' :=
  ObjectProperty.homMk (ObjectProperty.homMk
    { app U := ModuleCat.ofHom
        { toFun := f.hom.hom.app U
          map_add' := hadd U
          map_smul' := hsmul U }
      naturality U V i := by
        ext a
        exact ConcreteCategory.congr_hom (f.hom.hom.naturality i) a })

lemma forget_map_homOfForget (f : (forget Y Λ).obj F ⟶ (forget Y Λ).obj F') (hadd hsmul) :
    (forget Y Λ).map (homOfForget f hadd hsmul) = f :=
  rfl

lemma forget_map_app (f : F ⟶ F') (U) (a : F.obj.obj.obj U) :
    ((forget Y Λ).map f).hom.hom.app U a = f.hom.hom.app U a :=
  rfl

end Sections

section Stalk

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) [ConnectedSpace Y]
  {F F' F'' : Y.FiniteLocallyConstantModule Λ}

/-- The map on stalks of `Λ`-modules induced by a morphism of the underlying sheaves of sets. -/
noncomputable def stalkFun (f : (forget Y Λ).obj F ⟶ (forget Y Λ).obj F') :
    stalk s F → stalk s F' :=
  fun x ↦ forgetStalkEquiv s F'
    (FiniteLocallyConstant.stalkMap s f ((forgetStalkEquiv s F).symm x))

omit [ConnectedSpace Y] in
lemma stalkFun_map (f : F ⟶ F') (x : stalk s F) :
    stalkFun s ((forget Y Λ).map f) x = stalkMap s f x := by
  rw [stalkFun, forgetStalkEquiv_naturality, Equiv.apply_symm_apply]

omit [ConnectedSpace Y] in
lemma stalkFun_comp (f : (forget Y Λ).obj F ⟶ (forget Y Λ).obj F')
    (f' : (forget Y Λ).obj F' ⟶ (forget Y Λ).obj F'') (x : stalk s F) :
    stalkFun s (f ≫ f') x = stalkFun s f' (stalkFun s f x) := by
  simp [stalkFun, FiniteLocallyConstant.stalkMap_comp]

lemma stalkFun_injective {f f' : (forget Y Λ).obj F ⟶ (forget Y Λ).obj F'}
    (h : ∀ x, stalkFun s f x = stalkFun s f' x) : f = f' :=
  FiniteLocallyConstant.stalkMap_injective s fun y ↦ (forgetStalkEquiv s F').injective (by
    simpa [stalkFun] using h (forgetStalkEquiv s F y))

lemma hom_ext_of_stalkMap {f f' : F ⟶ F'} (h : ∀ x, stalkMap s f x = stalkMap s f' x) :
    f = f' := by
  have h' : (forget Y Λ).map f = (forget Y Λ).map f' :=
    stalkFun_injective s fun x ↦ by rw [stalkFun_map, stalkFun_map, h]
  ext U a
  exact congrArg (fun φ : (forget Y Λ).obj F ⟶ (forget Y Λ).obj F' ↦ φ.hom.hom.app U a) h'

/-- Multiplication by `c : Λ` on a finite locally constant sheaf of `Λ`-modules. -/
noncomputable abbrev smulHom (c : Λ) (F : Y.FiniteLocallyConstantModule Λ) : F ⟶ F :=
  ObjectProperty.homMk (c • 𝟙 F.obj)

omit [Finite Λ] [ConnectedSpace Y] in
lemma stalkMap_smulHom (c : Λ) (x : stalk s F) : stalkMap s (smulHom c F) x = c • x := by
  change (pointSmallEtale s).sheafFiber.map (c • 𝟙 F.obj) x = _
  rw [GrothendieckTopology.Point.sheafFiber_map_smul, CategoryTheory.Functor.map_id]
  rfl

omit [Finite Λ] [ConnectedSpace Y] in
lemma smulHom_app (c : Λ) (U) (a : F.obj.obj.obj U) :
    (smulHom c F).hom.hom.app U a = c • a :=
  rfl

end Stalk

section Double

variable (F : Y.FiniteLocallyConstantModule Λ)

/-- The first projection `F ⊞ F ⟶ F`. -/
noncomputable abbrev doubleFst : double F ⟶ F := ObjectProperty.homMk biprod.fst

/-- The second projection `F ⊞ F ⟶ F`. -/
noncomputable abbrev doubleSnd : double F ⟶ F := ObjectProperty.homMk biprod.snd

/-- The first inclusion `F ⟶ F ⊞ F`. -/
noncomputable abbrev doubleInl : F ⟶ double F := ObjectProperty.homMk biprod.inl

/-- The second inclusion `F ⟶ F ⊞ F`. -/
noncomputable abbrev doubleInr : F ⟶ double F := ObjectProperty.homMk biprod.inr

/-- The addition `F ⊞ F ⟶ F`. -/
noncomputable abbrev doubleAdd : double F ⟶ F := ObjectProperty.homMk (biprod.desc (𝟙 _) (𝟙 _))

omit [Finite Λ] in
lemma doubleInl_fst : doubleInl F ≫ doubleFst F = 𝟙 F := by ext1; simp
omit [Finite Λ] in
lemma doubleInr_fst : doubleInr F ≫ doubleFst F = 0 := by ext1; simp
omit [Finite Λ] in
lemma doubleInl_snd : doubleInl F ≫ doubleSnd F = 0 := by ext1; simp
omit [Finite Λ] in
lemma doubleInr_snd : doubleInr F ≫ doubleSnd F = 𝟙 F := by ext1; simp
omit [Finite Λ] in
lemma doubleInl_add : doubleInl F ≫ doubleAdd F = 𝟙 F := by ext1; simp
omit [Finite Λ] in
lemma doubleInr_add : doubleInr F ≫ doubleAdd F = 𝟙 F := by ext1; simp
omit [Finite Λ] in
lemma doubleAdd_hom : (doubleAdd F).hom = (doubleFst F).hom + (doubleSnd F).hom := by
  simp [biprod.desc_eq]

end Double

section StalkLemmas

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)
  {F F' F'' : Y.FiniteLocallyConstantModule Λ}

omit [Finite Λ] in
lemma stalkMap_comp (f : F ⟶ F') (f' : F' ⟶ F'') (x : stalk s F) :
    stalkMap s (f ≫ f') x = stalkMap s f' (stalkMap s f x) := by
  simp [stalkMap]

omit [Finite Λ] in
lemma stalkMap_id (x : stalk s F) : stalkMap s (𝟙 F) x = x := by
  simp [stalkMap]

omit [Finite Λ] in
lemma stalkMap_add (f f' : F ⟶ F') (x : stalk s F) :
    stalkMap s (f + f') x = stalkMap s f x + stalkMap s f' x := by
  have := (pointSmallEtale s).sheafFiber_additive (A := ModuleCat.{u + 1} Λ)
  change (pointSmallEtale s).sheafFiber.map (f.hom + f'.hom) x = _
  rw [Functor.map_add]
  rfl

omit [Finite Λ] in
lemma stalkMap_zero (x : stalk s F) : stalkMap s (0 : F ⟶ F') x = 0 := by
  have := (pointSmallEtale s).sheafFiber_additive (A := ModuleCat.{u + 1} Λ)
  change (pointSmallEtale s).sheafFiber.map (0 : F.obj ⟶ F'.obj) x = 0
  rw [Functor.map_zero]
  rfl

omit [Finite Λ] in
lemma stalkMap_doubleFst_inl (x : stalk s F) :
    stalkMap s (doubleFst F) (stalkMap s (doubleInl F) x) = x := by
  rw [← stalkMap_comp, doubleInl_fst, stalkMap_id]

omit [Finite Λ] in
lemma stalkMap_doubleFst_inr (x : stalk s F) :
    stalkMap s (doubleFst F) (stalkMap s (doubleInr F) x) = 0 := by
  rw [← stalkMap_comp, doubleInr_fst, stalkMap_zero]

omit [Finite Λ] in
lemma stalkMap_doubleSnd_inl (x : stalk s F) :
    stalkMap s (doubleSnd F) (stalkMap s (doubleInl F) x) = 0 := by
  rw [← stalkMap_comp, doubleInl_snd, stalkMap_zero]

omit [Finite Λ] in
lemma stalkMap_doubleSnd_inr (x : stalk s F) :
    stalkMap s (doubleSnd F) (stalkMap s (doubleInr F) x) = x := by
  rw [← stalkMap_comp, doubleInr_snd, stalkMap_id]

omit [Finite Λ] in
lemma stalkMap_doubleAdd (x : stalk s (double F)) :
    stalkMap s (doubleAdd F) x = stalkMap s (doubleFst F) x + stalkMap s (doubleSnd F) x := by
  have := (pointSmallEtale s).sheafFiber_additive (A := ModuleCat.{u + 1} Λ)
  change (pointSmallEtale s).sheafFiber.map (doubleAdd F).hom x = _
  rw [doubleAdd_hom, Functor.map_add]
  rfl

end StalkLemmas

section Full

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) [ConnectedSpace Y]
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G ((FiniteEtale.fiber s).obj P)] [IsFundamentalGroup (FiniteEtale.fiber s) G]
  {F F' : Y.FiniteLocallyConstantModule Λ}

lemma exists_stalkFun_eq (t : stalk s F → stalk s F')
    (ht : ∀ g x, t (smul s G g x) = smul s G g (t x)) :
    ∃ f : (forget Y Λ).obj F ⟶ (forget Y Λ).obj F', ∀ x, stalkFun s f x = t x := by
  obtain ⟨f, hf⟩ := FiniteLocallyConstant.exists_stalkMap_eq s G
    (fun y ↦ (forgetStalkEquiv s F').symm (t (forgetStalkEquiv s F y))) fun g y ↦ by
      have h := ht g (forgetStalkEquiv s F y)
      simp only [smul, Equiv.symm_apply_apply] at h
      simp only [h, Equiv.symm_apply_apply]
  refine ⟨f, fun x ↦ ?_⟩
  simp [stalkFun, hf]

omit [ConnectedSpace Y] in
lemma sectionMap_comp {F'' : Y.FiniteLocallyConstantModule Λ}
    (f : (forget Y Λ).obj F ⟶ (forget Y Λ).obj F')
    (f' : (forget Y Λ).obj F' ⟶ (forget Y Λ).obj F'') (U) (a : F.obj.obj.obj U) :
    sectionMap (f ≫ f') U a = sectionMap f' U (sectionMap f U a) :=
  rfl

/-- Blueprint `sk-i-real-galois`: the stalk functor is full onto `G`-equivariant maps: every
`Λ`-linear `G`-equivariant map between the stalks of two finite locally constant sheaves of
`Λ`-modules is induced by a morphism of sheaves. -/
theorem exists_stalkMap_eq (t : stalk s F →ₗ[Λ] stalk s F')
    (ht : ∀ g x, t (smul s G g x) = smul s G g (t x)) :
    ∃ f : F ⟶ F', ∀ x, stalkMap s f x = t x := by
  obtain ⟨f₀, hf₀⟩ := exists_stalkFun_eq s G t ht
  have hsmul (U) (c : Λ) (a : F.obj.obj.obj U) :
      sectionMap f₀ U (c • a) = c • sectionMap f₀ U a := by
    have h : (forget Y Λ).map (smulHom c F) ≫ f₀ = f₀ ≫ (forget Y Λ).map (smulHom c F') :=
      stalkFun_injective s fun x ↦ by
        rw [stalkFun_comp, stalkFun_comp, stalkFun_map, stalkFun_map, hf₀, hf₀,
          stalkMap_smulHom, stalkMap_smulHom, map_smul]
    exact congrArg (fun φ : (forget Y Λ).obj F ⟶ (forget Y Λ).obj F' ↦ sectionMap φ U a) h
  let T : stalk s (double F) → stalk s (double F') := fun w ↦
    stalkMap s (doubleInl F') (t (stalkMap s (doubleFst F) w)) +
      stalkMap s (doubleInr F') (t (stalkMap s (doubleSnd F) w))
  obtain ⟨f₁, hf₁⟩ := exists_stalkFun_eq s G T fun g w ↦ by
    simp only [T, stalkMap_smul, ht, smul_add]
  have h₁ : f₁ ≫ (forget Y Λ).map (doubleFst F') = (forget Y Λ).map (doubleFst F) ≫ f₀ :=
    stalkFun_injective s fun w ↦ by
      rw [stalkFun_comp, stalkFun_comp, stalkFun_map, stalkFun_map, hf₁, hf₀]
      simp only [T, map_add, stalkMap_doubleFst_inl, stalkMap_doubleFst_inr, add_zero]
  have h₂ : f₁ ≫ (forget Y Λ).map (doubleSnd F') = (forget Y Λ).map (doubleSnd F) ≫ f₀ :=
    stalkFun_injective s fun w ↦ by
      rw [stalkFun_comp, stalkFun_comp, stalkFun_map, stalkFun_map, hf₁, hf₀]
      simp only [T, map_add, stalkMap_doubleSnd_inl, stalkMap_doubleSnd_inr, zero_add]
  have h₃ : (forget Y Λ).map (doubleAdd F) ≫ f₀ = f₁ ≫ (forget Y Λ).map (doubleAdd F') :=
    stalkFun_injective s fun w ↦ by
      rw [stalkFun_comp, stalkFun_comp, stalkFun_map, stalkFun_map, hf₁, hf₀,
        stalkMap_doubleAdd, stalkMap_doubleAdd]
      simp only [T, map_add, stalkMap_doubleFst_inl, stalkMap_doubleFst_inr,
        stalkMap_doubleSnd_inl, stalkMap_doubleSnd_inr, add_zero, zero_add]
  have hadd (U) (a b : F.obj.obj.obj U) :
      sectionMap f₀ U (a + b) = sectionMap f₀ U a + sectionMap f₀ U b := by
    let x : (double F).obj.obj.obj U :=
      (doubleInl F).hom.hom.app U a + (doubleInr F).hom.hom.app U b
    have sec {A B : Y.FiniteLocallyConstantModule Λ} {φ ψ : A ⟶ B} (h : φ = ψ)
        (y : A.obj.obj.obj U) : φ.hom.hom.app U y = ψ.hom.hom.app U y := by rw [h]
    have hab : (doubleAdd F).hom.hom.app U x = a + b := by
      simp only [x, map_add]
      have e₁ := sec (doubleInl_add F) a
      have e₂ := sec (doubleInr_add F) b
      exact congrArg₂ (· + ·) e₁ e₂
    have hfst : (doubleFst F).hom.hom.app U x = a := by
      have e₁ := sec (doubleInl_fst F) a
      have e₂ := sec (doubleInr_fst F) b
      simp only [x, map_add]
      exact (congrArg₂ (· + ·) e₁ e₂).trans (add_zero a)
    have hsnd : (doubleSnd F).hom.hom.app U x = b := by
      have e₁ := sec (doubleInl_snd F) a
      have e₂ := sec (doubleInr_snd F) b
      simp only [x, map_add]
      exact (congrArg₂ (· + ·) e₁ e₂).trans (zero_add b)
    have k₁ := congrArg (fun φ : (forget Y Λ).obj (double F) ⟶ (forget Y Λ).obj F' ↦
      sectionMap φ U x) h₁
    have k₂ := congrArg (fun φ : (forget Y Λ).obj (double F) ⟶ (forget Y Λ).obj F' ↦
      sectionMap φ U x) h₂
    have k₃ := congrArg (fun φ : (forget Y Λ).obj (double F) ⟶ (forget Y Λ).obj F' ↦
      sectionMap φ U x) h₃
    simp only [sectionMap_comp] at k₁ k₂ k₃
    have hadd' : (doubleAdd F').hom.hom.app U (sectionMap f₁ U x) =
        (doubleFst F').hom.hom.app U (sectionMap f₁ U x) +
          (doubleSnd F').hom.hom.app U (sectionMap f₁ U x) := by
      rw [doubleAdd_hom]
      rfl
    rw [← hab]
    refine k₃.trans (hadd'.trans ?_)
    rw [← hfst, ← hsnd]
    exact congrArg₂ (· + ·) k₁ k₂
  exact ⟨homOfForget f₀ hadd hsmul, fun x ↦ by rw [← stalkFun_map, forget_map_homOfForget, hf₀]⟩

end Full

end AlgebraicGeometry.Scheme.FiniteLocallyConstantModule
