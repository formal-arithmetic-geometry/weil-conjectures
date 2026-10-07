/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.PicardFunctor
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import WeilConjectures.Mathlib.Algebra.Category.Grp.Adjunctions
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Invertible modules and `𝒪ˣ`-torsors on the Zariski site

For a scheme `X`, invertible `𝒪_X`-modules up to isomorphism are in bijection with torsors under
the sheaf `𝒪_Xˣ` of units on the Zariski site, up to isomorphism.

## Main definitions

- `AlgebraicGeometry.Scheme.unitsSheaf`: the sheaf `𝒪_Xˣ` of units on the Zariski site.
- `AlgebraicGeometry.Scheme.Modules.IsGenerator`: a section `s` of `M` over `U` is a generator
  if `a ↦ a • s` is a bijection `𝒪 ≅ M` over `U`.
- `AlgebraicGeometry.Scheme.Modules.generatorsTorsor`: for `M` invertible, the `𝒪_Xˣ`-torsor
  `Isom(𝒪_X, M)` of local generators of `M`.

## Main statements

- `AlgebraicGeometry.Scheme.nonempty_pic_equiv_quotient_torsor_unitsSheaf`: the map
  `M ↦ Isom(𝒪_X, M)` is a bijection from `Pic(X)` to the isomorphism classes of
  `𝒪_Xˣ`-torsors.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The sheaf `𝒪_Xˣ` of units of the structure sheaf on the Zariski site of `X`, written
additively. It is a sheaf because the functor of units preserves limits. -/
noncomputable def unitsSheaf : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  ⟨X.sheaf.obj ⋙ CommRingCat.unitsAddCommGrp,
    Presheaf.isSheaf_comp_of_isSheaf _ _ _ X.sheaf.property⟩

variable {X}

/-- A section of `𝒪_Xˣ`, as a unit of the ring of sections. -/
abbrev unitsSheaf.toUnits {U : X.Opensᵒᵖ} (g : X.unitsSheaf.obj.obj U) : Γ(X, U.unop)ˣ :=
  Additive.toMul g

/-- A unit of the ring of sections, as a section of `𝒪_Xˣ`. -/
abbrev unitsSheaf.ofUnits {U : X.Opensᵒᵖ} (g : Γ(X, U.unop)ˣ) : X.unitsSheaf.obj.obj U :=
  Additive.ofMul g

lemma unitsSheaf.val_toUnits_map {U V : X.Opensᵒᵖ} (f : U ⟶ V) (g : X.unitsSheaf.obj.obj U) :
    (toUnits (X.unitsSheaf.obj.map f g) : Γ(X, V.unop)) = X.presheaf.map f (toUnits g) :=
  rfl

/-- The structure sheaf of `X`, as a sheaf of types. -/
lemma isSheaf_presheaf_comp_forget :
    Presieve.IsSheaf (Opens.grothendieckTopology X)
      (X.presheaf ⋙ CategoryTheory.forget CommRingCat) :=
  (isSheaf_iff_isSheaf_of_type _ _).1
    ((sheafCompose _ (CategoryTheory.forget CommRingCat)).obj X.sheaf).property

namespace Modules

variable (M : X.Modules)

/-- The underlying sheaf of types of a sheaf of modules. -/
lemma isSheaf_presheaf_comp_forget :
    Presieve.IsSheaf (Opens.grothendieckTopology X)
      (M.presheaf ⋙ CategoryTheory.forget AddCommGrpCat) :=
  (isSheaf_iff_isSheaf_of_type _ _).1
    ((sheafCompose (Opens.grothendieckTopology X) (CategoryTheory.forget AddCommGrpCat.{u})).obj
      ⟨M.presheaf, M.isSheaf⟩).property

/-- A section `s` of `M` over `U` is a *generator* if for every open `V ⊆ U` the map
`Γ(X, V) → Γ(M, V)`, `a ↦ a • s|_V` is bijective, i.e. if `s` trivialises `M` over `U`. -/
def IsGenerator {U : X.Opens} (s : Γ(M, U)) : Prop :=
  ∀ ⦃V : X.Opens⦄ (i : V ⟶ U), Function.Bijective fun a : Γ(X, V) ↦ a • M.presheaf.map i.op s

variable {M}

lemma map_map_apply {U V W : X.Opens} (i : V ⟶ U) (j : W ⟶ V) (s : Γ(M, U)) :
    M.presheaf.map j.op (M.presheaf.map i.op s) = M.presheaf.map (j ≫ i).op s := by
  rw [op_comp, Functor.map_comp]
  rfl

lemma map_id_apply {U : X.Opens} (s : Γ(M, U)) : M.presheaf.map (𝟙 U).op s = s := by
  simp

lemma _root_.AlgebraicGeometry.Scheme.map_map_apply' {U V W : X.Opens} (i : V ⟶ U)
    (j : W ⟶ V) (a : Γ(X, U)) :
    X.presheaf.map j.op (X.presheaf.map i.op a) = X.presheaf.map (j ≫ i).op a := by
  rw [op_comp, Functor.map_comp]
  rfl

namespace IsGenerator

variable {U : X.Opens} {s : Γ(M, U)} (hs : M.IsGenerator s)
include hs

lemma bijective : Function.Bijective fun a : Γ(X, U) ↦ a • s := by
  simpa only [map_id_apply] using hs (𝟙 U)

lemma map {V : X.Opens} (i : V ⟶ U) : M.IsGenerator (M.presheaf.map i.op s) := by
  intro W j
  simpa only [map_map_apply] using hs (j ≫ i)

/-- The coefficient of a section `m` with respect to a generator `s`: the unique `a` with
`a • s = m`. -/
noncomputable def coeff (m : Γ(M, U)) : Γ(X, U) :=
  Function.surjInv hs.bijective.2 m

@[simp]
lemma coeff_smul (m : Γ(M, U)) : hs.coeff m • s = m :=
  Function.surjInv_eq hs.bijective.2 m

lemma coeff_eq_iff (m : Γ(M, U)) (a : Γ(X, U)) : hs.coeff m = a ↔ a • s = m :=
  ⟨fun h ↦ h ▸ hs.coeff_smul m, fun h ↦ hs.bijective.1 ((hs.coeff_smul m).trans h.symm)⟩

@[simp]
lemma coeff_smul_self (a : Γ(X, U)) : hs.coeff (a • s) = a :=
  (hs.coeff_eq_iff _ _).2 rfl

lemma smul_left_injective {a b : Γ(X, U)} (h : a • s = b • s) : a = b :=
  hs.bijective.1 h

lemma units_smul (g : Γ(X, U)ˣ) : M.IsGenerator ((g : Γ(X, U)) • s) := by
  intro V i
  have : (fun a : Γ(X, V) ↦ a • M.presheaf.map i.op ((g : Γ(X, U)) • s)) =
      (fun a : Γ(X, V) ↦ a • M.presheaf.map i.op s) ∘
        (fun a ↦ a * X.presheaf.map i.op (g : Γ(X, U))) := by
    ext a
    simp [mul_smul]
  rw [this]
  refine (hs i).comp ?_
  exact (Units.map (X.presheaf.map i.op).hom.toMonoidHom g).mulRight_bijective

@[simp]
lemma coeff_add (m m' : Γ(M, U)) : hs.coeff (m + m') = hs.coeff m + hs.coeff m' := by
  rw [coeff_eq_iff, add_smul, coeff_smul, coeff_smul]

@[simp]
lemma coeff_zero : hs.coeff 0 = 0 := by
  rw [coeff_eq_iff, zero_smul]

@[simp]
lemma coeff_smul_left (a : Γ(X, U)) (m : Γ(M, U)) : hs.coeff (a • m) = a * hs.coeff m := by
  rw [coeff_eq_iff, mul_smul, coeff_smul]

lemma coeff_map {V : X.Opens} (i : V ⟶ U) (m : Γ(M, U)) :
    (hs.map i).coeff (M.presheaf.map i.op m) = X.presheaf.map i.op (hs.coeff m) := by
  rw [coeff_eq_iff, ← map_smul, coeff_smul]

end IsGenerator

/-- Being a generator is a local property. -/
lemma isGenerator_of_mem {U : X.Opens} (s : Γ(M, U)) {S : Sieve U}
    (hS : S ∈ Opens.grothendieckTopology X U)
    (h : ∀ ⦃V : X.Opens⦄ (i : V ⟶ U), S i → M.IsGenerator (M.presheaf.map i.op s)) :
    M.IsGenerator s := by
  intro W j
  have hS' := (Opens.grothendieckTopology X).pullback_stable j hS
  have hO := Scheme.isSheaf_presheaf_comp_forget (X := X) _ hS'
  have hM := Modules.isSheaf_presheaf_comp_forget M _ hS'
  refine ⟨fun a b hab ↦ ?_, fun m ↦ ?_⟩
  · refine hO.isSeparatedFor.ext fun V f hf ↦ ?_
    have hg := h (f ≫ j) hf
    refine hg.smul_left_injective ?_
    have := congr_arg (M.presheaf.map f.op) hab
    simp only [map_smul, map_map_apply] at this
    exact this
  · let x : Presieve.FamilyOfElements (X.presheaf ⋙ CategoryTheory.forget CommRingCat)
        (S.pullback j).arrows := fun V f hf ↦ (h (f ≫ j) hf).coeff (M.presheaf.map f.op m)
    have hx : x.Compatible := by
      intro Z₁ Z₂ V g₁ g₂ f₁ f₂ hf₁ hf₂ hcomm
      change X.presheaf.map g₁.op (x f₁ hf₁) = X.presheaf.map g₂.op (x f₂ hf₂)
      simp only [x]
      rw [← IsGenerator.coeff_map, ← IsGenerator.coeff_map]
      simp only [map_map_apply]
      congr 2
    refine ⟨hO.amalgamate x hx, ?_⟩
    refine hM.isSeparatedFor.ext fun V f hf ↦ ?_
    change M.presheaf.map f.op (_ • _) = _
    rw [map_smul, map_map_apply]
    have := hO.valid_glue hx f hf
    change X.presheaf.map f.op _ = _ at this
    rw [this]
    simp only [x]
    exact (h (f ≫ j) hf).coeff_smul _

/-- If `M` is isomorphic to `𝒪` over `Y`, the section of `M` corresponding to `1` is a
generator. -/
lemma isGenerator_of_iso {Y : X.Opens}
    (e : M.over Y ≅ SheafOfModules.unit (X.ringCatSheaf.over Y)) :
    M.IsGenerator
      (show Γ(M, Y) from e.inv.val.app (op (Over.mk (𝟙 Y))) (1 : Γ(X, Y))) := by
  intro W i
  let E := sectionsLinearEquivOfOverIsoUnit e (leOfHom i)
  have key : M.presheaf.map i.op (show Γ(M, Y) from e.inv.val.app (op (Over.mk (𝟙 Y))) (1 : Γ(X, Y))) =
      E.symm 1 := by
    have := PresheafOfModules.naturality_apply e.inv.val
      (Over.homMk i : Over.mk (homOfLE (leOfHom i)) ⟶ Over.mk (𝟙 Y)).op (1 : Γ(X, Y))
    refine this.symm.trans (congr_arg _ ?_)
    exact map_one ((X.ringCatSheaf.over Y).obj.map _).hom
  rw [key]
  have : (fun a : Γ(X, W) ↦ a • E.symm 1) = E.symm := by
    ext a
    rw [← LinearEquiv.map_smul, smul_eq_mul, mul_one]
  rw [this]
  exact E.symm.bijective

variable (M) in
/-- An invertible module has a generator near every point. -/
lemma exists_isGenerator [M.IsInvertible] (x : X) :
    ∃ (Y : X.Opens) (s : Γ(M, Y)), x ∈ Y ∧ M.IsGenerator s := by
  obtain ⟨Y, hxY, ⟨e⟩⟩ := M.exists_mem_over_iso_unit x
  exact ⟨Y, _, hxY, isGenerator_of_iso e⟩

variable (M) in
/-- The subpresheaf of `M` of generators. -/
def generatorsSubfunctor : Subfunctor (M.presheaf ⋙ CategoryTheory.forget AddCommGrpCat) where
  obj U := {s | M.IsGenerator (U := U.unop) s}
  map {_ _} i _ hs := hs.map i.unop

lemma isSheaf_generatorsSubfunctor :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (generatorsSubfunctor M).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type, Subfunctor.isSheaf_iff _ (isSheaf_presheaf_comp_forget M)]
  intro U s hs
  exact isGenerator_of_mem (U := U.unop) s hs fun _ _ hi ↦ hi

variable (M) in
/-- The `𝒪_Xˣ`-torsor `Isom(𝒪_X, M)` of an invertible module `M`: its sections over `U` are the
generators of `M` over `U`, on which the units act by multiplication. -/
noncomputable def generatorsTorsor [M.IsInvertible] : Sheaf.Torsor X.unitsSheaf where
  sheaf := ⟨(generatorsSubfunctor M).toFunctor, isSheaf_generatorsSubfunctor⟩
  vadd U g s := ⟨((unitsSheaf.toUnits g : Γ(X, U.unop)ˣ) : Γ(X, U.unop)) •
    (show Γ(M, U.unop) from s.1), IsGenerator.units_smul s.2 _⟩
  zero_vadd U s := Subtype.ext (one_smul _ (show Γ(M, U.unop) from s.1))
  add_vadd U g h s := Subtype.ext (mul_smul _ _ (show Γ(M, U.unop) from s.1))
  map_vadd f g s := Subtype.ext (map_smul M f.unop _ (show Γ(M, _) from s.1))
  bijective_vadd U t := by
    refine ⟨fun g₁ g₂ h ↦ ?_, fun s ↦ ?_⟩
    · have := t.2.smul_left_injective (congr_arg Subtype.val h)
      exact Additive.toMul.injective (Units.ext this)
    · have ht : M.IsGenerator (show Γ(M, U.unop) from t.1) := t.2
      have hs : M.IsGenerator (show Γ(M, U.unop) from s.1) := s.2
      have hab : hs.coeff t.1 * ht.coeff s.1 = 1 := by
        refine ht.smul_left_injective ?_
        rw [mul_smul, ht.coeff_smul, hs.coeff_smul, one_smul]
      refine ⟨unitsSheaf.ofUnits ⟨ht.coeff s.1, hs.coeff t.1, by rw [mul_comm, hab], hab⟩,
        Subtype.ext ?_⟩
      exact ht.coeff_smul _
  nonemptySieve_mem U := by
    intro x hx
    obtain ⟨Y, s, hxY, hs⟩ := M.exists_isGenerator x
    exact ⟨U ⊓ Y, homOfLE inf_le_left, ⟨⟨_, hs.map (homOfLE inf_le_right)⟩⟩, ⟨hx, hxY⟩⟩

lemma IsGenerator.of_iso {N : X.Modules} (e : M ≅ N) {U : X.Opens} {s : Γ(M, U)}
    (hs : M.IsGenerator s) : N.IsGenerator (e.hom.app U s) := by
  intro V i
  have : (fun a : Γ(X, V) ↦ a • N.presheaf.map i.op (e.hom.app U s)) =
      e.hom.app V ∘ fun a : Γ(X, V) ↦ a • M.presheaf.map i.op s := by
    ext a
    simp only [Function.comp_apply, Hom.app_smul]
    congr 1
    exact (PresheafOfModules.naturality_apply e.hom.val i.op s).symm
  rw [this]
  refine Function.Bijective.comp ?_ (hs i)
  exact ((CategoryTheory.forget AddCommGrpCat).mapIso
    ((toPresheaf X).mapIso e |>.app (op V))).toEquiv.bijective

/-- Isomorphic invertible modules have isomorphic torsors of generators. -/
lemma generatorsTorsor_equiv_of_iso {N : X.Modules} [M.IsInvertible] [N.IsInvertible]
    (e : M ≅ N) : M.generatorsTorsor ≈ N.generatorsTorsor := by
  refine ⟨Sheaf.Torsor.Iso.ofHom (ObjectProperty.homMk
    { app U := TypeCat.ofHom fun s ↦ ⟨e.hom.app U.unop s.1, IsGenerator.of_iso e s.2⟩
      naturality U V f := ?_ }) fun U a s ↦ Subtype.ext ?_⟩
  · ext s
    apply Subtype.ext
    change e.hom.val.app V (M.val.map f s.1) = N.val.map f (e.hom.val.app U s.1)
    exact PresheafOfModules.naturality_apply e.hom.val f s.1
  · exact Hom.app_smul e.hom _ _

/-- A generator `s` of `M` over `Y` trivialises `M` over `Y`: `a ↦ a • s` is an isomorphism
`𝒪_Y ≅ M|_Y`. -/
noncomputable def IsGenerator.overIso {Y : X.Opens} {s : Γ(M, Y)} (hs : M.IsGenerator s) :
    M.over Y ≅ SheafOfModules.unit (X.ringCatSheaf.over Y) :=
  let σ : (M.over Y).sections := PresheafOfModules.sectionsMk
    (fun W ↦ show Γ(M, W.unop.left) from M.presheaf.map W.unop.hom.op s)
    (fun W W' f ↦ by
      change M.presheaf.map f.unop.left.op (M.presheaf.map W.unop.hom.op s) = _
      rw [map_map_apply]
      rfl)
  let φ := (M.over Y).unitHomEquiv.symm σ
  have : IsIso φ := by
    have : IsIso ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map φ) := by
      refine (NatTrans.isIso_iff_isIso_app _).2 fun W ↦ ?_
      rw [ConcreteCategory.isIso_iff_bijective]
      exact hs W.unop.hom
    exact isIso_of_reflects_iso φ (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)
  (asIso φ).symm

section OfUnitsTorsor

variable (T : Sheaf.Torsor X.unitsSheaf)

lemma _root_.AlgebraicGeometry.Scheme.torsor_map_map {U V W : X.Opens} (i : V ⟶ U) (j : W ⟶ V)
    (t : T.sheaf.obj.obj (op U)) :
    T.sheaf.obj.map j.op (T.sheaf.obj.map i.op t) = T.sheaf.obj.map (j ≫ i).op t := by
  rw [op_comp, Functor.map_comp]
  rfl

/-- The sections over `U` of the invertible module `L(T)` of an `𝒪_Xˣ`-torsor `T`: families of
maps `f_V : T(V) → Γ(X, V)` for the opens `V ⊆ U`, compatible with restriction and satisfying
`f_V (g • t) = g⁻¹ f_V t`. They are the `𝒪ˣ`-equivariant maps `T|_U → 𝒪|_U` for the twisted
action, i.e. `L(T) = (T × 𝒪) / 𝒪ˣ`. -/
def unitsTorsorSections (U : X.Opens) :
    AddSubgroup (∀ V : X.Opens, (V ⟶ U) → T.sheaf.obj.obj (op V) → Γ(X, V)) where
  carrier := {f | (∀ ⦃V W : X.Opens⦄ (i : V ⟶ U) (j : W ⟶ V) (t : T.sheaf.obj.obj (op V)),
      f W (j ≫ i) (T.sheaf.obj.map j.op t) = X.presheaf.map j.op (f V i t)) ∧
    ∀ ⦃V : X.Opens⦄ (i : V ⟶ U) (g : X.unitsSheaf.obj.obj (op V)) (t : T.sheaf.obj.obj (op V)),
      f V i (T.vadd (op V) g t) = ((unitsSheaf.toUnits g)⁻¹ : Γ(X, V)ˣ) * f V i t}
  add_mem' {f f'} hf hf' := ⟨fun V W i j t ↦ by simp [hf.1, hf'.1],
    fun V i g t ↦ by simp [hf.2, hf'.2, mul_add]⟩
  zero_mem' := ⟨fun _ _ _ _ _ ↦ by simp, fun _ _ _ _ ↦ by simp⟩
  neg_mem' {f} hf := ⟨fun V W i j t ↦ by simp [hf.1], fun V i g t ↦ by simp [hf.2]⟩

variable {T}

@[ext]
lemma unitsTorsorSections.ext {U : X.Opens} {f f' : unitsTorsorSections T U}
    (h : ∀ (V : X.Opens) (i : V ⟶ U) (t : T.sheaf.obj.obj (op V)), f.1 V i t = f'.1 V i t) :
    f = f' :=
  Subtype.ext (funext fun V ↦ funext fun i ↦ funext fun t ↦ h V i t)

lemma unitsTorsorSections.map_apply {U V W : X.Opens} (f : unitsTorsorSections T U)
    (i : V ⟶ U) (j : W ⟶ V) (t : T.sheaf.obj.obj (op V)) :
    f.1 W (j ≫ i) (T.sheaf.obj.map j.op t) = X.presheaf.map j.op (f.1 V i t) :=
  f.2.1 i j t

lemma unitsTorsorSections.vadd_apply {U V : X.Opens} (f : unitsTorsorSections T U)
    (i : V ⟶ U) (g : X.unitsSheaf.obj.obj (op V)) (t : T.sheaf.obj.obj (op V)) :
    f.1 V i (T.vadd (op V) g t) = ((unitsSheaf.toUnits g)⁻¹ : Γ(X, V)ˣ) * f.1 V i t :=
  f.2.2 i g t

instance (U : X.Opens) : SMul Γ(X, U) (unitsTorsorSections T U) where
  smul a f := ⟨fun V i t ↦ X.presheaf.map i.op a * f.1 V i t,
    fun V W i j t ↦ by
      dsimp only
      rw [unitsTorsorSections.map_apply f, map_mul, map_map_apply'],
    fun V i g t ↦ by
      dsimp only
      rw [unitsTorsorSections.vadd_apply f, mul_left_comm]⟩

@[simp]
lemma unitsTorsorSections.smul_apply {U V : X.Opens} (a : Γ(X, U)) (f : unitsTorsorSections T U)
    (i : V ⟶ U) (t : T.sheaf.obj.obj (op V)) :
    (a • f).1 V i t = X.presheaf.map i.op a * f.1 V i t :=
  rfl

@[simp]
lemma unitsTorsorSections.add_apply {U V : X.Opens} (f f' : unitsTorsorSections T U)
    (i : V ⟶ U) (t : T.sheaf.obj.obj (op V)) :
    (f + f').1 V i t = f.1 V i t + f'.1 V i t :=
  rfl

@[simp]
lemma unitsTorsorSections.zero_apply {U V : X.Opens} (i : V ⟶ U) (t : T.sheaf.obj.obj (op V)) :
    (0 : unitsTorsorSections T U).1 V i t = 0 :=
  rfl

instance (U : X.Opens) : Module Γ(X, U) (unitsTorsorSections T U) where
  one_smul f := by ext; simp
  mul_smul a b f := by ext; simp [mul_assoc]
  smul_zero a := by ext; simp
  smul_add a f f' := by ext; simp [mul_add]
  add_smul a b f := by ext; simp [add_mul]
  zero_smul f := by ext; simp

variable (T) in
/-- The presheaf of abelian groups underlying the invertible module `L(T)` of an
`𝒪_Xˣ`-torsor `T`. -/
noncomputable def unitsTorsorPresheaf : X.Opensᵒᵖ ⥤ Ab.{u} where
  obj U := AddCommGrpCat.of (unitsTorsorSections T U.unop)
  map {_ _} i := AddCommGrpCat.ofHom
    { toFun f := ⟨fun V j t ↦ f.1 V (j ≫ i.unop) t,
        fun _ _ j k t ↦ unitsTorsorSections.map_apply f (j ≫ i.unop) k t,
        fun _ j g t ↦ unitsTorsorSections.vadd_apply f (j ≫ i.unop) g t⟩
      map_zero' := rfl
      map_add' _ _ := rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

instance (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) ((unitsTorsorPresheaf T).obj U) :=
  inferInstanceAs (Module Γ(X, U.unop) (unitsTorsorSections T U.unop))

lemma unitsTorsorPresheaf_map_apply {U U' : X.Opensᵒᵖ} (i : U ⟶ U')
    (f : unitsTorsorSections T U.unop) {V : X.Opens} (j : V ⟶ U'.unop)
    (t : T.sheaf.obj.obj (op V)) :
    ((unitsTorsorPresheaf T).map i f).1 V j t = f.1 V (j ≫ i.unop) t :=
  rfl

lemma unitsTorsorPresheaf_map_smul {U U' : X.Opensᵒᵖ} (i : U ⟶ U')
    (a : X.ringCatSheaf.obj.obj U) (f : (unitsTorsorPresheaf T).obj U) :
    (unitsTorsorPresheaf T).map i (a • f) =
      X.ringCatSheaf.obj.map i a • (unitsTorsorPresheaf T).map i f := by
  refine unitsTorsorSections.ext fun V j t ↦ ?_
  change X.presheaf.map (j ≫ i.unop).op a * _ = X.presheaf.map j.op (X.presheaf.map i a) * _
  rw [← map_map_apply' i.unop j]
  rfl

/-- Two sections of the structure sheaf over `W` agree if they agree on a covering sieve. -/
lemma _root_.AlgebraicGeometry.Scheme.ext_of_mem {W : X.Opens} {S : Sieve W}
    (hS : S ∈ Opens.grothendieckTopology X W) {a b : Γ(X, W)}
    (h : ∀ ⦃Z : X.Opens⦄ (l : Z ⟶ W), S l → X.presheaf.map l.op a = X.presheaf.map l.op b) :
    a = b :=
  (Scheme.isSheaf_presheaf_comp_forget _ hS).isSeparatedFor.ext h

lemma isSheaf_unitsTorsorPresheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (unitsTorsorPresheaf T) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget Ab.{u}),
    isSheaf_iff_isSheaf_of_type]
  intro U S hS x hx
  -- the glued values: over `W ⊆ U`, glue the values of the `x` along `S`
  have hy (W : X.Opens) (k : W ⟶ U) (t : T.sheaf.obj.obj (op W)) :
      (Presieve.FamilyOfElements.Compatible (P := X.presheaf ⋙ CategoryTheory.forget CommRingCat)
        (R := (S.pullback k).arrows)
        fun Z l hl ↦ (x (l ≫ k) hl).1 Z (𝟙 Z) (T.sheaf.obj.map l.op t)) := by
    intro Z₁ Z₂ Z' m₁ m₂ l₁ l₂ hl₁ hl₂ hcomm
    change X.presheaf.map m₁.op ((x (l₁ ≫ k) hl₁).1 Z₁ (𝟙 Z₁) _) =
      X.presheaf.map m₂.op ((x (l₂ ≫ k) hl₂).1 Z₂ (𝟙 Z₂) _)
    rw [← unitsTorsorSections.map_apply, ← unitsTorsorSections.map_apply, torsor_map_map,
      torsor_map_map, hcomm]
    have := congr_arg (fun f : (unitsTorsorPresheaf T).obj (op Z') ↦
      f.1 Z' (𝟙 Z') (T.sheaf.obj.map (m₂ ≫ l₂).op t))
      (hx m₁ m₂ hl₁ hl₂ (by rw [← Category.assoc, hcomm, Category.assoc]))
    exact this
  have hO (W : X.Opens) (k : W ⟶ U) := Scheme.isSheaf_presheaf_comp_forget _
    ((Opens.grothendieckTopology X).pullback_stable k hS)
  let F : ∀ V : X.Opens, (V ⟶ U) → T.sheaf.obj.obj (op V) → Γ(X, V) :=
    fun W k t ↦ (hO W k).amalgamate _ (hy W k t)
  have hF (W : X.Opens) (k : W ⟶ U) (t : T.sheaf.obj.obj (op W)) ⦃Z : X.Opens⦄ (l : Z ⟶ W)
      (hl : S (l ≫ k)) :
      X.presheaf.map l.op (F W k t) = (x (l ≫ k) hl).1 Z (𝟙 Z) (T.sheaf.obj.map l.op t) :=
    (hO W k).valid_glue (hy W k t) l hl
  have hFmem : F ∈ unitsTorsorSections T U := by
    refine ⟨fun V W i j t ↦ ?_, fun V i g t ↦ ?_⟩
    · refine ext_of_mem ((Opens.grothendieckTopology X).pullback_stable (j ≫ i) hS)
        fun Z l hl ↦ ?_
      rw [hF W (j ≫ i) _ l hl, map_map_apply', hF V i t (l ≫ j) (by simpa using hl),
        torsor_map_map]
      rfl
    · refine ext_of_mem ((Opens.grothendieckTopology X).pullback_stable i hS)
        fun Z l hl ↦ ?_
      rw [hF V i _ l hl, map_mul, hF V i t l hl, T.map_vadd, unitsTorsorSections.vadd_apply]
      congr 1
  refine ⟨⟨F, hFmem⟩, fun V i hi ↦ ?_, fun f hf ↦ ?_⟩
  · refine unitsTorsorSections.ext fun W j t ↦ ?_
    change F W (j ≫ i) t = _
    refine ext_of_mem ((Opens.grothendieckTopology X).pullback_stable (j ≫ i) hS)
      fun Z l hl ↦ ?_
    rw [hF W (j ≫ i) t l hl, ← unitsTorsorSections.map_apply]
    have := congr_arg (fun f : (unitsTorsorPresheaf T).obj (op Z) ↦
      f.1 Z (𝟙 Z) (T.sheaf.obj.map l.op t))
      (hx (𝟙 Z) (l ≫ j) hl hi (by simp))
    exact this
  · refine unitsTorsorSections.ext fun W k t ↦ ?_
    change f.1 W k t = F W k t
    refine ext_of_mem ((Opens.grothendieckTopology X).pullback_stable k hS)
      fun Z l hl ↦ ?_
    rw [hF W k t l hl, ← unitsTorsorSections.map_apply, ← hf (l ≫ k) hl]
    rfl

variable (T) in
/-- The invertible `𝒪_X`-module `L(T) = (T × 𝒪_X) / 𝒪_Xˣ` of an `𝒪_Xˣ`-torsor `T`, realised as
the sheaf of `𝒪ˣ`-equivariant maps `T → 𝒪` for the action `g • a = g⁻¹ a` on `𝒪`. -/
noncomputable def ofUnitsTorsor : X.Modules where
  val := PresheafOfModules.ofPresheaf (unitsTorsorPresheaf T)
    fun _ _ i a f ↦ unitsTorsorPresheaf_map_smul i a f
  isSheaf := isSheaf_unitsTorsorPresheaf

@[simp]
lemma ofUnitsTorsor_smul_apply {U V : X.Opens} (a : Γ(X, U)) (f : Γ(ofUnitsTorsor T, U))
    (i : V ⟶ U) (t : T.sheaf.obj.obj (op V)) :
    (show unitsTorsorSections T U from a • f).1 V i t =
      X.presheaf.map i.op a * (show unitsTorsorSections T U from f).1 V i t :=
  rfl

lemma ofUnitsTorsor_map_apply {U U' V : X.Opens} (j : U' ⟶ U) (f : Γ(ofUnitsTorsor T, U))
    (i : V ⟶ U') (t : T.sheaf.obj.obj (op V)) :
    (show unitsTorsorSections T U' from (ofUnitsTorsor T).presheaf.map j.op f).1 V i t =
      (show unitsTorsorSections T U from f).1 V (i ≫ j) t :=
  rfl

lemma _root_.AlgebraicGeometry.Scheme.unitsSheaf.val_toUnits_inv_map {U V : X.Opens}
    (i : V ⟶ U) (g : X.unitsSheaf.obj.obj (op U)) :
    (((unitsSheaf.toUnits (X.unitsSheaf.obj.map i.op g))⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) =
      X.presheaf.map i.op ((unitsSheaf.toUnits g)⁻¹ : Γ(X, U)ˣ) :=
  rfl

variable (T) in
/-- The section `f_t` of `L(T)` over `U` attached to a section `t` of `T` over `U`: it sends
`g • t` to `g⁻¹`. -/
noncomputable def unitsTorsorBasis {U : X.Opens} (t : T.sheaf.obj.obj (op U)) :
    Γ(ofUnitsTorsor T, U) :=
  show unitsTorsorSections T U from
  ⟨fun V i s ↦ ((unitsSheaf.toUnits (T.sub (T.sheaf.obj.map i.op t) s))⁻¹ : Γ(X, V)ˣ),
    fun V W i j s ↦ by
      dsimp only
      rw [← torsor_map_map, ← T.map_sub_apply, ← unitsSheaf.val_toUnits_inv_map],
    fun V i g s ↦ by
      dsimp only
      rw [T.sub_vadd_right]
      change (((unitsSheaf.toUnits g *
        unitsSheaf.toUnits (T.sub (T.sheaf.obj.map i.op t) s))⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) = _
      rw [mul_inv, Units.val_mul]⟩

lemma unitsTorsorBasis_apply {U V : X.Opens} (t : T.sheaf.obj.obj (op U)) (i : V ⟶ U)
    (s : T.sheaf.obj.obj (op V)) :
    (show unitsTorsorSections T U from unitsTorsorBasis T t).1 V i s =
      ((unitsSheaf.toUnits (T.sub (T.sheaf.obj.map i.op t) s))⁻¹ : Γ(X, V)ˣ) :=
  rfl

lemma map_unitsTorsorBasis {U V : X.Opens} (t : T.sheaf.obj.obj (op U)) (j : V ⟶ U) :
    (ofUnitsTorsor T).presheaf.map j.op (unitsTorsorBasis T t) =
      unitsTorsorBasis T (T.sheaf.obj.map j.op t) := by
  refine unitsTorsorSections.ext fun W i s ↦ ?_
  rw [ofUnitsTorsor_map_apply, unitsTorsorBasis_apply, unitsTorsorBasis_apply, torsor_map_map]

/-- Every section of `L(T)` over `U` is a multiple of the basis section `f_t`. -/
lemma eq_smul_unitsTorsorBasis {U : X.Opens} (f : Γ(ofUnitsTorsor T, U))
    (t : T.sheaf.obj.obj (op U)) :
    f = (show unitsTorsorSections T U from f).1 U (𝟙 U) t • unitsTorsorBasis T t := by
  refine unitsTorsorSections.ext fun V i s ↦ ?_
  rw [ofUnitsTorsor_smul_apply, unitsTorsorBasis_apply,
    ← unitsTorsorSections.map_apply (show unitsTorsorSections T U from f) (𝟙 U) i t]
  conv_lhs => rw [← T.sub_vadd (T.sheaf.obj.map i.op t) s]
  rw [unitsTorsorSections.vadd_apply, mul_comm]
  rfl

@[simp]
lemma unitsTorsorBasis_apply_self {U : X.Opens} (t : T.sheaf.obj.obj (op U)) :
    (show unitsTorsorSections T U from unitsTorsorBasis T t).1 U (𝟙 U) t = 1 := by
  rw [unitsTorsorBasis_apply]
  change (((Additive.toMul (T.sub (T.sheaf.obj.map (𝟙 (op U)) t) t))⁻¹ : Γ(X, U)ˣ) : Γ(X, U))
    = 1
  rw [T.sheaf.obj.map_id]
  simp

/-- The basis section `f_t` of `L(T)` is a generator. -/
lemma isGenerator_unitsTorsorBasis {U : X.Opens} (t : T.sheaf.obj.obj (op U)) :
    (ofUnitsTorsor T).IsGenerator (unitsTorsorBasis T t) := by
  intro V i
  rw [map_unitsTorsorBasis]
  refine ⟨fun a b h ↦ ?_, fun f ↦ ⟨_, (eq_smul_unitsTorsorBasis f _).symm⟩⟩
  have := congr_arg (fun f : Γ(ofUnitsTorsor T, V) ↦
    (show unitsTorsorSections T V from f).1 V (𝟙 V) (T.sheaf.obj.map i.op t)) h
  simpa using this

instance isInvertible_ofUnitsTorsor :
    SheafOfModules.IsInvertible.{u, u, u} (ofUnitsTorsor T) := by
  refine SheafOfModules.isInvertible_of_forall_over_unit (M := ofUnitsTorsor T)
    (I := Σ U : X.Opens, T.sheaf.obj.obj (op U)) (fun p ↦ p.1) ?_
    fun p ↦ ⟨IsGenerator.overIso (isGenerator_unitsTorsorBasis p.2)⟩
  intro V x hx
  obtain ⟨W, f, ⟨t⟩, hxW⟩ := T.nonemptySieve_mem ⊤ x trivial
  exact ⟨V ⊓ W, homOfLE inf_le_left, ⟨⟨W, t⟩, ⟨homOfLE inf_le_right⟩⟩, ⟨hx, hxW⟩⟩

/-- Every `𝒪_Xˣ`-torsor `T` is the torsor of generators of `L(T)`, via `t ↦ f_t`. -/
lemma equiv_generatorsTorsor_ofUnitsTorsor : T ≈ (ofUnitsTorsor T).generatorsTorsor := by
  refine ⟨Sheaf.Torsor.Iso.ofHom (ObjectProperty.homMk
    { app U := TypeCat.ofHom fun t ↦ ⟨unitsTorsorBasis T t, isGenerator_unitsTorsorBasis t⟩
      naturality U V f := ?_ }) fun U g t ↦ Subtype.ext ?_⟩
  · ext t
    apply Subtype.ext
    exact (map_unitsTorsorBasis (U := U.unop) t f.unop).symm
  · refine unitsTorsorSections.ext fun V i s ↦ ?_
    change (((unitsSheaf.toUnits (T.sub (T.sheaf.obj.map i.op (T.vadd U g t)) s))⁻¹ :
      Γ(X, V)ˣ) : Γ(X, V)) = X.presheaf.map i.op (unitsSheaf.toUnits g : Γ(X, U.unop)) *
        (((unitsSheaf.toUnits (T.sub (T.sheaf.obj.map i.op t) s))⁻¹ : Γ(X, V)ˣ) : Γ(X, V))
    rw [T.map_vadd, T.sub_vadd_left]
    change (((unitsSheaf.toUnits (T.sub (T.sheaf.obj.map i.op t) s) /
      unitsSheaf.toUnits (X.unitsSheaf.obj.map i.op g))⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) = _
    rw [inv_div, div_eq_mul_inv, Units.val_mul]
    rfl

end OfUnitsTorsor

section Comparison

variable {T T' : Sheaf.Torsor X.unitsSheaf}

/-- The map `L(T') ⟶ L(T)` induced by an equivariant map `φ : T ⟶ T'` of torsors, given by
precomposition with `φ`. -/
noncomputable def ofUnitsTorsorMap (φ : T.sheaf ⟶ T'.sheaf)
    (hφ : ∀ U g t, φ.hom.app U (T.vadd U g t) = T'.vadd U g (φ.hom.app U t)) :
    ofUnitsTorsor T' ⟶ ofUnitsTorsor T :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun f := show unitsTorsorSections T U.unop from
            ⟨fun V i t ↦ (show unitsTorsorSections T' U.unop from f).1 V i (φ.hom.app _ t),
              fun V W i j t ↦ by
                dsimp only
                rw [← unitsTorsorSections.map_apply]
                exact congr_arg _ (NatTrans.naturality_apply φ.hom j.op t),
              fun V i g t ↦ by
                dsimp only
                rw [hφ, unitsTorsorSections.vadd_apply]⟩
          map_zero' := rfl
          map_add' _ _ := rfl }
      naturality _ _ _ := rfl }
    fun _ _ _ ↦ rfl⟩

lemma ofUnitsTorsorMap_apply (φ : T.sheaf ⟶ T'.sheaf)
    (hφ : ∀ U g t, φ.hom.app U (T.vadd U g t) = T'.vadd U g (φ.hom.app U t)) {U V : X.Opens}
    (f : Γ(ofUnitsTorsor T', U)) (i : V ⟶ U) (t : T.sheaf.obj.obj (op V)) :
    (show unitsTorsorSections T U from (ofUnitsTorsorMap φ hφ).app U f).1 V i t =
      (show unitsTorsorSections T' U from f).1 V i (φ.hom.app _ t) := by
  unfold ofUnitsTorsorMap
  dsimp [Hom.app, Hom.mapPresheaf]
  rfl

lemma ofUnitsTorsorMap_id :
    ofUnitsTorsorMap (𝟙 T.sheaf) (fun _ _ _ ↦ rfl) = 𝟙 (ofUnitsTorsor T) := by
  refine hom_ext _ _ fun U ↦ ?_
  ext f
  refine unitsTorsorSections.ext fun V i t ↦ ?_
  unfold ofUnitsTorsorMap
  dsimp [Hom.app, Hom.mapPresheaf]
  rfl

lemma ofUnitsTorsorMap_comp {T'' : Sheaf.Torsor X.unitsSheaf} (φ : T.sheaf ⟶ T'.sheaf)
    (hφ : ∀ U g t, φ.hom.app U (T.vadd U g t) = T'.vadd U g (φ.hom.app U t))
    (ψ : T'.sheaf ⟶ T''.sheaf)
    (hψ : ∀ U g t, ψ.hom.app U (T'.vadd U g t) = T''.vadd U g (ψ.hom.app U t)) :
    ofUnitsTorsorMap ψ hψ ≫ ofUnitsTorsorMap φ hφ =
      ofUnitsTorsorMap (φ ≫ ψ) (fun U g t ↦ by
        change ψ.hom.app U (φ.hom.app U _) = _
        rw [hφ, hψ]
        rfl) := by
  refine hom_ext _ _ fun U ↦ ?_
  ext f
  refine unitsTorsorSections.ext fun V i t ↦ ?_
  unfold ofUnitsTorsorMap
  dsimp [Hom.app, Hom.mapPresheaf]
  rfl

lemma ofUnitsTorsorMap_congr {φ φ' : T.sheaf ⟶ T'.sheaf} (h : φ = φ')
    (hφ : ∀ U g t, φ.hom.app U (T.vadd U g t) = T'.vadd U g (φ.hom.app U t))
    (hφ' : ∀ U g t, φ'.hom.app U (T.vadd U g t) = T'.vadd U g (φ'.hom.app U t)) :
    ofUnitsTorsorMap φ hφ = ofUnitsTorsorMap φ' hφ' := by
  subst h
  rfl

/-- Isomorphic torsors have isomorphic modules. -/
lemma nonempty_ofUnitsTorsor_iso (h : T ≈ T') :
    Nonempty (ofUnitsTorsor T ≅ ofUnitsTorsor T') := by
  obtain ⟨e⟩ := h
  refine ⟨{ hom := ofUnitsTorsorMap e.symm.iso.hom e.symm.map_vadd
            inv := ofUnitsTorsorMap e.iso.hom e.map_vadd
            hom_inv_id := ?_
            inv_hom_id := ?_ }⟩
  · rw [ofUnitsTorsorMap_comp, ← ofUnitsTorsorMap_id]
    exact ofUnitsTorsorMap_congr e.iso.hom_inv_id _ _
  · rw [ofUnitsTorsorMap_comp, ← ofUnitsTorsorMap_id]
    exact ofUnitsTorsorMap_congr e.iso.inv_hom_id _ _

section ToOfUnitsTorsor

variable [M.IsInvertible]

variable (M) in
/-- The section of `L(Isom(𝒪, M))` attached to a section `m` of `M`: it sends a local
generator `s` to the coefficient of `m` with respect to `s`. -/
noncomputable def toUnitsTorsorSections {U : X.Opens} (m : Γ(M, U)) :
    unitsTorsorSections M.generatorsTorsor U :=
  ⟨fun V i s ↦ IsGenerator.coeff (M := M) s.2 (M.presheaf.map i.op m),
    fun V W i j s ↦ by
      dsimp only
      rw [← map_map_apply i j m]
      exact IsGenerator.coeff_map (M := M) s.2 j _,
    fun V i g s ↦ by
      dsimp only
      rw [IsGenerator.coeff_eq_iff]
      change _ • ((unitsSheaf.toUnits g : Γ(X, V)) • _) = _
      rw [smul_smul, mul_assoc, mul_comm _ (unitsSheaf.toUnits g : Γ(X, V)), ← mul_assoc,
        Units.inv_mul, one_mul]
      exact IsGenerator.coeff_smul _ _⟩

lemma toUnitsTorsorSections_apply {U V : X.Opens} (m : Γ(M, U)) (i : V ⟶ U)
    (s : M.generatorsTorsor.sheaf.obj.obj (op V)) :
    (toUnitsTorsorSections M m).1 V i s =
      IsGenerator.coeff (M := M) s.2 (M.presheaf.map i.op m) :=
  rfl

variable (M) in
/-- The comparison map `M ⟶ L(Isom(𝒪, M))`. -/
noncomputable def toOfUnitsTorsor : M ⟶ ofUnitsTorsor M.generatorsTorsor :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun m := toUnitsTorsorSections M (U := U.unop) m
          map_zero' := unitsTorsorSections.ext fun V i s ↦ by
            rw [toUnitsTorsorSections_apply, map_zero, IsGenerator.coeff_zero]
            rfl
          map_add' m m' := unitsTorsorSections.ext fun V i s ↦ by
            rw [toUnitsTorsorSections_apply, map_add, IsGenerator.coeff_add]
            rfl }
      naturality U U' f := by
        ext m
        refine unitsTorsorSections.ext fun V i s ↦ ?_
        change (toUnitsTorsorSections M (U := U'.unop) (M.presheaf.map f m)).1 V i s =
          (toUnitsTorsorSections M (U := U.unop) m).1 V (i ≫ f.unop) s
        rw [toUnitsTorsorSections_apply, toUnitsTorsorSections_apply, ← map_map_apply]
        rfl }
    fun U a m ↦ by
      refine unitsTorsorSections.ext (U := U.unop) fun V i s ↦ ?_
      change (toUnitsTorsorSections M (U := U.unop) (a • m)).1 V i s =
        X.presheaf.map i.op a * (toUnitsTorsorSections M (U := U.unop) m).1 V i s
      rw [toUnitsTorsorSections_apply, toUnitsTorsorSections_apply,
        map_smul, IsGenerator.coeff_smul_left]⟩

lemma toOfUnitsTorsor_app_apply {U : X.Opens} (m : Γ(M, U)) :
    (toOfUnitsTorsor M).app U m = toUnitsTorsorSections M m := by
  unfold toOfUnitsTorsor
  dsimp [Hom.app, Hom.mapPresheaf]
  rfl

lemma bijective_toUnitsTorsorSections (U : X.Opens) :
    Function.Bijective (toUnitsTorsorSections M (U := U)) := by
  have hS := (generatorsTorsor M).nonemptySieve_mem U
  have hM := Modules.isSheaf_presheaf_comp_forget M _ hS
  refine ⟨fun m m' h ↦ ?_, fun F ↦ ?_⟩
  · refine hM.isSeparatedFor.ext fun V f ⟨s⟩ ↦ ?_
    have := congr_arg (fun F : unitsTorsorSections M.generatorsTorsor U ↦ F.1 V f s) h
    simp only [toUnitsTorsorSections_apply] at this
    change M.presheaf.map f.op m = M.presheaf.map f.op m'
    rw [← IsGenerator.coeff_smul (M := M) s.2 (M.presheaf.map f.op m), this,
      IsGenerator.coeff_smul]
  · -- two generators give the same section `F(s) • s`
    have key {V : X.Opens} (f : V ⟶ U) (s s' : M.generatorsTorsor.sheaf.obj.obj (op V)) :
        F.1 V f s • (show Γ(M, V) from s.1) = F.1 V f s' • (show Γ(M, V) from s'.1) := by
      rw [← (generatorsTorsor M).sub_vadd s s', unitsTorsorSections.vadd_apply]
      change _ = _ • (((unitsSheaf.toUnits ((generatorsTorsor M).sub s s') : Γ(X, V)ˣ) :
        Γ(X, V)) • _)
      rw [smul_smul, mul_assoc, mul_comm _ ((unitsSheaf.toUnits _ : Γ(X, V)ˣ) : Γ(X, V)),
        ← mul_assoc, Units.inv_mul, one_mul]
    let x : Presieve.FamilyOfElements (M.presheaf ⋙ CategoryTheory.forget AddCommGrpCat)
        (Sheaf.nonemptySieve (generatorsTorsor M).sheaf.obj U).arrows :=
      fun V f hf ↦ F.1 V f hf.some • (show Γ(M, V) from hf.some.1)
    have hx : x.Compatible := by
      intro Z₁ Z₂ V g₁ g₂ f₁ f₂ hf₁ hf₂ hcomm
      change M.presheaf.map g₁.op (F.1 Z₁ f₁ hf₁.some • _) =
        M.presheaf.map g₂.op (F.1 Z₂ f₂ hf₂.some • _)
      rw [map_smul, map_smul, ← unitsTorsorSections.map_apply,
        ← unitsTorsorSections.map_apply]
      have hc : g₁ ≫ f₁ = g₂ ≫ f₂ := hcomm
      exact (congr_arg (fun k ↦ F.1 V k _ • _) hc).trans
        (key (g₂ ≫ f₂) (M.generatorsTorsor.sheaf.obj.map g₁.op hf₁.some)
          (M.generatorsTorsor.sheaf.obj.map g₂.op hf₂.some))
    refine ⟨hM.amalgamate x hx, unitsTorsorSections.ext fun V i s ↦ ?_⟩
    rw [toUnitsTorsorSections_apply, IsGenerator.coeff_eq_iff]
    have := hM.valid_glue hx i ⟨s⟩
    change M.presheaf.map i.op _ = _ at this
    rw [this]
    exact key i _ _

instance : IsIso (toOfUnitsTorsor M) := by
  rw [Hom.isIso_iff_isIso_app]
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  have h := bijective_toUnitsTorsorSections (M := M) U
  refine ⟨fun m m' hm ↦ h.1 ?_, fun F ↦ ?_⟩
  · rwa [toOfUnitsTorsor_app_apply, toOfUnitsTorsor_app_apply] at hm
  · obtain ⟨m, hm⟩ := h.2 F
    exact ⟨m, (toOfUnitsTorsor_app_apply m).trans hm⟩

end ToOfUnitsTorsor

end Comparison

end Modules

open Modules in
/-- **Line bundles and `𝒪ˣ`-torsors, Zariski version.** For a scheme `X`, the map sending an
invertible `𝒪_X`-module `M` to the `𝒪_Xˣ`-torsor `Isom(𝒪_X, M)` of its local generators is a
bijection from the Picard group of `X` onto the set of isomorphism classes of `𝒪_Xˣ`-torsors on
the Zariski site of `X`. Its inverse sends a torsor `T` to the invertible module
`(T × 𝒪_X) / 𝒪_Xˣ` (`AlgebraicGeometry.Scheme.Modules.ofUnitsTorsor`).
(blueprint: `lem-sc-line-bundle-torsor`, Zariski part) -/
theorem nonempty_pic_equiv_quotient_torsor_unitsSheaf (X : Scheme.{u}) :
    Nonempty (X.Pic ≃ _root_.Quotient (Sheaf.Torsor.setoid (G := X.unitsSheaf))) := by
  let Φ : X.Pic → _root_.Quotient (Sheaf.Torsor.setoid (G := X.unitsSheaf)) := fun L ↦
    haveI := Pic.isInvertible L
    _root_.Quotient.mk _ (generatorsTorsor ((fromSkeleton X.Modules).obj L.val))
  refine ⟨Equiv.ofBijective Φ ⟨fun L L' h ↦ ?_, fun T ↦ ?_⟩⟩
  · have := Pic.isInvertible L
    have := Pic.isInvertible L'
    obtain ⟨e⟩ := nonempty_ofUnitsTorsor_iso (_root_.Quotient.exact h)
    exact Pic.eq_iff_nonempty_iso.2
      ⟨asIso (toOfUnitsTorsor _) ≪≫ e ≪≫ (asIso (toOfUnitsTorsor _)).symm⟩
  · induction T using _root_.Quotient.inductionOn with | h T => ?_
    refine ⟨Pic.mk (ofUnitsTorsor T), _root_.Quotient.sound ?_⟩
    have := Pic.isInvertible (Pic.mk (ofUnitsTorsor T))
    exact Setoid.trans (generatorsTorsor_equiv_of_iso (fromSkeletonToSkeletonIso _))
      (Setoid.symm (equiv_generatorsTorsor_ofUnitsTorsor (T := T)))

end AlgebraicGeometry.Scheme
