/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.Sites.EtalePicard
public import WeilConjectures.CategoryTheory.Sites.TorsorGluing
public import WeilConjectures.AlgebraicGeometry.Picard.Group

/-!
# Every `𝔾ₘ`-torsor comes from an invertible module

Let `T` be a `𝔾ₘ`-torsor on the small étale site of `X`, with sections `t i` over the members
`V i` of an étale covering. The differences of the `t i` on the overlaps `V i ×_X V j` form a
cocycle of units, and twisting the descent datum of `𝒪_X` by multiplication by this cocycle
gives a descent datum of sheaves of modules.
-/

@[expose] public section

universe u

open CategoryTheory Opposite Limits CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
  MonoidalCategory

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

namespace Etale

/-- The overlap `A ×_X B` of two étale `X`-schemes. -/
noncomputable def inter (A B : X.Etale) : X.Etale :=
  Etale.mk (pullback.fst A.hom B.hom ≫ A.hom)

/-- The first projection from the overlap. -/
noncomputable def interFst (A B : X.Etale) : inter A B ⟶ A :=
  MorphismProperty.Over.homMk (pullback.fst A.hom B.hom) rfl

/-- The second projection from the overlap. -/
noncomputable def interSnd (A B : X.Etale) : inter A B ⟶ B :=
  MorphismProperty.Over.homMk (pullback.snd A.hom B.hom) pullback.condition.symm

/-- The map to the overlap given by two maps. -/
noncomputable def interLift {A B Z : X.Etale} (u : Z ⟶ A) (w : Z ⟶ B) : Z ⟶ inter A B :=
  MorphismProperty.Over.homMk
    (pullback.lift u.left w.left (by rw [MorphismProperty.Over.w u, MorphismProperty.Over.w w]))
    (by
      change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ A.hom = Z.hom
      rw [pullback.lift_fst_assoc, MorphismProperty.Over.w u])

@[reassoc (attr := simp)]
lemma interLift_interFst {A B Z : X.Etale} (u : Z ⟶ A) (w : Z ⟶ B) :
    interLift u w ≫ interFst A B = u := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma interLift_interSnd {A B Z : X.Etale} (u : Z ⟶ A) (w : Z ⟶ B) :
    interLift u w ≫ interSnd A B = w := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.lift_snd _ _ _

end Etale

namespace Torsor

variable (T : Sheaf.Torsor X.gmSheaf) {ι : Type*} (V : ι → X.Etale)
  (t : ∀ i, T.sheaf.obj.obj (op (V i)))

/-- The transition function `t i - t j` on the overlap `V i ×_X V j`, as a unit. -/
noncomputable def transition (i j : ι) : Γ((Etale.inter (V i) (V j)).left, ⊤)ˣ :=
  Additive.toMul (T.sub (T.sheaf.obj.map (Etale.interSnd (V i) (V j)).op (t j))
    (T.sheaf.obj.map (Etale.interFst (V i) (V j)).op (t i))).down

/-- The transition function pulled back to `Z` is the difference of the pulled back sections. -/
lemma appTop_transition {Z : X.Etale} {i j : ι} (u : Z ⟶ V i) (w : Z ⟶ V j) :
    (Etale.interLift u w).left.appTop
        (transition T V t i j : Γ((Etale.inter (V i) (V j)).left, ⊤)) =
      ((Additive.toMul (T.sub (T.sheaf.obj.map w.op (t j)) (T.sheaf.obj.map u.op (t i))).down :
        Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤)) := by
  have h := T.map_sub_apply (Etale.interLift u w).op
    (T.sheaf.obj.map (Etale.interSnd (V i) (V j)).op (t j))
    (T.sheaf.obj.map (Etale.interFst (V i) (V j)).op (t i))
  rw [T.map_map_apply, T.map_map_apply, Etale.interLift_interSnd,
    Etale.interLift_interFst] at h
  rw [← h]
  rfl

end Torsor

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Torsor

variable {X : Scheme.{u}} (T : Sheaf.Torsor X.gmSheaf) {ι : Type*} (V : ι → X.Etale)
  (t : ∀ i, T.sheaf.obj.obj (op (V i)))

/-- The transition function `t i₁ - t i₂` pulled back to a scheme `Y` mapping to `V i₁` and
`V i₂` over `X`. -/
noncomputable def transitionAt {Y : Scheme.{u}} {i₁ i₂ : ι} (f₁ : Y ⟶ (V i₁).left)
    (f₂ : Y ⟶ (V i₂).left) (h : f₁ ≫ (V i₁).hom = f₂ ≫ (V i₂).hom) : Γ(Y, ⊤) :=
  (pullback.lift f₁ f₂ h).appTop (transition T V t i₁ i₂ : Γ((Etale.inter (V i₁) (V i₂)).left, ⊤))

lemma transitionAt_comp {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) {i₁ i₂ : ι} (f₁ : Y ⟶ (V i₁).left)
    (f₂ : Y ⟶ (V i₂).left) (h : f₁ ≫ (V i₁).hom = f₂ ≫ (V i₂).hom) :
    transitionAt T V t (g ≫ f₁) (g ≫ f₂) (by simp [h]) =
      g.appTop (transitionAt T V t f₁ f₂ h) := by
  have : pullback.lift (g ≫ f₁) (g ≫ f₂) (by simp [h]) = g ≫ pullback.lift f₁ f₂ h := by
    apply pullback.hom_ext <;> simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]
  rw [transitionAt, this]
  rfl

lemma transitionAt_self {Y : Scheme.{u}} {i : ι} (f : Y ⟶ (V i).left) :
    transitionAt T V t f f rfl = 1 := by
  have : pullback.lift f f rfl = f ≫ (Etale.interLift (𝟙 (V i)) (𝟙 (V i))).left := by
    apply pullback.hom_ext
    · change _ = (f ≫ pullback.lift (𝟙 (V i).left) (𝟙 (V i).left) rfl) ≫
        pullback.fst (V i).hom (V i).hom
      rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.comp_id]
    · change _ = (f ≫ pullback.lift (𝟙 (V i).left) (𝟙 (V i).left) rfl) ≫
        pullback.snd (V i).hom (V i).hom
      rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]
  rw [transitionAt, this]
  change f.appTop ((Etale.interLift (𝟙 (V i)) (𝟙 (V i))).left.appTop _) = 1
  rw [appTop_transition, T.sub_self]
  change f.appTop ((1 : Γ((V i).left, ⊤)ˣ) : Γ((V i).left, ⊤)) = 1
  rw [Units.val_one, map_one]

lemma transitionAt_eq {Y : Scheme.{u}} {Z : X.Etale} (k : Y ⟶ Z.left) {i j : ι} (u : Z ⟶ V i)
    (w : Z ⟶ V j) (f₁ : Y ⟶ (V i).left) (f₂ : Y ⟶ (V j).left)
    (h : f₁ ≫ (V i).hom = f₂ ≫ (V j).hom) (h₁ : k ≫ u.left = f₁) (h₂ : k ≫ w.left = f₂) :
    transitionAt T V t f₁ f₂ h = k.appTop ((Additive.toMul
      (T.sub (T.sheaf.obj.map w.op (t j)) (T.sheaf.obj.map u.op (t i))).down :
        Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤)) := by
  have : pullback.lift f₁ f₂ h = k ≫ (Etale.interLift u w).left := by
    apply pullback.hom_ext
    · change _ = k ≫ pullback.lift u.left w.left _ ≫ pullback.fst (V i).hom (V j).hom
      rw [pullback.lift_fst, pullback.lift_fst, h₁]
    · change _ = k ≫ pullback.lift u.left w.left _ ≫ pullback.snd (V i).hom (V j).hom
      rw [pullback.lift_snd, pullback.lift_snd, h₂]
  rw [transitionAt, this]
  change k.appTop ((Etale.interLift u w).left.appTop _) = _
  rw [appTop_transition]

lemma transitionAt_mul {Y : Scheme.{u}} {i₁ i₂ i₃ : ι} (f₁ : Y ⟶ (V i₁).left)
    (f₂ : Y ⟶ (V i₂).left) (f₃ : Y ⟶ (V i₃).left) (h₁₂ : f₁ ≫ (V i₁).hom = f₂ ≫ (V i₂).hom)
    (h₂₃ : f₂ ≫ (V i₂).hom = f₃ ≫ (V i₃).hom) :
    transitionAt T V t f₁ f₂ h₁₂ * transitionAt T V t f₂ f₃ h₂₃ =
      transitionAt T V t f₁ f₃ (h₁₂.trans h₂₃) := by
  let Z := Etale.inter (Etale.inter (V i₁) (V i₂)) (V i₃)
  let u₁ : Z ⟶ V i₁ := Etale.interFst _ _ ≫ Etale.interFst _ _
  let u₂ : Z ⟶ V i₂ := Etale.interFst _ _ ≫ Etale.interSnd _ _
  let u₃ : Z ⟶ V i₃ := Etale.interSnd _ _
  let k : Y ⟶ Z.left := pullback.lift (pullback.lift f₁ f₂ h₁₂) f₃
    (by
      change pullback.lift f₁ f₂ h₁₂ ≫ pullback.fst _ _ ≫ (V i₁).hom = _
      rw [pullback.lift_fst_assoc, h₁₂, h₂₃])
  have k₁ : k ≫ u₁.left = f₁ := by
    change k ≫ pullback.fst _ _ ≫ pullback.fst _ _ = f₁
    simp only [k]
    erw [pullback.lift_fst_assoc, pullback.lift_fst]
  have k₂ : k ≫ u₂.left = f₂ := by
    change k ≫ pullback.fst _ _ ≫ pullback.snd _ _ = f₂
    simp only [k]
    erw [pullback.lift_fst_assoc, pullback.lift_snd]
  have k₃ : k ≫ u₃.left = f₃ := by
    change k ≫ pullback.snd _ _ = f₃
    simp only [k]
    erw [pullback.lift_snd]
  rw [transitionAt_eq T V t k u₁ u₂ _ _ _ k₁ k₂, transitionAt_eq T V t k u₂ u₃ _ _ _ k₂ k₃,
    transitionAt_eq T V t k u₁ u₃ _ _ _ k₁ k₃, ← map_mul, ← Units.val_mul]
  have e : T.sub (T.sheaf.obj.map u₃.op (t i₃)) (T.sheaf.obj.map u₁.op (t i₁)) =
      T.sub (T.sheaf.obj.map u₂.op (t i₂)) (T.sheaf.obj.map u₁.op (t i₁)) +
        T.sub (T.sheaf.obj.map u₃.op (t i₃)) (T.sheaf.obj.map u₂.op (t i₂)) := by
    rw [← T.sub_sub_sub (T.sheaf.obj.map u₃.op (t i₃)) (T.sheaf.obj.map u₂.op (t i₂)),
      sub_add_cancel]
  rw [e]
  rfl

end AlgebraicGeometry.Scheme.Torsor

namespace AlgebraicGeometry

lemma smulMor_naturality {Y : Scheme.{u}} {A B : modulesPseudofunctor.obj (.mk (op Y))}
    (φ : A ⟶ B) (a : Γ(Y, ⊤)) : smulMor A a ≫ φ = φ ≫ smulMor B a :=
  Scheme.Modules.smulHom_naturality (M := (A : Y.Modules)) (N := (B : Y.Modules)) φ a

lemma smulMor_comp_smulMor_comp {Y : Scheme.{u}} {A B C : modulesPseudofunctor.obj (.mk (op Y))}
    (φ : A ⟶ B) (ψ : B ⟶ C) (χ : A ⟶ C) (h : φ ≫ ψ = χ) (a b c : Γ(Y, ⊤)) (habc : a * b = c) :
    (smulMor A a ≫ φ) ≫ (smulMor B b ≫ ψ) = smulMor A c ≫ χ := by
  rw [Category.assoc, ← Category.assoc φ, ← smulMor_naturality, Category.assoc,
    ← Category.assoc (smulMor A a), ← smulMor_mul, h, mul_comm, habc]

namespace Scheme.Torsor

variable {X : Scheme.{u}} (T : Sheaf.Torsor X.gmSheaf) {ι : Type*} (V : ι → X.Etale)
  (t : ∀ i, T.sheaf.obj.obj (op (V i)))

/-- The descent datum of the structure sheaf relative to the `V i`. -/
noncomputable abbrev unitDescentData :
    modulesPseudofunctor.DescentData (S := X) (X := fun i ↦ (V i).left) (fun i ↦ (V i).hom) :=
  Pseudofunctor.DescentData.ofObj (F := modulesPseudofunctor) (S := X) (X := fun i ↦ (V i).left)
    (f := fun i ↦ (V i).hom) (Modules.unitObj X)

set_option backward.isDefEq.respectTransparency.types false in
/-- The descent datum of the structure sheaf twisted by the transition functions of `T`: the
gluing morphisms of `𝒪_X` restricted to the `V i` are multiplied by `t i₂ - t i₁`. -/
noncomputable def descentData :
    modulesPseudofunctor.DescentData (S := X) (X := fun i ↦ (V i).left) (fun i ↦ (V i).hom) where
  obj i := (modulesPseudofunctor.map (V i).hom.op.toLoc).toFunctor.obj (Modules.unitObj X)
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
    smulMor ((modulesPseudofunctor.map f₁.op.toLoc).toFunctor.obj
        ((modulesPseudofunctor.map (V i₁).hom.op.toLoc).toFunctor.obj (Modules.unitObj X)))
        (transitionAt T V t f₁ f₂ (by rw [hf₁, hf₂])) ≫
      (unitDescentData V).hom q f₁ f₂ hf₁ hf₂
  pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    subst hgf₁ hgf₂
    rw [pullHom_comp _ _ g (g ≫ f₁) (g ≫ f₁) (g ≫ f₂) rfl rfl rfl]
    unfold smulMor
    rw [pullHom_smulHom, transitionAt_comp]
    · congr 1
      exact (unitDescentData V).pullHom_hom g q q' hq f₁ f₂ hf₁
        hf₂ (g ≫ f₁) (g ≫ f₂) rfl rfl
    · rw [hf₁, hf₂]
  hom_self Y q i g hg := by
    rw [transitionAt_self, smulMor_one, Category.id_comp,
      (unitDescentData V).hom_self q g hg]
    rfl
  hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    exact smulMor_comp_smulMor_comp _ _ _ ((unitDescentData V).hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃)
      _ _ _ (transitionAt_mul T V t f₁ f₂ f₃ _ _)

end Scheme.Torsor

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Torsor

variable {X : Scheme.{u}} (T : Sheaf.Torsor X.gmSheaf)

set_option backward.isDefEq.respectTransparency.types false in
/-- The étale `X`-schemes over which a `𝔾ₘ`-torsor has a section cover `X` for the fpqc
topology. -/
lemma ofArrows_mem_fpqcTopology :
    Sieve.ofArrows (fun i : {V : X.Etale // Nonempty (T.sheaf.obj.obj (op V))} ↦ i.1.left)
      (fun i ↦ i.1.hom) ∈ Scheme.fpqcTopology X := by
  have hR := T.nonemptySieve_mem (Etale.mk (𝟙 X))
  obtain ⟨𝒰, _, h, hle⟩ := (mem_smallGrothendieckTopology _ _).1 hR
  apply proetaleTopology_le_fpqcTopology
  apply etaleTopology_le_proetaleTopology
  rw [mem_grothendieckTopology_iff]
  refine ⟨𝒰, ?_⟩
  rintro _ _ ⟨j⟩
  have hj : Nonempty (T.sheaf.obj.obj (op ((𝒰.X j).asOverProp X (h j)))) :=
    hle _ _ (Presieve.ofArrows.mk j)
  refine ⟨_, 𝟙 _, _, Presieve.ofArrows.mk
    (ι := {V : X.Etale // Nonempty (T.sheaf.obj.obj (op V))}) ⟨_, hj⟩, ?_⟩
  rw [Category.id_comp]
  change 𝒰.X j ↘ X = _
  rw [← comp_over (𝒰.f j) X]
  exact Category.comp_id _

end AlgebraicGeometry.Scheme.Torsor

namespace AlgebraicGeometry.Scheme.Torsor

/-- Transport of a commutative square along isomorphisms: if `x₁ ≫ β⁻¹ ≫ δ = (s ≫ α⁻¹ ≫ γ) ≫ x₂`
and `α ≫ s = s' ≫ α`, then `α ≫ x₁ ≫ β⁻¹ = s' ≫ γ ≫ x₂ ≫ δ⁻¹`. -/
private lemma comp_eq_of_comm {𝒞 : Type*} [Category 𝒞] {Oq O₁ O₂ Mq M₁ M₂ : 𝒞} (α : Oq ≅ O₁)
    (β : Mq ≅ M₁) (γ : Oq ≅ O₂) (δ : Mq ≅ M₂) (x₁ : O₁ ⟶ M₁) (x₂ : O₂ ⟶ M₂) (s : O₁ ⟶ O₁)
    (s' : Oq ⟶ Oq) (hs : α.hom ≫ s = s' ≫ α.hom)
    (comm : x₁ ≫ β.inv ≫ δ.hom = (s ≫ α.inv ≫ γ.hom) ≫ x₂) :
    α.hom ≫ x₁ ≫ β.inv = s' ≫ γ.hom ≫ x₂ ≫ δ.inv := by
  have : x₁ ≫ β.inv = (s ≫ α.inv ≫ γ.hom) ≫ x₂ ≫ δ.inv := by
    rw [← Category.assoc _ x₂, ← comm]
    simp
  rw [this, ← Category.assoc, ← Category.assoc, ← Category.assoc, hs]
  simp

variable {X : Scheme.{u}} (T : Sheaf.Torsor X.gmSheaf)

set_option maxHeartbeats 4000000 in
-- the defeq checks through the small étale and pro-étale sites are slow
set_option backward.isDefEq.respectTransparency.types false in
/-- **Every `𝔾ₘ`-torsor is the torsor of trivialisations of an invertible module.** The descent
datum `AlgebraicGeometry.Scheme.Torsor.descentData` is effective by fpqc descent, and the
trivialisations of the descended module over the covering have the transition functions of
the torsor. -/
theorem exists_etaleIsoTorsor_equiv :
    ∃ (L : modulesPseudofunctor.obj (.mk (op X)))
      (_ : SheafOfModules.IsInvertible.{u, u, u} (L : X.Modules)),
      Modules.etaleIsoTorsor L ≈ T := by
  let ι := {V : X.Etale // Nonempty (T.sheaf.obj.obj (op V))}
  let V : ι → X.Etale := fun i ↦ i.1
  let t : ∀ i, T.sheaf.obj.obj (op (V i)) := fun i ↦ i.2.some
  have hcov := ofArrows_mem_fpqcTopology T
  have hD (i : ι) : ((descentData T V t).obj i : (V i).left.Modules).IsQuasicoherent :=
    Modules.isQuasicoherent_pullback (V i).hom (Modules.unit X)
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_isQuasicoherent_toDescentData_iso (fun i : ι ↦ (V i).hom) hcov
    (descentData T V t) hD
  have hDinv (i : ι) : SheafOfModules.IsInvertible.{u, u, u}
      ((descentData T V t).obj i : (V i).left.Modules) :=
    SheafOfModules.IsInvertible.of_iso.{u, u, u} (M := 𝟙_ (V i).left.Modules)
      (Modules.pullbackObjUnitIso (V i).hom).symm
      (h := Modules.IsInvertible.sheafOfModules_isInvertible (𝟙_ (V i).left.Modules))
  have hinv := isInvertible_of_toDescentData_iso (fun i : ι ↦ (V i).hom) hcov
    (descentData T V t) M ⟨e⟩ hDinv
  have : MorphismProperty.ContainsIdentities
      (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) :=
    AlgebraicGeometry.Etale.instIsMultiplicativeScheme.toContainsIdentities
  have hT : Limits.IsTerminal (Etale.mk (𝟙 X)) := MorphismProperty.Over.mkIdTerminal _ X
  refine ⟨M, hinv, Setoid.symm (Sheaf.Torsor.equiv_of_sub_eq hT T (Modules.etaleIsoTorsor M)
    (Sheaf.nonemptySieve T.sheaf.obj (Etale.mk (𝟙 X))) (T.nonemptySieve_mem _)
    (fun V hV ↦ hV.some)
    (fun V hV ↦ Modules.etaleIsoTorsorMk M (e.inv.hom ⟨V, hV⟩)
      ⟨e.hom.hom ⟨V, hV⟩,
        congrArg (fun φ ↦ Pseudofunctor.DescentData.Hom.hom φ ⟨V, hV⟩) e.inv_hom_id,
        congrArg (fun φ ↦ Pseudofunctor.DescentData.Hom.hom φ ⟨V, hV⟩) e.hom_inv_id⟩) ?_)⟩
  intro V₁ V₂ Z h₁ h₂ a b
  have hc := e.inv.comm Z.hom (i₁ := ⟨V₂, h₂⟩) (i₂ := ⟨V₁, h₁⟩) b.left a.left
    (MorphismProperty.Over.w b) (MorphismProperty.Over.w a)
  have e1 := transitionAt_eq T V t (𝟙 Z.left) (i := ⟨V₂, h₂⟩) (j := ⟨V₁, h₁⟩) b a b.left a.left
    (by rw [MorphismProperty.Over.w a, MorphismProperty.Over.w b]) (Category.id_comp _)
    (Category.id_comp _)
  symm
  rw [Sheaf.Torsor.sub_eq_iff]
  apply Modules.etaleIsoTorsorVal_injective
  rw [Modules.etaleIsoTorsorVal_vadd]
  have e2 : ((Additive.toMul (T.sub (T.sheaf.obj.map a.op (t ⟨V₁, h₁⟩))
      (T.sheaf.obj.map b.op (t ⟨V₂, h₂⟩))).down : Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤)) =
      transitionAt T V t (i₁ := ⟨V₂, h₂⟩) (i₂ := ⟨V₁, h₁⟩) b.left a.left
        (by rw [MorphismProperty.Over.w a, MorphismProperty.Over.w b]) :=
    e1.symm
  erw [e2]
  change smulMor _ _ ≫ (modulesPseudofunctor.presheafHom (Modules.unitObj X) M).map
      ((toProEt X ⋙ ProEt.forget X).map a).op (e.inv.hom ⟨V₁, h₁⟩) =
    (modulesPseudofunctor.presheafHom (Modules.unitObj X) M).map
      ((toProEt X ⋙ ProEt.forget X).map b).op (e.inv.hom ⟨V₂, h₂⟩)
  simp only [Pseudofunctor.presheafHom_map, TypeCat.ofHom_apply, Quiver.Hom.unop_op]
  dsimp only [pullHom]
  let G := toProEt X ⋙ ProEt.forget X
  let mcB := modulesPseudofunctor.mapComp' (G.obj V₂).hom.op.toLoc (G.map b).left.op.toLoc
    (G.obj Z).hom.op.toLoc (by
      rw [← Quiver.Hom.comp_toLoc, ← op_comp, Over.w (G.map b)])
  let mcA := modulesPseudofunctor.mapComp' (G.obj V₁).hom.op.toLoc (G.map a).left.op.toLoc
    (G.obj Z).hom.op.toLoc (by
      rw [← Quiver.Hom.comp_toLoc, ← op_comp, Over.w (G.map a)])
  have key := comp_eq_of_comm ((Cat.Hom.toNatIso mcB).app (Modules.unitObj X))
    ((Cat.Hom.toNatIso mcB).app M) ((Cat.Hom.toNatIso mcA).app (Modules.unitObj X))
    ((Cat.Hom.toNatIso mcA).app M)
    ((modulesPseudofunctor.map (G.map b).left.op.toLoc).toFunctor.map (e.inv.hom ⟨V₂, h₂⟩))
    ((modulesPseudofunctor.map (G.map a).left.op.toLoc).toFunctor.map (e.inv.hom ⟨V₁, h₁⟩))
    _ _ (smulMor_naturality ((Cat.Hom.toNatIso mcB).app (Modules.unitObj X)).hom
      (transitionAt T V t (i₁ := ⟨V₂, h₂⟩) (i₂ := ⟨V₁, h₁⟩) b.left a.left
        ((MorphismProperty.Over.w b).trans (MorphismProperty.Over.w a).symm))).symm hc
  simp only [Iso.app_hom, Iso.app_inv, Cat.Hom.toNatIso_hom, Cat.Hom.toNatIso_inv, mcA,
    mcB] at key
  exact key.symm

end AlgebraicGeometry.Scheme.Torsor
