/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.LogIdealChartPresentation
public import WeilConjectures.AlgebraicGeometry.FSStrictLogMorphism
/-!
# Identity and composition of logarithmic morphisms

Source: ILO VI 1.1; Kato 1988, section 1
(blueprint: lem-sfb-log-morphism-operations).

Composition is constructed through the canonical pullback of an etale test object.
The formulas on relative triangles prove the recorded composite equations.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Compose log maps by factoring a relative test diagram through the pulled-back
etale object. Source: ILO VI 1.1 (blueprint: lem-sfb-log-morphism-operations). -/
noncomputable def EtaleLogMap.comp {X Y Z : Scheme.{u}}
    {L : EtaleLogStructure X} {M : EtaleLogStructure Y} {N : EtaleLogStructure Z}
    (f : EtaleLogMap L M) (g : EtaleLogMap M N) : EtaleLogMap L N where
  base := f.base ≫ g.base
  sectionMap W V k hk :=
    let U : Y.Etale := Scheme.Etale.mk (pullback.fst g.base W.hom)
    let l : V.left ⟶ U.left := pullback.lift (V.hom ≫ f.base) k (by simpa using hk.symm)
    (f.sectionMap U V l (by simp [l, U])).comp
      (g.sectionMap W U (pullback.snd g.base W.hom) (by
        exact pullback.condition.symm))
  naturality := by
    intro W₁ W₂ V₁ V₂ a c k₁ k₂ h₁ h₂ he
    let U₁ : Y.Etale := Scheme.Etale.mk (pullback.fst g.base W₁.hom)
    let U₂ : Y.Etale := Scheme.Etale.mk (pullback.fst g.base W₂.hom)
    let b : U₁ ⟶ U₂ := MorphismProperty.Over.homMk
      (pullback.map g.base W₁.hom g.base W₂.hom (𝟙 Y) a.left (𝟙 Z)
        (by simp) (by simp)) (by simp [U₁, U₂])
    let l₁ : V₁.left ⟶ U₁.left :=
      pullback.lift (V₁.hom ≫ f.base) k₁ (by simpa using h₁.symm)
    let l₂ : V₂.left ⟶ U₂.left :=
      pullback.lift (V₂.hom ≫ f.base) k₂ (by simpa using h₂.symm)
    have hf := f.naturality U₁ U₂ V₁ V₂ b c l₁ l₂
      (by simp [l₁, U₁]) (by simp [l₂, U₂]) (by
        apply pullback.hom_ext <;> simp [l₁, l₂, b, U₁, U₂, Category.assoc, he])
    have hg := g.naturality W₁ W₂ U₁ U₂ a b
      (pullback.snd g.base W₁.hom) (pullback.snd g.base W₂.hom)
      (pullback.condition.symm) (pullback.condition.symm) (by simp [b])
    change _ = _
    rw [← MonoidHom.comp_assoc, hf, MonoidHom.comp_assoc, hg, ← MonoidHom.comp_assoc]
  compatibility := by
    intro W V k hk s
    dsimp only [MonoidHom.comp_apply]
    rw [f.compatibility, g.compatibility]
    have he := congrArg (fun h ↦ h (N.alpha.app (op W) s))
      (congrArg (fun h ↦ ((forget₂ CommRingCat CommMonCat).map h).hom)
      (Scheme.Hom.comp_appTop
        (pullback.lift (V.hom ≫ f.base) k (by simpa using hk.symm))
        (pullback.snd g.base W.hom)))
    rw [pullback.lift_snd] at he
    exact he.symm

/-- The constructed composition has the prescribed maps on every relative triangle.
Source: ILO VI 1.1 (blueprint: lem-sfb-log-morphism-operations).
Proof: factor the intermediate test object through its canonical pullback and use
naturality of both section maps. -/
theorem EtaleLogMap.comp_compEq {X Y Z : Scheme.{u}}
    {L : EtaleLogStructure X} {M : EtaleLogStructure Y} {N : EtaleLogStructure Z}
    (f : EtaleLogMap L M) (g : EtaleLogMap M N) : f.CompEq g (f.comp g) := by
  refine ⟨rfl, ?_⟩
  intro W V T k l m hk hl hm h
  let U : Y.Etale := Scheme.Etale.mk (pullback.fst g.base W.hom)
  let b : V ⟶ U := MorphismProperty.Over.homMk
    (pullback.lift V.hom k hk.symm) (by simp [U])
  let n : T.left ⟶ U.left := pullback.lift (T.hom ≫ f.base) m (by
    simpa only [EtaleLogMap.comp, Category.assoc] using hm.symm)
  have hf := f.naturality V U T T b (𝟙 T) l n hl (by simp [n, U]) (by
    change n = l ≫ b.left
    apply pullback.hom_ext <;> simp [n, b, Category.assoc, hl, h])
  have hg := g.naturality W W V U (𝟙 W) b k (pullback.snd g.base W.hom)
    hk pullback.condition.symm (by change b.left ≫ _ = k ≫ 𝟙 _; simp [b])
  rw [op_id, L.monoidSheaf.obj.map_id] at hf
  rw [op_id, N.monoidSheaf.obj.map_id] at hg
  change f.sectionMap U T n _ =
    (f.sectionMap V T l hl).comp (M.monoidSheaf.obj.map b.op).hom at hf
  change (M.monoidSheaf.obj.map b.op).hom.comp
    (g.sectionMap W U (pullback.snd g.base W.hom) _) = g.sectionMap W V k hk at hg
  change _ = (f.sectionMap U T n _).comp
    (g.sectionMap W U (pullback.snd g.base W.hom) _)
  rw [← hg]
  ext s
  exact congrArg (fun h ↦ h (g.sectionMap W U (pullback.snd g.base W.hom)
    pullback.condition.symm s)) hf.symm

/-- The identity uses the restriction maps on the small etale site.
Source: ILO VI 1.1 (blueprint: lem-sfb-log-morphism-operations). -/
noncomputable def EtaleLogMap.id {X : Scheme.{u}} (M : EtaleLogStructure X) :
    EtaleLogMap M M where
  base := 𝟙 X
  sectionMap W V k hk :=
    (M.monoidSheaf.obj.map (MorphismProperty.Over.homMk k (by simpa using hk) : V ⟶ W).op).hom
  naturality := by
    intro W₁ W₂ V₁ V₂ a c k₁ k₂ h₁ h₂ h
    change (M.monoidSheaf.obj.map
      (MorphismProperty.Over.homMk k₂ _ : V₂ ⟶ W₂).op ≫ M.monoidSheaf.obj.map c.op).hom = _
    rw [← Functor.map_comp]
    change _ = (M.monoidSheaf.obj.map a.op ≫ M.monoidSheaf.obj.map
      (MorphismProperty.Over.homMk k₁ _ : V₁ ⟶ W₁).op).hom
    rw [← Functor.map_comp]
    have he : (MorphismProperty.Over.homMk k₂
        (by simpa using h₂) : V₂ ⟶ W₂).op ≫ c.op =
        a.op ≫ (MorphismProperty.Over.homMk k₁
          (by simpa using h₁) : V₁ ⟶ W₁).op := by
      apply Quiver.Hom.unop_inj
      ext
      exact h
    rw [he]
  compatibility := by
    intro W V k hk s
    exact congrArg (fun q ↦ q s) (congrArg (fun q ↦ q.hom)
      (M.alpha.naturality (MorphismProperty.Over.homMk k
        (by simpa using hk) : V ⟶ W).op))
/-- Convert a general log map between the recorded fs objects without changing data.
Source: ILO VI 1.1 (blueprint: lem-sfb-log-morphism-operations). -/
def EtaleLogMap.toFSHom {X Y : FineSaturatedLogScheme.{u}}
    (f : EtaleLogMap X.logStructure Y.logStructure) : EtaleLogHom X Y where
  base := f.base
  sectionMap := f.sectionMap
  naturality := f.naturality
  compatibility := f.compatibility

/-- The identity fs log morphism.
Source: ILO VI 1.1 (blueprint: lem-sfb-log-morphism-operations). -/
noncomputable def EtaleLogHom.id (X : FineSaturatedLogScheme.{u}) : EtaleLogHom X X :=
  (EtaleLogMap.id X.logStructure).toFSHom

/-- Composition of fs log morphisms, with the actual section-map construction.
Source: ILO VI 1.1 (blueprint: lem-sfb-log-morphism-operations). -/
noncomputable def EtaleLogHom.comp {X Y Z : FineSaturatedLogScheme.{u}}
    (f : EtaleLogHom X Y) (g : EtaleLogHom Y Z) : EtaleLogHom X Z :=
  (f.toLogMap.comp g.toLogMap).toFSHom

/-- Composition has the recorded section equations for fs log schemes.
Source: ILO VI 1.1 (blueprint: lem-sfb-log-morphism-operations).
Proof: apply the general relative-triangle equation to the same data. -/
theorem EtaleLogHom.comp_compEq {X Y Z : FineSaturatedLogScheme.{u}}
    (f : EtaleLogHom X Y) (g : EtaleLogHom Y Z) : f.CompEq g (f.comp g) :=
  f.toLogMap.comp_compEq g.toLogMap

/-- The constructed identity fixes every relative test section.
Source: ILO VI 1.1 (blueprint: lem-sfb-log-morphism-operations).
Proof: both sides are the same restriction map; the scheme map is the identity. -/
theorem EtaleLogHom.id_isIdentity (X : FineSaturatedLogScheme.{u}) :
    (EtaleLogHom.id X).IsIdentity := by
  refine ⟨rfl, ?_⟩
  intro W V k hk h
  rfl

/-- Log maps are equal when their bases and all relative section maps agree.
Source: ILO VI 1.1 (blueprint: lem-sfb-log-morphism-operations).
Proof: eliminate the underlying-map equality and use function extensionality on
all section maps; the remaining fields are proofs. -/
theorem EtaleLogMap.ext {X Y : Scheme.{u}}
    {M : EtaleLogStructure X} {N : EtaleLogStructure Y} (f g : EtaleLogMap M N)
    (hb : f.base = g.base)
    (hs : ∀ W V k hk,
      f.sectionMap W V k hk = g.sectionMap W V k (hk.trans (congrArg (V.hom ≫ ·) hb))) :
    f = g := by
  cases f
  cases g
  cases hb
  congr
  funext W V k hk
  exact hs W V k hk

/-- The equations specifying a composite determine its relative section maps.
Source: ILO VI 1.1 (blueprint: lem-sfb-log-morphism-operations).
Proof: use the canonical pulled-back target test object as the intermediate object
in the triangle equation. Its two projections give exactly the definition of comp. -/
theorem EtaleLogMap.eq_comp_of_compEq {X Y Z : Scheme.{u}}
    {L : EtaleLogStructure X} {M : EtaleLogStructure Y} {N : EtaleLogStructure Z}
    {f : EtaleLogMap L M} {g : EtaleLogMap M N} {h : EtaleLogMap L N}
    (hh : f.CompEq g h) : h = f.comp g := by
  apply EtaleLogMap.ext _ _ hh.1.symm
  intro W V k hk
  let U : Y.Etale := Scheme.Etale.mk (pullback.fst g.base W.hom)
  let l : V.left ⟶ U.left := pullback.lift (V.hom ≫ f.base) k (by
    simpa only [Category.assoc, hh.1] using hk.symm)
  exact (hh.2 W U V (pullback.snd g.base W.hom) l k pullback.condition.symm
    (by simp [l, U]) hk (by simp [l])).symm

/-- The scheme map of composition is composition of scheme maps.
Source: ILO VI 1.1 (blueprint: lem-sfb-log-morphism-operations).
Proof: this is the first field of the construction. -/
@[simp] theorem EtaleLogMap.comp_base {X Y Z : Scheme.{u}}
    {L : EtaleLogStructure X} {M : EtaleLogStructure Y} {N : EtaleLogStructure Z}
    (f : EtaleLogMap L M) (g : EtaleLogMap M N) :
    (f.comp g).base = f.base ≫ g.base := rfl

/-- The scheme map of the identity is the identity.
Source: ILO VI 1.1 (blueprint: lem-sfb-log-morphism-operations).
Proof: this is the first field of the construction. -/
@[simp] theorem EtaleLogMap.id_base {X : Scheme.{u}} (M : EtaleLogStructure X) :
    (EtaleLogMap.id M).base = 𝟙 X := rfl

/-- A composite with an identity on the target is the original log map.
Source: ILO VI 1.1 (blueprint: lem-sfb-log-morphism-operations).
Proof: naturality against the relative test map is precisely the triangle equation. -/
theorem EtaleLogMap.compEq_id {X Y : Scheme.{u}}
    {M : EtaleLogStructure X} {N : EtaleLogStructure Y} (f : EtaleLogMap M N) :
    f.CompEq (EtaleLogMap.id N) f := by
  refine ⟨Category.comp_id _, ?_⟩
  intro W V T k l m hk hl hm h
  have hf := f.naturality V W T T
    (MorphismProperty.Over.homMk k (by simpa using hk)) (𝟙 T) l m hl hm (by
      change m = l ≫ k
      exact h.symm)
  rw [op_id, M.monoidSheaf.obj.map_id] at hf
  exact hf.symm

/-- A composite with an identity on the source is the original log map.
Source: ILO VI 1.1 (blueprint: lem-sfb-log-morphism-operations).
Proof: naturality in the source test object gives the triangle equation. -/
theorem EtaleLogMap.id_compEq {X Y : Scheme.{u}}
    {M : EtaleLogStructure X} {N : EtaleLogStructure Y} (f : EtaleLogMap M N) :
    (EtaleLogMap.id M).CompEq f f := by
  refine ⟨Category.id_comp _, ?_⟩
  intro W V T k l m hk hl hm h
  have hf := f.naturality W W T V (𝟙 W)
    (MorphismProperty.Over.homMk l (by simpa using hl)) m k hm hk (by
      change l ≫ k = m ≫ 𝟙 _
      simpa using h)
  rw [op_id, N.monoidSheaf.obj.map_id] at hf
  exact hf

/-- Right identity for log-map composition.
Source: ILO VI 1.1 (blueprint: lem-sfb-log-morphism-operations).
Proof: uniqueness of the composite applied to its identity triangle equations. -/
theorem EtaleLogMap.comp_id {X Y : Scheme.{u}}
    {M : EtaleLogStructure X} {N : EtaleLogStructure Y} (f : EtaleLogMap M N) :
    f.comp (EtaleLogMap.id N) = f := (EtaleLogMap.eq_comp_of_compEq f.compEq_id).symm

/-- Left identity for log-map composition.
Source: ILO VI 1.1 (blueprint: lem-sfb-log-morphism-operations).
Proof: uniqueness of the composite applied to its identity triangle equations. -/
theorem EtaleLogMap.id_comp {X Y : Scheme.{u}}
    {M : EtaleLogStructure X} {N : EtaleLogStructure Y} (f : EtaleLogMap M N) :
    (EtaleLogMap.id M).comp f = f := (EtaleLogMap.eq_comp_of_compEq f.id_compEq).symm

/-- Associativity of log-map composition.
Source: ILO VI 1.1 (blueprint: lem-sfb-log-morphism-operations).
Proof: refine a relative test diagram to successive canonical pullbacks; naturality
identifies the two composites of the same three section maps. -/
theorem EtaleLogMap.comp_assoc {X Y Z T : Scheme.{u}}
    {L : EtaleLogStructure X} {M : EtaleLogStructure Y}
    {N : EtaleLogStructure Z} {O : EtaleLogStructure T}
    (f : EtaleLogMap L M) (g : EtaleLogMap M N) (h : EtaleLogMap N O) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  apply EtaleLogMap.ext _ _ (Category.assoc _ _ _)
  intro W V k hk
  let U : Z.Etale := Scheme.Etale.mk (pullback.fst h.base W.hom)
  let R : Y.Etale := Scheme.Etale.mk (pullback.fst g.base U.hom)
  let n : V.left ⟶ U.left :=
    pullback.lift (V.hom ≫ f.base ≫ g.base) k (by
      simpa only [EtaleLogMap.comp, Category.assoc] using hk.symm)
  let m : R.left ⟶ W.left := pullback.snd g.base U.hom ≫ pullback.snd h.base W.hom
  let l : V.left ⟶ R.left :=
    pullback.lift (V.hom ≫ f.base) n (by simp [n, U])
  have hfg := (f.comp_compEq g).2 U R V (pullback.snd g.base U.hom) l n
    pullback.condition.symm (by simp [l, R]) (by simp [n, U]) (by simp [l])
  have hgh := (g.comp_compEq h).2 W U R (pullback.snd h.base W.hom)
    (pullback.snd g.base U.hom) m pullback.condition.symm pullback.condition.symm
    (by
      change (pullback.snd g.base (pullback.fst h.base W.hom) ≫
        pullback.snd h.base W.hom) ≫ W.hom =
        pullback.fst g.base (pullback.fst h.base W.hom) ≫ (g.base ≫ h.base)
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, ← pullback.condition,
        Category.assoc]) rfl
  have hfh := (f.comp_compEq (g.comp h)).2 W R V m l k
    (by
      change (pullback.snd g.base (pullback.fst h.base W.hom) ≫
        pullback.snd h.base W.hom) ≫ W.hom =
        pullback.fst g.base (pullback.fst h.base W.hom) ≫ (g.base ≫ h.base)
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, ← pullback.condition,
        Category.assoc])
    (by simp [l, R]) (by simpa only [EtaleLogMap.comp, Category.assoc] using hk)
    (by simp [l, m, n])
  change ((f.comp g).sectionMap U V n _).comp
    (h.sectionMap W U (pullback.snd h.base W.hom) _) = _
  rw [← hfg, ← hfh, ← hgh]
  exact MonoidHom.comp_assoc _ _ _

/-- Strict etale log maps compose, including their prescribed section maps.
Source: ILO VI 1.1, VIII 3.3.4(ii) (blueprint: lem-sfb-log-morphism-operations).
Proof: on every etale test object, the composite restriction map is the composite
of the two bijective restriction maps, by the relative-triangle equation. -/
theorem EtaleLogMap.strictEtale_comp {X Y Z : Scheme.{u}}
    {L : EtaleLogStructure X} {M : EtaleLogStructure Y} {N : EtaleLogStructure Z}
    (f : EtaleLogMap L M) (g : EtaleLogMap M N)
    (hf : f.IsStrictEtale) (hg : g.IsStrictEtale) : (f.comp g).IsStrictEtale := by
  obtain ⟨hf, hfb⟩ := hf
  obtain ⟨hg, hgb⟩ := hg
  have : Etale (f.comp g).base := inferInstanceAs (Etale (f.base ≫ g.base))
  refine ⟨this, ?_⟩
  intro V
  let U : Y.Etale := Scheme.Etale.mk (V.hom ≫ f.base)
  let W : Z.Etale := Scheme.Etale.mk (V.hom ≫ (f.comp g).base)
  have hfu : Function.Bijective (f.sectionMap U V (𝟙 V.left) (by simp [U])) := hfb V
  have hwu : (𝟙 V.left) ≫ W.hom = U.hom ≫ g.base := by
    change (𝟙 V.left) ≫ (V.hom ≫ (f.base ≫ g.base)) = (V.hom ≫ f.base) ≫ g.base
    exact (Category.id_comp _).trans (Category.assoc _ _ _).symm
  have hgu : Function.Bijective (g.sectionMap W U (𝟙 V.left) hwu) := by
    have hgU := hgb U
    change Function.Bijective (g.sectionMap
      (Scheme.Etale.mk ((V.hom ≫ f.base) ≫ g.base)) U (𝟙 V.left) _) at hgU
    change Function.Bijective (g.sectionMap
      (Scheme.Etale.mk (V.hom ≫ (f.base ≫ g.base))) U (𝟙 V.left) _)
    convert hgU using 1 <;> rfl
  have hc := (f.comp_compEq g).2 W U V (𝟙 V.left) (𝟙 V.left) (𝟙 V.left)
    hwu (by simp [U]) (by simp [W]) (by simp)
  rw [← hc]
  exact hfu.comp hgu

end AlgebraicGeometry
