/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
public import WeilConjectures.AlgebraicGeometry.Descent
public import WeilConjectures.AlgebraicGeometry.Modules.Endomorphism
public import WeilConjectures.AlgebraicGeometry.PicardFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Descent.IsPrestack

/-!
# Descent data for invertible modules normalized along a section

Let `f : X ⟶ S` be a morphism of schemes and let `s` choose, for every scheme `Y` over `S`, a
section `s Y` of the projection `X_Y = X ×_S Y ⟶ Y`. Let `{T i ⟶ T}` be a family of schemes over
`S` and `L i` invertible modules on `X_{T i}` whose pullbacks along the sections are trivialised
by isomorphisms `α i : (s (T i))^* L i ≅ (T i ⟶ T)^* N`. A morphism between pullbacks of the
`L i` is *normalized* if its pullback along the section is compatible with the trivialisations.

When `Γ(Y, 𝒪_Y) ⟶ Γ(X_Y, 𝒪_{X_Y})` is surjective, normalized morphisms are unique, and any
isomorphism can be rescaled by a unit to a normalized one. Consequently normalized gluing
isomorphisms automatically satisfy the cocycle condition. This is the rigidification in the proof
that the `σ`-normalized relative Picard functor is an fppf sheaf (blueprint `lem-pc-k-sheaf`).

## Main definitions

- `AlgebraicGeometry.IsSectionNormalized`: the normalization condition on a morphism.
- `AlgebraicGeometry.chosenPullbackBaseChangeMap`, `AlgebraicGeometry.chosenPullback₃BaseChangeMap`:
  the fibre products `X_{A ×_C B}` of `X_A ⟶ X_C ⟵ X_B`, and the triple fibre products, in terms
  of which descent data are written down.
- `AlgebraicGeometry.descentDataOfIsSectionNormalized`: normalized gluing isomorphisms form a
  descent datum, for any pseudofunctor in which normalized morphisms are rigid.
- `AlgebraicGeometry.normalizedDescentData`: the descent datum of sheaves of modules obtained by
  normalizing gluing isomorphisms.

## Main statements

- `AlgebraicGeometry.IsSectionNormalized.eq`: rigidity of normalized morphisms.
- `AlgebraicGeometry.exists_isSectionNormalized`: every isomorphism can be normalized.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry

open Scheme

section Normalization

variable {F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{u, u + 1}} {X S : Scheme.{u}}
  {f : X ⟶ S} (s : ∀ Y : Over S, Y.left ⟶ pullback f Y.hom) {T : Over S}
  {ι : Type*} {T' : ι → Over S} (g : ∀ i, T' i ⟶ T) {N : F.obj (.mk (op T.left))}
  {L : ∀ i, F.obj (.mk (op (pullback f (T' i).hom)))}
  (α : ∀ i, (F.map (s (T' i)).op.toLoc).toFunctor.obj
    (L i) ≅ (F.map (g i).left.op.toLoc).toFunctor.obj N)

/-- A morphism `φ : v₁^* L i ⟶ v₂^* L j` over `X_Y` is *normalized* if its pullback along the
section `s Y` is compatible with the trivialisations `α i` and `α j`. -/
def IsSectionNormalized {Y : Over S} {i j : ι} {v₁ : pullback f Y.hom ⟶ pullback f (T' i).hom}
    {v₂ : pullback f Y.hom ⟶ pullback f (T' j).hom} {t₁ : Y.left ⟶ (T' i).left}
    {t₂ : Y.left ⟶ (T' j).left} {q : Y.left ⟶ T.left}
    (h₁ : s Y ≫ v₁ = t₁ ≫ s (T' i)) (h₂ : s Y ≫ v₂ = t₂ ≫ s (T' j))
    (hq₁ : t₁ ≫ (g i).left = q) (hq₂ : t₂ ≫ (g j).left = q)
    (φ : (F.map v₁.op.toLoc).toFunctor.obj (L i) ⟶
      (F.map v₂.op.toLoc).toFunctor.obj (L j)) : Prop :=
  pullHom φ (s Y) (t₁ ≫ s (T' i)) (t₂ ≫ s (T' j)) h₁ h₂ ≫
    pullHom (α j).hom t₂ (t₂ ≫ s (T' j)) q rfl hq₂ =
  pullHom (α i).hom t₁ (t₁ ≫ s (T' i)) q rfl hq₁

variable {s g α}

/-- Normalized morphisms are stable under composition. -/
lemma IsSectionNormalized.comp {Y : Over S} {i j k : ι}
    {v₁ : pullback f Y.hom ⟶ pullback f (T' i).hom}
    {v₂ : pullback f Y.hom ⟶ pullback f (T' j).hom}
    {v₃ : pullback f Y.hom ⟶ pullback f (T' k).hom} {t₁ : Y.left ⟶ (T' i).left}
    {t₂ : Y.left ⟶ (T' j).left} {t₃ : Y.left ⟶ (T' k).left} {q : Y.left ⟶ T.left}
    {h₁ : s Y ≫ v₁ = t₁ ≫ s (T' i)} {h₂ : s Y ≫ v₂ = t₂ ≫ s (T' j)}
    {h₃ : s Y ≫ v₃ = t₃ ≫ s (T' k)}
    {hq₁ : t₁ ≫ (g i).left = q} {hq₂ : t₂ ≫ (g j).left = q} {hq₃ : t₃ ≫ (g k).left = q}
    {φ : (F.map v₁.op.toLoc).toFunctor.obj (L i) ⟶
      (F.map v₂.op.toLoc).toFunctor.obj (L j)}
    {ψ : (F.map v₂.op.toLoc).toFunctor.obj (L j) ⟶
      (F.map v₃.op.toLoc).toFunctor.obj (L k)}
    (hφ : IsSectionNormalized s g α h₁ h₂ hq₁ hq₂ φ)
    (hψ : IsSectionNormalized s g α h₂ h₃ hq₂ hq₃ ψ) :
    IsSectionNormalized s g α h₁ h₃ hq₁ hq₃ (φ ≫ ψ) := by
  unfold IsSectionNormalized at hφ hψ ⊢
  rw [pullHom_comp  φ ψ _ _ (t₂ ≫ s (T' j)) _ h₁ h₂ h₃,
    Category.assoc, hψ, hφ]

/-- Identities are normalized. -/
lemma isSectionNormalized_id {Y : Over S} {i : ι} {v₁ : pullback f Y.hom ⟶ pullback f (T' i).hom}
    {t₁ : Y.left ⟶ (T' i).left} {q : Y.left ⟶ T.left} {h₁ : s Y ≫ v₁ = t₁ ≫ s (T' i)}
    {hq₁ : t₁ ≫ (g i).left = q} :
    IsSectionNormalized s g α h₁ h₁ hq₁ hq₁
      (𝟙 ((F.map v₁.op.toLoc).toFunctor.obj (L i))) := by
  unfold IsSectionNormalized
  rw [pullHom_id_eq_id, Category.id_comp]

/-- Normalized morphisms are stable under pullback along a morphism `b : X_{Y'} ⟶ X_Y`
compatible with the sections, for instance `b = baseChangeMap f w`. -/
lemma IsSectionNormalized.pullHom {Y Y' : Over S} (w : Y' ⟶ Y) {i j : ι}
    {v₁ : pullback f Y.hom ⟶ pullback f (T' i).hom}
    {v₂ : pullback f Y.hom ⟶ pullback f (T' j).hom} {t₁ : Y.left ⟶ (T' i).left}
    {t₂ : Y.left ⟶ (T' j).left} {q : Y.left ⟶ T.left}
    {h₁ : s Y ≫ v₁ = t₁ ≫ s (T' i)} {h₂ : s Y ≫ v₂ = t₂ ≫ s (T' j)}
    {hq₁ : t₁ ≫ (g i).left = q} {hq₂ : t₂ ≫ (g j).left = q}
    {φ : (F.map v₁.op.toLoc).toFunctor.obj (L i) ⟶ (F.map v₂.op.toLoc).toFunctor.obj (L j)}
    (hφ : IsSectionNormalized s g α h₁ h₂ hq₁ hq₂ φ) (b : pullback f Y'.hom ⟶ pullback f Y.hom)
    (hb : s Y' ≫ b = w.left ≫ s Y) {v₁' : pullback f Y'.hom ⟶ pullback f (T' i).hom}
    {v₂' : pullback f Y'.hom ⟶ pullback f (T' j).hom} (hv₁ : b ≫ v₁ = v₁') (hv₂ : b ≫ v₂ = v₂')
    (h₁' : s Y' ≫ v₁' = (w.left ≫ t₁) ≫ s (T' i))
    (h₂' : s Y' ≫ v₂' = (w.left ≫ t₂) ≫ s (T' j))
    (hq₁' : (w.left ≫ t₁) ≫ (g i).left = w.left ≫ q)
    (hq₂' : (w.left ≫ t₂) ≫ (g j).left = w.left ≫ q) :
    IsSectionNormalized s g α h₁' h₂' hq₁' hq₂' (pullHom φ b v₁' v₂' hv₁ hv₂) := by
  unfold IsSectionNormalized at hφ ⊢
  rw [pullHom_pullHom, pullHom_congr_left φ hb,
    ← pullHom_pullHom φ (s Y) (t₁ ≫ s (T' i)) (t₂ ≫ s (T' j)) w.left _ _ h₁ h₂,
    ← pullHom_pullHom (α j).hom t₂ (t₂ ≫ s (T' j)) q w.left _ (w.left ≫ q) rfl hq₂,
    ← pullHom_comp, hφ, pullHom_pullHom]

/-- Being normalized only depends on the equality classes of the auxiliary morphisms `t₁`, `t₂`
and `q`. -/
lemma IsSectionNormalized.congr {Y : Over S} {i j : ι}
    {v₁ : pullback f Y.hom ⟶ pullback f (T' i).hom}
    {v₂ : pullback f Y.hom ⟶ pullback f (T' j).hom} {t₁ t₁' : Y.left ⟶ (T' i).left}
    {t₂ t₂' : Y.left ⟶ (T' j).left} {q q' : Y.left ⟶ T.left}
    {h₁ : s Y ≫ v₁ = t₁ ≫ s (T' i)} {h₂ : s Y ≫ v₂ = t₂ ≫ s (T' j)}
    {hq₁ : t₁ ≫ (g i).left = q} {hq₂ : t₂ ≫ (g j).left = q}
    {h₁' : s Y ≫ v₁ = t₁' ≫ s (T' i)} {h₂' : s Y ≫ v₂ = t₂' ≫ s (T' j)}
    {hq₁' : t₁' ≫ (g i).left = q'} {hq₂' : t₂' ≫ (g j).left = q'}
    {φ : (F.map v₁.op.toLoc).toFunctor.obj (L i) ⟶ (F.map v₂.op.toLoc).toFunctor.obj (L j)}
    (ht₁ : t₁ = t₁') (ht₂ : t₂ = t₂') (hq : q = q')
    (hφ : IsSectionNormalized s g α h₁ h₂ hq₁ hq₂ φ) :
    IsSectionNormalized s g α h₁' h₂' hq₁' hq₂' φ := by
  subst ht₁ ht₂ hq
  exact hφ

/-- Two normalized morphisms have the same pullback along the section. -/
lemma IsSectionNormalized.map_eq {Y : Over S} {i j : ι}
    {v₁ : pullback f Y.hom ⟶ pullback f (T' i).hom}
    {v₂ : pullback f Y.hom ⟶ pullback f (T' j).hom} {t₁ : Y.left ⟶ (T' i).left}
    {t₂ : Y.left ⟶ (T' j).left} {q : Y.left ⟶ T.left}
    {h₁ : s Y ≫ v₁ = t₁ ≫ s (T' i)} {h₂ : s Y ≫ v₂ = t₂ ≫ s (T' j)}
    {hq₁ : t₁ ≫ (g i).left = q} {hq₂ : t₂ ≫ (g j).left = q}
    {φ ψ : (F.map v₁.op.toLoc).toFunctor.obj (L i) ⟶ (F.map v₂.op.toLoc).toFunctor.obj (L j)}
    (hφ : IsSectionNormalized s g α h₁ h₂ hq₁ hq₂ φ)
    (hψ : IsSectionNormalized s g α h₁ h₂ hq₁ hq₂ ψ) :
    (F.map (s Y).op.toLoc).toFunctor.map φ = (F.map (s Y).op.toLoc).toFunctor.map ψ := by
  unfold IsSectionNormalized at hφ hψ
  rw [← hψ, cancel_mono] at hφ
  rw [map_eq_pullHom φ (s Y) _ _ h₁ h₂, map_eq_pullHom ψ (s Y) _ _ h₁ h₂, hφ]

end Normalization

section NormalizationModules

variable {X S : Scheme.{u}} {f : X ⟶ S} {s : ∀ Y : Over S, Y.left ⟶ pullback f Y.hom}
  {T : Over S} {ι : Type*} {T' : ι → Over S} {g : ∀ i, T' i ⟶ T}
  {N : modulesPseudofunctor.obj (.mk (op T.left))}
  {L : ∀ i, modulesPseudofunctor.obj (.mk (op (pullback f (T' i).hom)))}
  {α : ∀ i, (modulesPseudofunctor.map (s (T' i)).op.toLoc).toFunctor.obj
    (L i) ≅ (modulesPseudofunctor.map (g i).left.op.toLoc).toFunctor.obj N}

/-- **Rigidity of normalized morphisms.** If `Γ(Y, 𝒪_Y) ⟶ Γ(X_Y, 𝒪_{X_Y})` is surjective, a
normalized morphism between pullbacks of invertible modules is determined by its normalization:
two normalized morphisms, one of them an isomorphism, are equal. -/
lemma IsSectionNormalized.eq {Y : Over S} (hs : s Y ≫ pullback.snd f Y.hom = 𝟙 _)
    (hY : Function.Surjective (pullback.snd f Y.hom).appTop) {i j : ι}
    [hL : Modules.IsInvertible (X := pullback f (T' i).hom) (L i)]
    {v₁ : pullback f Y.hom ⟶ pullback f (T' i).hom}
    {v₂ : pullback f Y.hom ⟶ pullback f (T' j).hom} {t₁ : Y.left ⟶ (T' i).left}
    {t₂ : Y.left ⟶ (T' j).left} {q : Y.left ⟶ T.left}
    {h₁ : s Y ≫ v₁ = t₁ ≫ s (T' i)} {h₂ : s Y ≫ v₂ = t₂ ≫ s (T' j)}
    {hq₁ : t₁ ≫ (g i).left = q} {hq₂ : t₂ ≫ (g j).left = q}
    {φ ψ : (modulesPseudofunctor.map v₁.op.toLoc).toFunctor.obj (L i) ⟶
      (modulesPseudofunctor.map v₂.op.toLoc).toFunctor.obj (L j)} [IsIso ψ]
    (hφ : IsSectionNormalized s g α h₁ h₂ hq₁ hq₂ φ)
    (hψ : IsSectionNormalized s g α h₁ h₂ hq₁ hq₂ ψ) :
    φ = ψ := by
  have : ((Modules.pullback v₁).obj (L i)).IsInvertible := inferInstance
  exact Modules.eq_of_pullback_map_eq (A := (Modules.pullback v₁).obj (L i))
    (pullback.snd f Y.hom) (s Y) hs hY φ ψ
    (hφ.map_eq hψ)

/-- Pulling back multiplication by a global function along `b` gives multiplication by its
pullback. -/
lemma pullHom_smulHom {Y Y' Z : Scheme.{u}} (M : modulesPseudofunctor.obj (.mk (op Z)))
    (f₁ : Y ⟶ Z) (b : Y' ⟶ Y) (bf : Y' ⟶ Z) (h : b ≫ f₁ = bf) (u : Γ(Y, ⊤)) :
    pullHom (F := modulesPseudofunctor)
      (Modules.smulHom ((modulesPseudofunctor.map f₁.op.toLoc).toFunctor.obj M) u) b bf bf h h =
      Modules.smulHom ((modulesPseudofunctor.map bf.op.toLoc).toFunctor.obj M) (b.appTop u) := by
  dsimp only [pullHom]
  erw [Modules.pullback_map_smulHom, ← Modules.smulHom_naturality_assoc]
  rw [Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id]
  rfl

/-- **Normalizing an isomorphism.** Any isomorphism between pullbacks of invertible modules can be
rescaled by a unit to a normalized isomorphism. -/
lemma exists_isSectionNormalized {Y : Over S} (hs : s Y ≫ pullback.snd f Y.hom = 𝟙 _) {i j : ι}
    [hL : Modules.IsInvertible (X := pullback f (T' i).hom) (L i)]
    {v₁ : pullback f Y.hom ⟶ pullback f (T' i).hom}
    {v₂ : pullback f Y.hom ⟶ pullback f (T' j).hom} {t₁ : Y.left ⟶ (T' i).left}
    {t₂ : Y.left ⟶ (T' j).left} {q : Y.left ⟶ T.left}
    (h₁ : s Y ≫ v₁ = t₁ ≫ s (T' i)) (h₂ : s Y ≫ v₂ = t₂ ≫ s (T' j))
    (hq₁ : t₁ ≫ (g i).left = q) (hq₂ : t₂ ≫ (g j).left = q)
    (e : (modulesPseudofunctor.map v₁.op.toLoc).toFunctor.obj (L i) ≅
      (modulesPseudofunctor.map v₂.op.toLoc).toFunctor.obj (L j)) :
    ∃ φ, IsIso φ ∧ IsSectionNormalized s g α h₁ h₂ hq₁ hq₂ φ := by
  let Pi := pullHom (F := modulesPseudofunctor) (α i).hom t₁ (t₁ ≫ s (T' i)) q rfl hq₁
  let Pj := pullHom (F := modulesPseudofunctor) (α j).hom t₂ (t₂ ≫ s (T' j)) q rfl hq₂
  let E := pullHom (F := modulesPseudofunctor) e.hom (s Y) (t₁ ≫ s (T' i)) (t₂ ≫ s (T' j)) h₁ h₂
  have : IsIso Pi := isIso_pullHom _ _ _ _ _ _
  have : IsIso Pj := isIso_pullHom _ _ _ _ _ _
  have : IsIso E := isIso_pullHom _ _ _ _ _ _
  let A : Y.left.Modules :=
    (modulesPseudofunctor.map (t₁ ≫ s (T' i)).op.toLoc).toFunctor.obj (L i)
  have : A.IsInvertible := inferInstanceAs ((Modules.pullback _).obj (L i)).IsInvertible
  let δ : A ⟶ A := E ≫ Pj ≫ inv Pi
  have : IsIso δ := by dsimp only [δ]; infer_instance
  obtain ⟨c, hc⟩ := Modules.exists_eq_smulHom A (inv δ)
  obtain ⟨c', hc'⟩ := Modules.exists_eq_smulHom A δ
  have hcc : c * c' = 1 := by
    refine Modules.eq_of_smulHom_eq A ?_
    rw [Modules.smulHom_mul, Modules.smulHom_one, ← hc, ← hc', IsIso.hom_inv_id]
  have hcc' : c' * c = 1 := by rw [mul_comm, hcc]
  let B : (pullback f Y.hom).Modules :=
    (modulesPseudofunctor.map v₁.op.toLoc).toFunctor.obj (L i)
  let u := (pullback.snd f Y.hom).appTop c
  let u' := (pullback.snd f Y.hom).appTop c'
  have hsu : (s Y).appTop u = c := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, hs]
    rfl
  have : IsIso (B.smulHom u) := ⟨B.smulHom u', by
    rw [← Modules.smulHom_mul, ← map_mul, hcc', map_one, Modules.smulHom_one], by
    rw [← Modules.smulHom_mul, ← map_mul, hcc, map_one, Modules.smulHom_one]⟩
  refine ⟨B.smulHom u ≫ e.hom, inferInstance, ?_⟩
  unfold IsSectionNormalized
  rw [pullHom_comp (F := modulesPseudofunctor) _ _ _ _ (t₁ ≫ s (T' i)) _ h₁ h₁ h₂,
    pullHom_smulHom, hsu, ← hc, Category.assoc]
  change inv δ ≫ E ≫ Pj = Pi
  simp [δ]

end NormalizationModules

section ChosenPullbacks

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The fibre product of `X_A ⟶ X_C ⟵ X_B` for morphisms `u : A ⟶ C`, `v : B ⟶ C` of schemes
over `S`, chosen to be `X_{A ×_C B}`. -/
noncomputable abbrev chosenPullbackBaseChangeMap {A B C : Over S} (u : A ⟶ C) (v : B ⟶ C) :
    ChosenPullback (baseChangeMap f u) (baseChangeMap f v) where
  pullback := pullback f (pullback u v).hom
  p₁ := baseChangeMap f (pullback.fst u v)
  p₂ := baseChangeMap f (pullback.snd u v)
  condition := (isPullback_baseChangeMap_of_isPullback f
    ((IsPullback.of_hasPullback u v).map (Over.forget S))).w
  isLimit := (isPullback_baseChangeMap_of_isPullback f
    ((IsPullback.of_hasPullback u v).map (Over.forget S))).isLimit

variable {T : Over S} {ι : Type*} {T' : ι → Over S} (g : ∀ i, T' i ⟶ T)

/-- The triple fibre products `X_{T i ×_T T j ×_T T k}`. -/
noncomputable abbrev chosenPullback₃BaseChangeMap (i j k : ι) :
    ChosenPullback₃ (chosenPullbackBaseChangeMap f (g i) (g j))
      (chosenPullbackBaseChangeMap f (g j) (g k)) (chosenPullbackBaseChangeMap f (g i) (g k)) where
  chosenPullback := chosenPullbackBaseChangeMap f (pullback.snd (g i) (g j))
    (pullback.fst (g j) (g k))
  l :=
    { f := baseChangeMap f (pullback.lift (pullback.fst _ _ ≫ pullback.fst (g i) (g j))
        (pullback.snd _ _ ≫ pullback.snd (g j) (g k)) (by
          simp [pullback.condition, pullback.condition_assoc]))
      f_p₁ := by
        simp only [chosenPullbackBaseChangeMap, ← baseChangeMap_comp, pullback.lift_fst]
      f_p₂ := by
        simp only [chosenPullbackBaseChangeMap, ← baseChangeMap_comp, pullback.lift_snd]
      f_p := by
        simp only [chosenPullbackBaseChangeMap, ← baseChangeMap_comp, pullback.lift_fst_assoc,
          Category.assoc] }

end ChosenPullbacks

section DescentDatum

variable {F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{u, u + 1}} {X S : Scheme.{u}}
  {f : X ⟶ S} {s : ∀ Y : Over S, Y.left ⟶ pullback f Y.hom}
  (hsb : ∀ {Y Z : Over S} (w : Y ⟶ Z), s Y ≫ baseChangeMap f w = w.left ≫ s Z)
  {T : Over S} {ι : Type*} {T' : ι → Over S} {g : ∀ i, T' i ⟶ T}
  {N : F.obj (.mk (op T.left))} {L : ∀ i, F.obj (.mk (op (pullback f (T' i).hom)))}
  {α : ∀ i, (F.map (s (T' i)).op.toLoc).toFunctor.obj (L i) ≅
    (F.map (g i).left.op.toLoc).toFunctor.obj N}
  (hrigid : ∀ {Y : Over S} {i j : ι} {v₁ : pullback f Y.hom ⟶ pullback f (T' i).hom}
    {v₂ : pullback f Y.hom ⟶ pullback f (T' j).hom} {t₁ : Y.left ⟶ (T' i).left}
    {t₂ : Y.left ⟶ (T' j).left} {q : Y.left ⟶ T.left}
    {h₁ : s Y ≫ v₁ = t₁ ≫ s (T' i)} {h₂ : s Y ≫ v₂ = t₂ ≫ s (T' j)}
    {hq₁ : t₁ ≫ (g i).left = q} {hq₂ : t₂ ≫ (g j).left = q}
    {φ ψ : (F.map v₁.op.toLoc).toFunctor.obj (L i) ⟶ (F.map v₂.op.toLoc).toFunctor.obj (L j)},
    IsIso ψ → IsSectionNormalized s g α h₁ h₂ hq₁ hq₂ φ →
      IsSectionNormalized s g α h₁ h₂ hq₁ hq₂ ψ → φ = ψ)
  (hom : ∀ i j,
    (F.map (chosenPullbackBaseChangeMap f (g i) (g j)).p₁.op.toLoc).toFunctor.obj (L i) ⟶
      (F.map (chosenPullbackBaseChangeMap f (g i) (g j)).p₂.op.toLoc).toFunctor.obj (L j))
  [hiso : ∀ i j, IsIso (hom i j)]
  (hhom : ∀ i j, IsSectionNormalized s g α (hsb (pullback.fst (g i) (g j)))
      (hsb (pullback.snd (g i) (g j))) (q := (pullback.fst (g i) (g j) ≫ g i).left) rfl
      (by rw [← Over.comp_left, ← pullback.condition]) (hom i j))

omit hiso in
include hhom in
/-- The pullbacks of normalized gluing morphisms to fibre products are normalized. -/
lemma isSectionNormalized_pullHom {i j : ι} {Y : Over S}
    (w : Y ⟶ pullback (g i) (g j)) {v₁ : pullback f Y.hom ⟶ pullback f (T' i).hom}
    {v₂ : pullback f Y.hom ⟶ pullback f (T' j).hom}
    (hv₁ : baseChangeMap f w ≫ (chosenPullbackBaseChangeMap f (g i) (g j)).p₁ = v₁)
    (hv₂ : baseChangeMap f w ≫ (chosenPullbackBaseChangeMap f (g i) (g j)).p₂ = v₂)
    {t₁ : Y.left ⟶ (T' i).left} {t₂ : Y.left ⟶ (T' j).left} {q : Y.left ⟶ T.left}
    (ht₁ : (w ≫ pullback.fst (g i) (g j)).left = t₁)
    (ht₂ : (w ≫ pullback.snd (g i) (g j)).left = t₂)
    (hq : (w ≫ pullback.fst (g i) (g j) ≫ g i).left = q)
    (h₁ : s Y ≫ v₁ = t₁ ≫ s (T' i)) (h₂ : s Y ≫ v₂ = t₂ ≫ s (T' j))
    (hq₁ : t₁ ≫ (g i).left = q) (hq₂ : t₂ ≫ (g j).left = q) :
    IsSectionNormalized s g α h₁ h₂ hq₁ hq₂ (pullHom (hom i j) (baseChangeMap f w) v₁ v₂ hv₁ hv₂) :=
  ((hhom i j).pullHom w (baseChangeMap f w) (hsb w) hv₁ hv₂
    (by rw [← hv₁, ← Category.assoc, hsb, Category.assoc, hsb, Category.assoc])
    (by rw [← hv₂, ← Category.assoc, hsb, Category.assoc, hsb, Category.assoc]) rfl
    (by rw [Category.assoc, ← Over.comp_left, ← pullback.condition])).congr ht₁ ht₂ hq

include hrigid hhom in
/-- The descent datum given by normalized gluing isomorphisms: the cocycle condition holds by
rigidity. -/
noncomputable def descentDataOfIsSectionNormalized :
    F.DescentData' (fun i j ↦ chosenPullbackBaseChangeMap f (g i) (g j))
      (fun i j k ↦ chosenPullback₃BaseChangeMap f g i j k) where
  obj := L
  hom := hom
  pullHom'_hom_self i := by
    let Δ : T' i ⟶ pullback (g i) (g i) := pullback.lift (𝟙 _) (𝟙 _) rfl
    rw [Pseudofunctor.DescentData'.pullHom'_eq_pullHom _ _ _ _ (baseChangeMap f Δ) (by simp)
      (by simp) (by simp [← baseChangeMap_comp, Δ]) (by simp [← baseChangeMap_comp, Δ])]
    exact hrigid inferInstance
      (isSectionNormalized_pullHom hsb hom hhom Δ _ _ (t₁ := 𝟙 _) (t₂ := 𝟙 _)
        (q := (g i).left) (by simp [Δ]) (by simp [Δ]) (by simp [Δ]) (by simp) (by simp)
        (by simp) (by simp))
      isSectionNormalized_id
  pullHom'_hom_comp i j k := by
    rw [Pseudofunctor.DescentData'.pullHom'₁₂_eq_pullHom_of_chosenPullback₃,
      Pseudofunctor.DescentData'.pullHom'₂₃_eq_pullHom_of_chosenPullback₃,
      Pseudofunctor.DescentData'.pullHom'₁₃_eq_pullHom_of_chosenPullback₃]
    let a : pullback (pullback.snd (g i) (g j)) (pullback.fst (g j) (g k)) ⟶
      pullback (g i) (g j) := pullback.fst _ _
    let b : pullback (pullback.snd (g i) (g j)) (pullback.fst (g j) (g k)) ⟶
      pullback (g j) (g k) := pullback.snd _ _
    let c : pullback (pullback.snd (g i) (g j)) (pullback.fst (g j) (g k)) ⟶
      pullback (g i) (g k) := pullback.lift (a ≫ pullback.fst _ _) (b ≫ pullback.snd _ _)
        (by simp [a, b, pullback.condition, pullback.condition_assoc])
    have e₂ : (b ≫ pullback.fst (g j) (g k)).left = (a ≫ pullback.snd (g i) (g j)).left :=
      congrArg CommaMorphism.left pullback.condition.symm
    have eq₂ : (b ≫ pullback.fst (g j) (g k) ≫ g j).left =
        (a ≫ pullback.fst (g i) (g j) ≫ g i).left := by
      refine congrArg CommaMorphism.left ?_
      rw [← Category.assoc, ← pullback.condition, Category.assoc, ← pullback.condition]
    have ec₁ : (c ≫ pullback.fst (g i) (g k)).left = (a ≫ pullback.fst (g i) (g j)).left := by
      simp [c]
    have ec₃ : (c ≫ pullback.snd (g i) (g k)).left = (b ≫ pullback.snd (g j) (g k)).left := by
      simp [c]
    have eqc : (c ≫ pullback.fst (g i) (g k) ≫ g i).left =
        (a ≫ pullback.fst (g i) (g j) ≫ g i).left := by
      simp [c]
    have h₁ : s _ ≫ (chosenPullback₃BaseChangeMap f g i j k).p₁ =
        (a ≫ pullback.fst (g i) (g j)).left ≫ s (T' i) := by
      change s _ ≫ baseChangeMap f a ≫ baseChangeMap f _ = _
      rw [← baseChangeMap_comp, hsb]
    have h₂ : s _ ≫ (chosenPullback₃BaseChangeMap f g i j k).p₂ =
        (a ≫ pullback.snd (g i) (g j)).left ≫ s (T' j) := by
      change s _ ≫ baseChangeMap f a ≫ baseChangeMap f _ = _
      rw [← baseChangeMap_comp, hsb]
    have h₃ : s _ ≫ (chosenPullback₃BaseChangeMap f g i j k).p₃ =
        (b ≫ pullback.snd (g j) (g k)).left ≫ s (T' k) := by
      change s _ ≫ baseChangeMap f b ≫ baseChangeMap f _ = _
      rw [← baseChangeMap_comp, hsb]
    have hq₂ : (a ≫ pullback.snd (g i) (g j)).left ≫ (g j).left =
        (a ≫ pullback.fst (g i) (g j) ≫ g i).left := by
      rw [← e₂, ← eq₂]
      rfl
    have hq₃ : (b ≫ pullback.snd (g j) (g k)).left ≫ (g k).left =
        (a ≫ pullback.fst (g i) (g j) ≫ g i).left := by
      rw [← eq₂, ← Over.comp_left, Category.assoc, ← pullback.condition]
    exact hrigid inferInstance
      ((isSectionNormalized_pullHom hsb hom hhom a _ _ rfl rfl rfl h₁ h₂ rfl hq₂).comp
        (isSectionNormalized_pullHom hsb hom hhom b _ _ e₂ rfl eq₂ h₂ h₃ hq₂ hq₃))
      (isSectionNormalized_pullHom hsb hom hhom c _ _ ec₁ ec₃ eqc h₁ h₃ rfl hq₃)

end DescentDatum

section DescentDatumModules

variable {X S : Scheme.{u}} {f : X ⟶ S} {s : ∀ Y : Over S, Y.left ⟶ pullback f Y.hom}
  (hs : ∀ Y, s Y ≫ pullback.snd f Y.hom = 𝟙 _)
  (hsb : ∀ {Y Z : Over S} (w : Y ⟶ Z), s Y ≫ baseChangeMap f w = w.left ≫ s Z)
  (hsurj : ∀ Y : Over S, Function.Surjective (pullback.snd f Y.hom).appTop)
  {T : Over S} {ι : Type*} {T' : ι → Over S} {g : ∀ i, T' i ⟶ T}
  {N : modulesPseudofunctor.obj (.mk (op T.left))}
  {L : ∀ i, modulesPseudofunctor.obj (.mk (op (pullback f (T' i).hom)))}
  [hL : ∀ i, Modules.IsInvertible (X := pullback f (T' i).hom) (L i)]
  (α : ∀ i, (modulesPseudofunctor.map (s (T' i)).op.toLoc).toFunctor.obj
    (L i) ≅ (modulesPseudofunctor.map (g i).left.op.toLoc).toFunctor.obj N)
  (e : ∀ i j,
    (modulesPseudofunctor.map (chosenPullbackBaseChangeMap f (g i) (g j)).p₁.op.toLoc).toFunctor.obj
      (L i) ≅
    (modulesPseudofunctor.map (chosenPullbackBaseChangeMap f (g i) (g j)).p₂.op.toLoc).toFunctor.obj
      (L j))

include hs hsb e in
/-- There are normalized gluing isomorphisms on the double overlaps. -/
lemma exists_isSectionNormalized_gluing (i j : ι) :
    ∃ φ, IsIso φ ∧ IsSectionNormalized s g α (hsb (pullback.fst (g i) (g j)))
      (hsb (pullback.snd (g i) (g j))) (q := (pullback.fst (g i) (g j) ≫ g i).left) rfl
      (by rw [← Over.comp_left, ← pullback.condition]) φ :=
  exists_isSectionNormalized (hs _) _ _ _ _ (e i j)

/-- The normalized gluing isomorphisms. -/
noncomputable def normalizedGluing (i j : ι) :
    (modulesPseudofunctor.map (chosenPullbackBaseChangeMap f (g i) (g j)).p₁.op.toLoc).toFunctor.obj
      (L i) ⟶
    (modulesPseudofunctor.map (chosenPullbackBaseChangeMap f (g i) (g j)).p₂.op.toLoc).toFunctor.obj
      (L j) :=
  (exists_isSectionNormalized_gluing hs hsb α e i j).choose

instance (i j : ι) : IsIso (normalizedGluing hs hsb α e i j) :=
  (exists_isSectionNormalized_gluing hs hsb α e i j).choose_spec.1

/-- The descent datum, relative to the family `X_{T i} ⟶ X_T`, formed by the modules `L i` and
the normalized gluing isomorphisms `normalizedGluing`. -/
noncomputable def normalizedDescentData :
    modulesPseudofunctor.DescentData' (fun i j ↦ chosenPullbackBaseChangeMap f (g i) (g j))
      (fun i j k ↦ chosenPullback₃BaseChangeMap f g i j k) :=
  descentDataOfIsSectionNormalized hsb (α := α)
    (fun hψ hφ hψ' ↦ have := hψ; IsSectionNormalized.eq (hs _) (hsurj _) hφ hψ')
    (normalizedGluing hs hsb α e)
    (fun i j ↦ (exists_isSectionNormalized_gluing hs hsb α e i j).choose_spec.2)

end DescentDatumModules

end AlgebraicGeometry
