/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.ModulePointFunctions
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit

/-!
# Sections of constant sheaves as locally constant functions

For a scheme `X` and a `Λ`-module `M`, the constant sheaf `M_X` on the small étale site embeds
into the sheaf of `M`-valued functions on points
(`AlgebraicGeometry.Scheme.moduleConstantSheafToPointFunctionSheaf`). We show that its sections
over an étale `X`-scheme `V` are exactly the locally constant functions on `V`, and compute the
map `f₁_* M ⟶ f₂_* M` pulling back sections along a morphism `q` over the base in terms of
functions: it is precomposition with the base change of `q`.

## Main statements

- `AlgebraicGeometry.Scheme.exists_moduleConstantSheafToPointFunctionSheaf_app_eq`: every locally
  constant function is a section of the constant sheaf.
- `AlgebraicGeometry.Etale.constantSheafPullbackMap`: the morphism `(p₂)_* M ⟶ (p₁)_* M` for
  `q : Y₁ ⟶ Y₂` with `q ≫ p₂ = p₁`, and
  `AlgebraicGeometry.Etale.constantSheafPullbackMap_apply`: its effect on functions.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] (M : ModuleCat.{u + 1} Λ)

namespace Scheme

variable (X : Scheme.{u})

/-- The sections of the constant sheaf embed into the functions on points. -/
lemma injective_moduleConstantSheafToPointFunctionSheaf_app (V : X.Etale) :
    Function.Injective ((X.moduleConstantSheafToPointFunctionSheaf M).hom.app (op V)) := by
  have : Mono ((sheafToPresheaf _ _).map (X.moduleConstantSheafToPointFunctionSheaf M)) :=
    Functor.map_mono _ _
  have : Mono ((X.moduleConstantSheafToPointFunctionSheaf M).hom.app (op V)) :=
    (NatTrans.mono_iff_mono_app _).1 this (op V)
  exact (ModuleCat.mono_iff_injective _).1 this

/-- **Sections of the constant sheaf are locally constant functions.** -/
lemma isLocallyConstant_moduleConstantSheafToPointFunctionSheaf_app (V : X.Etale)
    (σ : ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M).obj.obj (op V)) :
    IsLocallyConstant ((X.moduleConstantSheafToPointFunctionSheaf M).hom.app (op V) σ :
      V.left → M) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  obtain ⟨W, g, w, ⟨m, hm⟩, hgw⟩ := exists_of_mem_smallEtaleTopology
    (Presheaf.imageSieve_mem X.smallEtaleTopology
      (CategoryTheory.toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)) σ) x
  have hD (w' : W.left) :
      ((X.moduleConstantSheafToPointFunctionSheaf M).hom.app (op V) σ : V.left → M)
        (g.left w') = m := by
    have h₁ := congrArg
      (fun s ↦ (X.moduleConstantSheafToPointFunctionSheaf M).hom.app (op W) s w') hm
    have h₂ := NatTrans.naturality_apply
      (X.moduleConstantSheafToPointFunctionSheaf M).hom g.op σ
    simp only at h₁
    rw [moduleConstantSheafToPointFunctionSheaf_app_toSheafify] at h₁
    exact (congrFun h₂ w').symm.trans h₁.symm
  have : AlgebraicGeometry.Etale g.left := by
    have : AlgebraicGeometry.Etale (g.left ≫ V.hom) := by
      rw [show g.left ≫ V.hom = W.hom from CategoryTheory.Over.w ((Etale.forget X).map g)]
      exact W.prop
    exact AlgebraicGeometry.Etale.of_comp g.left V.hom
  refine ⟨Set.range g.left, g.left.isOpenMap.isOpen_range, ⟨w, hgw⟩, ?_⟩
  rintro _ ⟨w', rfl⟩
  rw [hD, ← hgw, hD]

/-- **Locally constant functions are sections of the constant sheaf.** -/
lemma exists_moduleConstantSheafToPointFunctionSheaf_app_eq (V : X.Etale) (f : V.left → M)
    (hf : IsLocallyConstant f) :
    ∃ s, (X.moduleConstantSheafToPointFunctionSheaf M).hom.app (op V) s = f := by
  let G := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  let ψ := X.moduleConstantSheafToPointFunctionSheaf M
  have hG := (Presheaf.isSheaf_iff_isSheaf_forget X.smallEtaleTopology G.obj
    (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).1 G.property
  rw [isSheaf_iff_isSheaf_of_type] at hG
  let S : Sieve V :=
    { arrows := fun W g ↦ ∃ a, ψ.hom.app (op W) a = fun w ↦ f (g.left w)
      downward_closed := by
        rintro W W' g ⟨a, ha⟩ k
        refine ⟨G.obj.map k.op a, ?_⟩
        rw [NatTrans.naturality_apply ψ.hom k.op a, ha]
        rfl }
  have hS : S ∈ X.smallEtaleTopology V := by
    refine (Scheme.mem_smallEtaleTopology_iff _).2 fun x ↦ ?_
    let O : V.left.Opens := ⟨f ⁻¹' {f x}, hf.isOpen_fiber _⟩
    refine ⟨Etale.ofOpens V O, Etale.ofOpensι V O, ⟨(CategoryTheory.toSheafify
      X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app _ (f x), ?_⟩, ?_⟩
    · rw [moduleConstantSheafToPointFunctionSheaf_app_toSheafify]
      funext w
      exact (show O.ι w ∈ (O : Set V.left) by rw [Scheme.Opens.ι_apply]; exact w.2).symm
    · exact ⟨⟨x, rfl⟩, rfl⟩
  choose a ha using fun (W : X.Etale) (g : W ⟶ V) (hg : S g) ↦ hg
  let x : Presieve.FamilyOfElements (G.obj ⋙ CategoryTheory.forget _) S.arrows :=
    fun W g hg ↦ a W g hg
  have hx : x.Compatible := by
    intro W₁ W₂ W g₁ g₂ f₁ f₂ hf₁ hf₂ hcomp
    apply injective_moduleConstantSheafToPointFunctionSheaf_app M X W
    change ψ.hom.app (op W) (G.obj.map g₁.op (a _ f₁ hf₁)) =
      ψ.hom.app (op W) (G.obj.map g₂.op (a _ f₂ hf₂))
    rw [NatTrans.naturality_apply ψ.hom g₁.op, NatTrans.naturality_apply ψ.hom g₂.op, ha, ha]
    funext w
    change f (f₁.left (g₁.left w)) = f (f₂.left (g₂.left w))
    exact congrArg (fun k : W ⟶ V ↦ f (k.left w)) hcomp
  refine ⟨(hG S hS).amalgamate x hx, funext fun y ↦ ?_⟩
  obtain ⟨W, g, w, hg, rfl⟩ := exists_of_mem_smallEtaleTopology hS y
  have h₁ := (hG S hS).valid_glue hx g hg
  have h₂ := NatTrans.naturality_apply ψ.hom g.op ((hG S hS).amalgamate x hx)
  have h₃ := congrFun (h₂.symm.trans ((congrArg (ψ.hom.app (op W)) h₁).trans (ha W g hg))) w
  exact h₃

end Scheme

namespace Etale

/-- The module version of restriction of functions on points along `g : Z ⟶ X`: the map of
sheaves `(V → M) ⟶ (V ×_X Z → M)` given by precomposition with the first projection. -/
noncomputable def modulePointFunctionSheafToLowerStar {X Z : Scheme.{u}} (g : Z ⟶ X) :
    X.modulePointFunctionSheaf M ⟶
      (g)_*[ModuleCat.{u + 1} Λ].obj (Z.modulePointFunctionSheaf M) :=
  ⟨{ app V := ModuleCat.ofHom
        { toFun D z := D (pullback.fst V.unop.hom g z)
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
     naturality {V W} φ := by
      ext D
      funext z
      exact congrArg D (Scheme.overPullback_map_left_fst g φ.unop z).symm }⟩

/-- The unit `M_Y ⟶ g_* M_Z` on functions: precomposition with the first projection. -/
lemma constantSheafUnit_comp_lowerStar_map {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    constantSheafUnit g M ≫ (g)_*[ModuleCat.{u + 1} Λ].map
      (Z.moduleConstantSheafToPointFunctionSheaf M) =
      Y.moduleConstantSheafToPointFunctionSheaf M ≫ modulePointFunctionSheafToLowerStar M g := by
  refine Sheaf.hom_ext (sheafify_hom_ext _ _ _
    ((g)_*[ModuleCat.{u + 1} Λ].obj (Z.modulePointFunctionSheaf M)).property ?_)
  ext V m
  induction V using Opposite.rec with | op V => ?_
  change ((Z.moduleConstantSheafToPointFunctionSheaf M).hom.app _)
      ((constantSheafUnit g M).hom.app (op V) (((CategoryTheory.toSheafify
        Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).app (op V)) m)) =
    ((modulePointFunctionSheafToLowerStar M g).hom.app (op V))
      ((Y.moduleConstantSheafToPointFunctionSheaf M).hom.app (op V)
        (((CategoryTheory.toSheafify Y.smallEtaleTopology
          ((Functor.const Y.Etaleᵒᵖ).obj M)).app (op V)) m))
  rw [constantSheafUnit_app_toSheafify, moduleConstantSheafToPointFunctionSheaf_app_toSheafify]
  exact moduleConstantSheafToPointFunctionSheaf_app_toSheafify Z M _ m

/-- The unit `M_Y ⟶ g_* M_Z` on functions: a section over `V` with function `D` is sent to the
section over `V ×_Y Z` with function `D ∘ pr₁`. -/
lemma moduleConstantSheafToPointFunctionSheaf_constantSheafUnit_app {Z Y : Scheme.{u}}
    (g : Z ⟶ Y) (V : Y.Etale)
    (t : ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M).obj.obj (op V))
    (z : ↥(pullback V.hom g)) :
    (Z.moduleConstantSheafToPointFunctionSheaf M).hom.app
        (op ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g).obj V))
      ((constantSheafUnit g M).hom.app (op V) t) z =
      (Y.moduleConstantSheafToPointFunctionSheaf M).hom.app (op V) t (pullback.fst V.hom g z) :=
  congrFun (congrArg (fun φ ↦ φ.hom.app (op V) t)
    (constantSheafUnit_comp_lowerStar_map M g)) z

variable {X Y₁ Y₂ : Scheme.{u}} (p₁ : Y₁ ⟶ X) (p₂ : Y₂ ⟶ X) (q : Y₁ ⟶ Y₂)
  (h : q ≫ p₂ = p₁)

/-- For `q : Y₁ ⟶ Y₂` over `X`, the morphism `(p₂)_* M ⟶ (p₁)_* M` pulling back sections of
the constant sheaf along `q`. -/
noncomputable def constantSheafPullbackMap :
    (p₂)_*[ModuleCat.{u + 1} Λ].obj
        ((constantSheaf Y₂.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ⟶
      (p₁)_*[ModuleCat.{u + 1} Λ].obj
        ((constantSheaf Y₁.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
  (p₂)_*[ModuleCat.{u + 1} Λ].map (constantSheafUnit q M) ≫
    (lowerStarComp (ModuleCat.{u + 1} Λ) q p₂ p₁ h.symm).hom.app _

lemma constantSheafPullbackMap_congr {q' : Y₁ ⟶ Y₂} (hq : q = q') (h' : q' ≫ p₂ = p₁) :
    constantSheafPullbackMap M p₁ p₂ q h = constantSheafPullbackMap M p₁ p₂ q' h' := by
  subst hq
  rfl

/-- The base change `V ×_X Y₁ ⟶ V ×_X Y₂` of `q`. -/
noncomputable abbrev pullbackLiftOfOver (V : X.Etale) :
    pullback V.hom p₁ ⟶ pullback V.hom p₂ :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ q)
    (by rw [Category.assoc, h, pullback.condition])

/-- **Pulling back sections along `q`, on functions**: precomposition with the base change of
`q`. -/
lemma constantSheafPullbackMap_apply (V : X.Etale)
    (t : ((constantSheaf Y₂.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M).obj.obj
      (op ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ p₂).obj V)))
    (z : ↥(pullback V.hom p₁)) :
    (Y₁.moduleConstantSheafToPointFunctionSheaf M).hom.app
        (op ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ p₁).obj V))
      ((constantSheafPullbackMap M p₁ p₂ q h).hom.app (op V) t) z =
      (Y₂.moduleConstantSheafToPointFunctionSheaf M).hom.app
        (op ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ p₂).obj V)) t
        (pullbackLiftOfOver p₁ p₂ q h V z) := by
  let e := (MorphismProperty.Over.pullbackComp (P := @AlgebraicGeometry.Etale) (Q := ⊤) q p₂ p₁
    h.symm).hom.app V
  have h₁ : (constantSheafPullbackMap M p₁ p₂ q h).hom.app (op V) t =
      ((constantSheaf Y₁.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M).obj.map e.op
        ((constantSheafUnit q M).hom.app _ t) := by
    change ((lowerStarComp (ModuleCat.{u + 1} Λ) q p₂ p₁ h.symm).hom.app _).hom.app (op V)
      ((constantSheafUnit q M).hom.app _ t) = _
    rw [lowerStarComp_hom_app_hom_app]
    rfl
  rw [h₁]
  refine (congrFun (NatTrans.naturality_apply (Y₁.moduleConstantSheafToPointFunctionSheaf M).hom
    e.op ((constantSheafUnit q M).hom.app _ t)) z).trans ?_
  refine (moduleConstantSheafToPointFunctionSheaf_constantSheafUnit_app M q _ t
    (e.left z)).trans ?_
  have key : e.left ≫ pullback.fst _ q = pullbackLiftOfOver p₁ p₂ q h V := by
    apply pullback.hom_ext
    · simp only [e, MorphismProperty.Over.pullbackComp_hom_app_left,
        Category.assoc, pullback.lift_fst]
      erw [pullbackLeftPullbackSndIso_inv_fst]
      simp
    · simp only [e, MorphismProperty.Over.pullbackComp_hom_app_left,
        Category.assoc, pullback.lift_snd]
      erw [pullbackLeftPullbackSndIso_inv_fst_snd]
      simp
  have hz : pullback.fst _ q (e.left z) = pullbackLiftOfOver p₁ p₂ q h V z := by
    rw [← key]
    rfl
  exact congrArg _ hz

/-- Two morphisms into `(p₁)_* M` agreeing on functions agree. -/
lemma hom_ext_lowerStar_constantSheaf {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {a b : G ⟶ (p₁)_*[ModuleCat.{u + 1} Λ].obj
      ((constantSheaf Y₁.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)}
    (hab : ∀ (V : X.Etale) (σ : G.obj.obj (op V)) (z : ↥(pullback V.hom p₁)),
      (Y₁.moduleConstantSheafToPointFunctionSheaf M).hom.app
        (op ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ p₁).obj V))
          (a.hom.app (op V) σ) z =
        (Y₁.moduleConstantSheafToPointFunctionSheaf M).hom.app
          (op ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ p₁).obj V))
          (b.hom.app (op V) σ) z) :
    a = b := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V ↦ ModuleCat.hom_ext
    (LinearMap.ext fun σ ↦ ?_)))
  induction V using Opposite.rec with | op V => ?_
  exact Scheme.injective_moduleConstantSheafToPointFunctionSheaf_app M Y₁ _
    (funext (hab V σ))

/-- Pulling back sections along `q` and then along `q'` is pulling back along `q' ≫ q`. -/
lemma constantSheafPullbackMap_comp {Y₀ : Scheme.{u}} (p₀ : Y₀ ⟶ X) (q' : Y₀ ⟶ Y₁)
    (h' : q' ≫ p₁ = p₀) :
    constantSheafPullbackMap M p₁ p₂ q h ≫ constantSheafPullbackMap M p₀ p₁ q' h' =
      constantSheafPullbackMap M p₀ p₂ (q' ≫ q) (by rw [Category.assoc, h, h']) := by
  refine hom_ext_lowerStar_constantSheaf M p₀ fun V σ z ↦
    ((constantSheafPullbackMap_apply M p₀ p₁ q' h' V _ z).trans
      ((constantSheafPullbackMap_apply M p₁ p₂ q h V σ _).trans ?_)).trans
      (constantSheafPullbackMap_apply M p₀ p₂ (q' ≫ q) _ V σ z).symm
  have key : pullbackLiftOfOver p₀ p₁ q' h' V ≫ pullbackLiftOfOver p₁ p₂ q h V =
      pullbackLiftOfOver p₀ p₂ (q' ≫ q) (by rw [Category.assoc, h, h']) V := by
    apply pullback.hom_ext <;> simp
  have hz : pullbackLiftOfOver p₁ p₂ q h V (pullbackLiftOfOver p₀ p₁ q' h' V z) =
      pullbackLiftOfOver p₀ p₂ (q' ≫ q) (by rw [Category.assoc, h, h']) V z := by
    rw [← Scheme.Hom.comp_apply, key]
  exact congrArg _ hz

end Etale

end AlgebraicGeometry
