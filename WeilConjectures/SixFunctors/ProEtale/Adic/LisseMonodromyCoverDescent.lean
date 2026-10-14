/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyCover
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalkPointwise
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.GermComp

/-!
# Descent of invariant sections along universal covers

Let `Y` be a connected scheme with universal profinite étale covers on which lisse `ℓ`-adic
sheaves are free, and let `M` be a lisse sheaf on `Y`. A section `m` of the stalk `M_t` at a base
point `t` which is invariant under the monodromy is the restriction of a global section of `M`
(`AlgebraicGeometry.Scheme.UniversalCovers.exists_globalSection_of_invariant`).

The section `s` of `M` over the universal cover `p : Ỹ_t ⟶ Y` corresponding to `m` has equal
restrictions along the two projections `Ỹ_t ×_Y Ỹ_t ⟶ Ỹ_t`: their difference is a section of a
lisse sheaf which vanishes along the graph of the transport by every loop, and every point of
`Ỹ_t ×_Y Ỹ_t` lies on such a graph. Since `p` is a pro-étale covering (it is weakly étale,
surjective and quasi-compact), `s` descends to a global section of `M`, by the sheaf condition
for the covering sieve of `p`. Sections of `M` over a weakly étale `Y`-scheme `V` are identified
with the global sections of the pullback of `M` to `V` through germs along the diagonal
(`AlgebraicGeometry.ProEtale.germ`, `AlgebraicGeometry.ProEtale.diagLift`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.ProEtale

open Scheme

section Germ

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The lift `T ⟶ V ×_Y T` of `T` through the base change of `V` along `g : T ⟶ Y`, given by a
morphism `h : T ⟶ V` over `Y`. -/
noncomputable def overLift {Y T : Scheme.{u}} (V : Y.ProEt) (h : T ⟶ V.left) {g : T ⟶ Y}
    (e : h ≫ V.hom = g) :
    ProEt.mk (𝟙 T) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V :=
  MorphismProperty.Over.homMk (pullback.lift h (𝟙 T) (e.trans (Category.id_comp g).symm))
    (by exact pullback.lift_snd _ _ _)

/-- The lift given by `h : T ⟶ V` over `Y`, transported to an iterated base change, is the
base change of the diagonal of `V`. -/
lemma overLift_comp_pullbackComp_hom_app {Y T : Scheme.{u}} (V : Y.ProEt) (h : T ⟶ V.left) :
    overLift V h rfl ≫ (MorphismProperty.Over.pullbackComp h V.hom).hom.app V =
      (overPullbackObjMkIdIso h).inv ≫
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ h).map (diagLift V) := by
  refine MorphismProperty.Over.Hom.ext ?_
  erw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left]
  rw [← cancel_epi (pullback.snd (𝟙 V.left) h)]
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp [overLift, diagLift, overPullbackObjMkIdIso]
      erw [pullbackLeftPullbackSndIso_inv_fst, pullback.lift_fst]
      exact pullback.condition.symm
    · simp [overLift, diagLift, overPullbackObjMkIdIso]
      erw [pullbackLeftPullbackSndIso_inv_fst_snd, pullback.lift_snd_assoc, Category.id_comp]
      exact pullback.condition.symm
  · simp [overLift, diagLift, overPullbackObjMkIdIso]
    erw [pullbackLeftPullbackSndIso_inv_snd_snd, pullback.lift_snd, Category.comp_id]
    rfl

/-- The germ along the lift given by a morphism `h : T ⟶ V` over `Y` is the germ along the
diagonal of `V`, restricted along `h`. -/
lemma germ_overLift {Y T : Scheme.{u}} (P : Sheaf (ProEt.topology Y) A) (V : Y.ProEt)
    (h : T ⟶ V.left) {g : T ⟶ Y} (e : h ≫ V.hom = g) :
    germ A g P (overLift V h e) = germ A V.hom P (diagLift V) ≫ (resOver A h e).app P := by
  subst e
  have key := germ_comp A h V.hom P (diagLift V) (overLift V h rfl)
    (overLift_comp_pullbackComp_hom_app V h)
  rw [resOver_app, upperStarFactor_rfl, ← reassoc_of% key, ← Functor.map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]

/-- **Naturality of germs along diagonals.** For a morphism `f : V' ⟶ V` of weakly étale
`Y`-schemes, the germ along the diagonal of the restriction of a section to `V'` is the germ
along the diagonal of `V`, restricted along `f`. -/
lemma map_comp_germ_diagLift {Y : Scheme.{u}} (P : Sheaf (ProEt.topology Y) A) {V V' : Y.ProEt}
    (f : V' ⟶ V) :
    P.obj.map f.op ≫ germ A V'.hom P (diagLift V') =
      germ A V.hom P (diagLift V) ≫ (resOver A f.left (MorphismProperty.Over.w f)).app P := by
  rw [map_germ (t := overLift V f.left (MorphismProperty.Over.w f)), germ_overLift]
  refine MorphismProperty.Over.Hom.ext ?_
  apply pullback.hom_ext
  · erw [MorphismProperty.Comma.comp_left]
    simp [overLift, diagLift]
    exact Category.id_comp _
  · erw [MorphismProperty.Comma.comp_left]
    simp [overLift, diagLift]

/-- The restriction of global sections along `g` is the germ along the lift of the terminal
object. -/
lemma globalSectionsToUpperStar_app_eq_germ {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (P : Sheaf (ProEt.topology Y) A) :
    (globalSectionsToUpperStar A g).app P =
      (Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId Y)).hom.app P ≫
        germ A g P (overPullbackObjMkIdIso g).inv := by
  have n := (Sheaf.ΓNatIsoSheafSections _ A (ProEt.isTerminalMkId Y)).hom.naturality
    ((upperStarLowerStarAdjunction A g).unit.app P)
  rw [globalSectionsToUpperStar_app, globalSectionsLowerStarIso_hom_app', germ, reassoc_of% n]
  rfl

/-- The germ along the diagonal identifies the sections of a sheaf over a weakly étale
`Y`-scheme `V` with the global sections of its pullback to `V`. -/
instance isIso_germ_diagLift {Y : Scheme.{u}} (P : Sheaf (ProEt.topology Y) A) (V : Y.ProEt) :
    IsIso (germ A V.hom P (diagLift V)) := by
  let e : (MorphismProperty.Over.map ⊤ V.prop).obj (ProEt.mk (𝟙 V.left)) ⟶ V :=
    (MorphismProperty.Over.map ⊤ V.prop).map (diagLift V) ≫
      (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ V.hom V.prop trivial).counit.app V
  let r : V ⟶ (MorphismProperty.Over.map ⊤ V.prop).obj (ProEt.mk (𝟙 V.left)) :=
    MorphismProperty.Over.homMk (𝟙 _) (by simp only [Category.id_comp]; rfl)
  have he : e.left = 𝟙 _ := by
    change 𝟙 _ ≫ pullback.lift (𝟙 V.left) (𝟙 V.left) rfl ≫ pullback.fst _ _ = 𝟙 _
    simp
  have : IsIso e := ⟨r, MorphismProperty.Over.Hom.ext (by
      erw [MorphismProperty.Comma.comp_left, he]; rfl),
    MorphismProperty.Over.Hom.ext (by erw [MorphismProperty.Comma.comp_left, he]; rfl)⟩
  have h := germ_comp_upperStarIsoLocalizationRestriction A V.hom V.prop P (diagLift V)
  have hI : IsIso (P.obj.map e.op) := Functor.map_isIso _ e.op
  rw [show P.obj.map e.op = _ from h.symm] at hI
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance hI

end Germ

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme.UniversalCovers

open ProEtale FiniteEtale

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}} {Ω : Type u} [Field Ω]
  {U : Scheme.UniversalCovers Y Ω}

/-- The graph `x ↦ (x, g x)` of the transport of the universal cover along a loop `g`. -/
noncomputable def graph (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (g : Aut (fiber t)) :
    U.cover t ⟶ pullback (U.proj t) (U.proj t) :=
  pullback.lift (𝟙 _) (U.transport g).hom (by rw [Category.id_comp, U.transport_proj])

lemma graph_fst (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (g : Aut (fiber t)) :
    U.graph t g ≫ pullback.fst _ _ = 𝟙 _ :=
  pullback.lift_fst _ _ _

lemma graph_snd (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (g : Aut (fiber t)) :
    U.graph t g ≫ pullback.snd _ _ = (U.transport g).hom :=
  pullback.lift_snd _ _ _

lemma graph_fst_proj (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (g : Aut (fiber t)) :
    U.graph t g ≫ pullback.fst (U.proj t) (U.proj t) ≫ U.proj t = U.proj t := by
  rw [← Category.assoc, graph_fst, Category.id_comp]

/-- **Invariant sections over the universal cover have equal restrictions to
`Ỹ_t ×_Y Ỹ_t`.** A section `s` of a lisse sheaf `M` over the universal cover `Ỹ_t` which is
invariant under the transports along all loops at `t` has equal restrictions along the two
projections `Ỹ_t ×_Y Ỹ_t ⟶ Ỹ_t`: their difference vanishes along the graph of every loop, and
these graphs cover `Ỹ_t ×_Y Ỹ_t`. -/
theorem resOver_fst_apply_eq_resOver_snd_apply (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)
    (M : LisseSheaf l Y)
    (s : (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj ((U.proj t)^*[_].obj M.obj.X))
    (hs : ∀ g : Aut (fiber t), ((U.transportRes l g).hom.app M.obj.X).hom s = s) :
    ((resOver (WeilCoefficients.{u} l) (pullback.fst (U.proj t) (U.proj t)) rfl).app
        M.obj.X).hom s =
      ((resOver (WeilCoefficients.{u} l) (pullback.snd (U.proj t) (U.proj t))
        pullback.condition.symm).app M.obj.X).hom s := by
  rw [← sub_eq_zero]
  obtain ⟨β, hβ⟩ := (bijective_globalSectionOfModHom
    ((pullback.fst (U.proj t) (U.proj t) ≫ U.proj t)^*ᵃ[l].obj M.obj)).2
    (((resOver (WeilCoefficients.{u} l) (pullback.fst (U.proj t) (U.proj t)) rfl).app
        M.obj.X).hom s -
      ((resOver (WeilCoefficients.{u} l) (pullback.snd (U.proj t) (U.proj t))
        pullback.condition.symm).app M.obj.X).hom s)
  -- the difference vanishes along the graph of every loop
  have hgraph (g : Aut (fiber t)) :
      ((resOver (WeilCoefficients.{u} l) (U.graph t g) (graph_fst_proj t g)).app M.obj.X).hom
        (globalSectionOfModHom β) = 0 := by
    have h₁ := congrArg (fun φ ↦ φ.hom s) (resOver_comp (WeilCoefficients.{u} l) (U.graph t g)
      (pullback.fst (U.proj t) (U.proj t)) (graph_fst_proj t g) rfl
      (by rw [graph_fst, Category.id_comp]) M.obj.X)
    have h₂ := congrArg (fun φ ↦ φ.hom s) (resOver_comp (WeilCoefficients.{u} l) (U.graph t g)
      (pullback.snd (U.proj t) (U.proj t)) (graph_fst_proj t g) pullback.condition.symm
      (by rw [graph_snd, U.transport_proj]) M.obj.X)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h₁ h₂
    rw [hβ, map_sub, h₁, h₂, resOver_congr _ (graph_fst t g) _ (Category.id_comp _),
      resOver_id, resOver_congr _ (graph_snd t g) _ (U.transport_proj g)]
    have hinv : ((resOver (WeilCoefficients.{u} l) (U.transport g).hom
        (U.transport_proj g)).app M.obj.X).hom s = s := by
      have h := congrArg (fun φ ↦ φ.hom s)
        (congrArg (fun α ↦ α.app M.obj.X) (U.transportRes l g).hom_inv_id)
      simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply, NatTrans.id_app,
        ModuleCat.hom_id, LinearMap.id_apply, hs g] at h
      exact h
    rw [hinv]
    exact sub_self _
  have hβ0 : β = 0 := by
    refine (M.property.upperStar _).eq_zero_of_globalSectionsToUpperStar_eq_zero' β fun w ↦ ?_
    obtain ⟨g, x, hx⟩ := U.exists_graph t w
    let K := AlgebraicClosure ((U.cover t).residueField x)
    let s₀ : Spec (.of K) ⟶ U.cover t :=
      Spec.map (CommRingCat.ofHom (algebraMap ((U.cover t).residueField x) K)) ≫
        (U.cover t).fromSpecResidueField x
    have hs₀ : s₀.base (IsLocalRing.closedPoint K) = x :=
      (U.cover t).fromSpecResidueField_apply x _
    refine ⟨w, K, inferInstance, inferInstance, s₀ ≫ U.graph t g, specializes_rfl,
      specializes_of_eq ?_, ?_⟩
    · show w = (U.graph t g).base (s₀.base (IsLocalRing.closedPoint K))
      rw [hs₀]
      exact hx.symm
    · have h₀ : ((globalSectionsToUpperStar (WeilCoefficients.{u} l) (U.graph t g)).app
          ((pullback.fst (U.proj t) (U.proj t) ≫ U.proj t)^*[_].obj M.obj.X)).hom
            (globalSectionOfModHom β) = 0 := by
        have h := hgraph g
        rw [resOver_app, ModuleCat.comp_apply] at h
        refine ((Sheaf.Γ _ (WeilCoefficients.{u} l)).mapIso
          ((upperStarFactor (WeilCoefficients.{u} l) (graph_fst_proj t g)).app
            M.obj.X).symm).toLinearEquiv.injective ?_
        rw [map_zero]
        exact h
      have hc := congrArg (fun φ ↦ φ.hom (globalSectionOfModHom β))
        (globalSectionsToUpperStar_comp (WeilCoefficients.{u} l) s₀ (U.graph t g)
          ((pullback.fst (U.proj t) (U.proj t) ≫ U.proj t)^*[_].obj M.obj.X))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, h₀, map_zero] at hc
      refine ((Sheaf.Γ _ (WeilCoefficients.{u} l)).mapIso
        ((upperStarComp (WeilCoefficients.{u} l) s₀ (U.graph t g)).app
          ((pullback.fst (U.proj t) (U.proj t) ≫ U.proj t)^*[_].obj
            M.obj.X))).toLinearEquiv.injective ?_
      rw [map_zero]
      exact hc
  rw [← hβ, hβ0, globalSectionOfModHom_eq]
  simp

end AlgebraicGeometry.Scheme.UniversalCovers
