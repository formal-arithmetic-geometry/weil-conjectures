/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.FormalFunctions
public import WeilConjectures.AlgebraicGeometry.Modules.TrivialLineBundle
public import WeilConjectures.AlgebraicGeometry.ThickeningUnits
public import WeilConjectures.Mathlib.Algebra.Category.Grp.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Integral
public import WeilConjectures.Mathlib.Logic.Function.Basic

/-!
# Formal triviality produces a section near the point

Let `f : W ⟶ T` be a proper morphism, let `t` be a point of `T` and let `F` be a coherent sheaf
of `𝒪_W`-modules whose pullback `F⁽ⁿ⁾` to the infinitesimal base change `W ×_T Tₙ` is trivial
for every `n`, where `Tₙ = Spec (𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1))`. This file proves that the stalk of
`f_* F` at `t` then has a germ whose image in `Γ(W ×_T T₀, F⁽⁰⁾)` is non-zero; equivalently, `F`
has a section over `f ⁻¹ᵁ V` for some open neighbourhood `V` of `t` which does not vanish
identically on the fibre `W_t`.

This is the first half of `prop:cube-formal-triviality` of the blueprint, steps 1 to 3 of its
proof, and it is the half that consumes the theorem on formal functions.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.surjective_formalSectionsMap`: if `F⁽ⁿ⁾` is trivial then the
  transition map `Γ(W ×_T Tₙ, F⁽ⁿ⁾) ⟶ Γ(W ×_T Tₘ, F⁽ᵐ⁾)` is surjective as soon as
  `Γ(W ×_T Tₙ, 𝒪) ⟶ Γ(W ×_T Tₘ, 𝒪)` is. This is steps 1 and 2 of the blueprint proof: a single
  trivialisation of `F⁽ⁿ⁾` restricts to one of `F⁽ᵐ⁾`, so no compatible choice of generators is
  needed.
- `AlgebraicGeometry.Scheme.Modules.exists_stalkToFormalSections_zero_ne_zero`: the map from the
  stalk of `f_* F` at `t` to `Γ(W ×_T T₀, F⁽⁰⁾)` is non-zero. This is step 3, and it uses
  `AlgebraicGeometry.Scheme.Modules.isIso_formalFunctionsComparison`, which is `sorry` by design.
- `AlgebraicGeometry.Scheme.Modules.exists_formalSectionsOfNhds_zero_ne_zero`: the same, spelled
  out as a section of `F` over `f ⁻¹ᵁ V` for an open neighbourhood `V` of `t`.
- `AlgebraicGeometry.Scheme.Modules.exists_fiberSectionsOfNhds_ne_zero`: the same, read on the
  scheme-theoretic fibre `W_t` rather than on `W ×_T T₀`.
- `AlgebraicGeometry.Scheme.Modules.exists_fiberSectionsOfNhds_ne_zero_of_isProper`: the above
  for the projection `X × T ⟶ T` of a proper variety `X` over a field, where the two hypotheses
  on the rings of the infinitesimal base changes are automatic.

## Implementation notes

* The blueprint chooses generators `sₙ` of `Mₙ := Γ(W ×_T Tₙ, F⁽ⁿ⁾)` compatibly across the tower
  by lifting units of the local rings `Aₙ`. That is not needed: a trivialisation of `F⁽ⁿ⁾`
  pulls back to one of `F⁽ᵐ⁾` for `m ≤ n`, which identifies the transition map `Mₙ ⟶ Mₘ` with
  `Aₙ ⟶ Aₘ` and therefore makes it *surjective*. A compatible family with prescribed level-zero
  term is then produced by lifting through the tower, and only its level-zero term is used.
* Everything downstream needs only that the composite `(f_* F)_t ⟶ M₀` is non-zero, not that
  `(f_* F)_t` is free of rank one, so the faithful flatness of completion does not appear. What
  replaces it is that `AdicCompletion.eval` at level one has the same image as the map from the
  uncompleted module, both being the full quotient by `𝔪_t`.

## Blueprint

Steps 1 to 3 of the proof of `prop:cube-formal-triviality`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite IsLocalRing SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-!
### Pulling back the sections of a trivial sheaf of modules
-/

section PullbackSections

variable {X X' W : Scheme.{u}}

/-- **Pulling back the global sections of a trivial sheaf is as surjective as pulling back
functions.** If `G` is isomorphic to the structure sheaf of `X'`, then the pullback of global
sections along `u : X ⟶ X'` is surjective as soon as `u.appTop` is. -/
theorem surjective_sectionsPullback_of_iso_structureModules (u : X ⟶ X') (G : X'.Modules)
    (e : G ≅ X'.structureModules) (hu : Function.Surjective u.appTop) :
    Function.Surjective (sectionsPullback u G) := by
  have key : ∀ s : Γ(G, ⊤),
      Hom.app (pullbackUnitIso u).hom ⊤
          (Hom.app ((pullback u).mapIso e).hom ⊤ (sectionsPullback u G s)) =
        u.appTop (Hom.app e.hom ⊤ s) := by
    intro s
    rw [Functor.mapIso_hom, sectionsPullback_naturality_apply u e.hom s,
      app_pullbackUnitIso_hom_sectionsPullback]
  intro y
  obtain ⟨r, hr⟩ := hu (Hom.app (pullbackUnitIso u).hom ⊤
    (Hom.app ((pullback u).mapIso e).hom ⊤ y))
  refine ⟨Hom.app e.inv ⊤ r, ?_⟩
  have h₁ : Hom.app e.hom ⊤ (Hom.app e.inv ⊤ r) = r :=
    (sectionsEquivOfIso e ⊤).apply_symm_apply r
  have h₂ := key (Hom.app e.inv ⊤ r)
  rw [h₁, hr] at h₂
  exact (sectionsEquivOfIso ((pullback u).mapIso e) ⊤).injective
    ((sectionsEquivOfIso (pullbackUnitIso u) ⊤).injective h₂)

/-- **Pulling back the global sections of a trivial sheaf over a base.** If the pullback of `F`
to `X'` is trivial, then pulling sections back along a morphism `u : X ⟶ X'` over the base is
surjective as soon as `u.appTop` is. -/
theorem surjective_sectionsPullbackOver_of_iso_structureModules (u : X ⟶ X') {p : X ⟶ W}
    {p' : X' ⟶ W} (hu : u ≫ p' = p) (F : W.Modules)
    (e : (pullback p').obj F ≅ X'.structureModules)
    (hu' : Function.Surjective u.appTop) :
    Function.Surjective (sectionsPullbackOver u hu F) := by
  intro y
  set α : (pullback u).obj ((pullback p').obj F) ≅ (pullback p).obj F :=
    (pullbackTriangle hu).app F with hα
  have key : ∀ s : Γ((pullback p').obj F, ⊤), sectionsPullbackOver u hu F s =
      Hom.app α.hom ⊤ (sectionsPullback u ((pullback p').obj F) s) := fun _ ↦ rfl
  obtain ⟨s, hs⟩ := surjective_sectionsPullback_of_iso_structureModules u _ e hu'
    ((sectionsEquivOfIso α ⊤).symm y)
  exact ⟨s, by rw [key, hs]; exact (sectionsEquivOfIso α ⊤).apply_symm_apply y⟩

end PullbackSections

/-!
### The transition maps of the tower of formal sections
-/

section FormalSections

variable {W T : Scheme.{u}} (f : W ⟶ T) (t : T) (F : W.Modules)

/-- **Functions lift along the infinitesimal base changes.** If the global functions of
`W ×_T Tₘ` are the ring `𝒪_{T, t} ⧸ 𝔪_t ^ (m + 1)`, then every function on `W ×_T Tₘ` is the
restriction of a function on `W ×_T Tₙ` for `m ≤ n`. -/
theorem surjective_appTop_infinitesimalBaseChangeMap {m n : ℕ} (h : m ≤ n)
    (hm : Function.Surjective (infinitesimalRingToΓ f t m)) :
    Function.Surjective (infinitesimalBaseChangeMap f t h).appTop := by
  intro y
  obtain ⟨b, rfl⟩ := hm y
  obtain ⟨c, rfl⟩ := T.infinitesimalRingMap_surjective t h b
  exact ⟨infinitesimalRingToΓ f t n c, by
    rw [← CommRingCat.comp_apply, infinitesimalRingToΓ_comp_appTop, CommRingCat.comp_apply]⟩

/-- **The transition maps of the tower of formal sections are surjective.**

A trivialisation of `F⁽ⁿ⁾` restricts to a trivialisation of `F⁽ᵐ⁾` for `m ≤ n`, which identifies
the transition map `Γ(W ×_T Tₙ, F⁽ⁿ⁾) ⟶ Γ(W ×_T Tₘ, F⁽ᵐ⁾)` with the restriction of functions
`Γ(W ×_T Tₙ, 𝒪) ⟶ Γ(W ×_T Tₘ, 𝒪)`. This is steps 1 and 2 of the blueprint proof of
`prop:cube-formal-triviality`, and it is where triviality of `F⁽ⁿ⁾` is used. -/
theorem surjective_formalSectionsMap {m n : ℕ} (h : m ≤ n)
    (e : (pullback (infinitesimalBaseChangeFst f t n)).obj F ≅
      (infinitesimalBaseChange f t n).structureModules)
    (hm : Function.Surjective (infinitesimalRingToΓ f t m)) :
    Function.Surjective (formalSectionsMap f t F h) :=
  surjective_sectionsPullbackOver_of_iso_structureModules _
    (infinitesimalBaseChangeMap_fst f t h) F e
    (surjective_appTop_infinitesimalBaseChangeMap f t h hm)

/-- The level-zero formal sections are non-trivial: they are isomorphic to the ring
`𝒪_{T, t} ⧸ 𝔪_t`, which is the residue field at `t`. -/
theorem nontrivial_formalSections_zero (h0 : IsIso (infinitesimalRingToΓ f t 0))
    (e : (pullback (infinitesimalBaseChangeFst f t 0)).obj F ≅
      (infinitesimalBaseChange f t 0).structureModules) :
    Nontrivial (formalSections f t F 0) := by
  have hring : Nontrivial ↥Γ(infinitesimalBaseChange f t 0, ⊤) :=
    ((asIso (infinitesimalRingToΓ f t 0)).commRingCatIsoToRingEquiv).toEquiv.symm.nontrivial
  exact nontrivial_sections_of_iso_unit e

/-- A compatible family of formal sections with a prescribed level-zero term, built by lifting
through the surjective transition maps of the tower. -/
theorem exists_forall_formalSectionsMap_eq
    (hsurj : ∀ n : ℕ, Function.Surjective (formalSectionsMap f t F n.le_succ))
    (s₀ : formalSections f t F 0) :
    ∃ s : ∀ n : ℕ, formalSections f t F n, s 0 = s₀ ∧
      ∀ n : ℕ, formalSectionsMap f t F n.le_succ (s (n + 1)) = s n :=
  Function.exists_seq_of_forall_surjective
    (M := fun n ↦ (formalSections f t F n : Type u))
    (fun n ↦ (formalSectionsMap f t F n.le_succ).hom) hsurj s₀

/-- The cone on the tower of formal sections attached to a compatible family `s`, with vertex
the local ring `𝒪_{T, t}`: its `n`-th leg sends `r` to `r • sₙ`. -/
def compatibleFamilyCone (s : ∀ n : ℕ, formalSections f t F n)
    (hs : ∀ n : ℕ, formalSectionsMap f t F n.le_succ (s (n + 1)) = s n) :
    Cone (formalSectionsSystem f t F) where
  pt := ModuleCat.of (T.presheaf.stalk t) (T.presheaf.stalk t)
  π := NatTrans.ofOpSequence
    (fun n ↦ ModuleCat.toSpanSingletonHom (formalSections f t F n) (s n))
    (fun n ↦ by
      rw [formalSectionsSystem_map_succ]
      refine (Category.id_comp _).trans ?_
      refine ((ModuleCat.toSpanSingletonHom_comp
        (formalSectionsMap f t F n.le_succ) (s (n + 1))).trans ?_).symm
      rw [hs n])

@[simp]
lemma compatibleFamilyCone_π_app (s : ∀ n : ℕ, formalSections f t F n)
    (hs : ∀ n : ℕ, formalSectionsMap f t F n.le_succ (s (n + 1)) = s n) (n : ℕ) :
    (compatibleFamilyCone f t F s hs).π.app (op n) =
      ModuleCat.toSpanSingletonHom (formalSections f t F n) (s n) := rfl

/-- The map from `𝒪_{T, t}` to the completed stalk of `f_* F` at `t` attached to a compatible
family of formal sections: the cone of
`AlgebraicGeometry.Scheme.Modules.compatibleFamilyCone` read through the comparison isomorphism
of the theorem on formal functions. -/
def ofCompatibleFamily (hiso : IsIso (formalFunctionsComparison f t F))
    (s : ∀ n : ℕ, formalSections f t F n)
    (hs : ∀ n : ℕ, formalSectionsMap f t F n.le_succ (s (n + 1)) = s n) :
    ModuleCat.of (T.presheaf.stalk t) (T.presheaf.stalk t) ⟶
      ModuleCat.of (T.presheaf.stalk t) (completedStalk ((pushforward f).obj F) t) :=
  limit.lift (formalSectionsSystem f t F) (compatibleFamilyCone f t F s hs) ≫
    inv (formalFunctionsComparison f t F)

/-- The level-zero component of `AlgebraicGeometry.Scheme.Modules.ofCompatibleFamily` is
multiplication by the level-zero term of the family. -/
lemma ofCompatibleFamily_comp_completedStalkToFormalSectionsHom
    (hiso : IsIso (formalFunctionsComparison f t F)) (s : ∀ n : ℕ, formalSections f t F n)
    (hs : ∀ n : ℕ, formalSectionsMap f t F n.le_succ (s (n + 1)) = s n) :
    ofCompatibleFamily f t F hiso s hs ≫ completedStalkToFormalSectionsHom f t F 0 =
      ModuleCat.toSpanSingletonHom (formalSections f t F 0) (s 0) := by
  simp only [ofCompatibleFamily, ← formalFunctionsComparison_π, Category.assoc,
    IsIso.inv_hom_id_assoc, limit.lift_π, compatibleFamilyCone_π_app]

/-- Every germ of the completed stalk has the same image in the formal sections as some germ of
the stalk itself: the evaluation of the completion at level `n + 1` and the quotient map of the
stalk have the same image, namely all of `(f_* F)_t ⧸ 𝔪_t ^ (n + 1)`. -/
theorem exists_stalkToFormalSections_eq (n : ℕ)
    (y : completedStalk ((pushforward f).obj F) t) :
    ∃ z : ((pushforward f).obj F).presheaf.stalk t,
      stalkToFormalSections f t F n z = completedStalkToFormalSections f t F n y := by
  obtain ⟨z, hz⟩ := Submodule.mkQ_surjective
    (maximalIdeal (T.presheaf.stalk t) ^ (n + 1) •
      (⊤ : Submodule (T.presheaf.stalk t) (((pushforward f).obj F).presheaf.stalk t)))
    (AdicCompletion.eval (maximalIdeal (T.presheaf.stalk t)) _ (n + 1) y)
  refine ⟨z, ?_⟩
  rw [completedStalkToFormalSections, LinearMap.comp_apply, ← hz, Submodule.mkQ_apply,
    Submodule.liftQ_apply]

/-- **Formal triviality gives a germ of `f_* F` at `t` which is non-zero on the fibre.**

If all the transition maps of the tower of formal sections are surjective and the level-zero
formal sections are non-trivial, then the canonical map from the stalk of `f_* F` at `t` to
`Γ(W ×_T T₀, F⁽⁰⁾)` is non-zero. This is step 3 of the blueprint proof of
`prop:cube-formal-triviality`.

This statement rests on `AlgebraicGeometry.Scheme.Modules.isIso_formalFunctionsComparison`,
which is `sorry` by design. -/
theorem exists_stalkToFormalSections_zero_ne_zero [IsLocallyNoetherian T] [IsProper f]
    [F.IsCoherent] (h0 : Nontrivial (formalSections f t F 0))
    (hsurj : ∀ n : ℕ, Function.Surjective (formalSectionsMap f t F n.le_succ)) :
    ∃ z : ((pushforward f).obj F).presheaf.stalk t, stalkToFormalSections f t F 0 z ≠ 0 := by
  obtain ⟨s₀, hs₀⟩ := exists_ne (0 : formalSections f t F 0)
  obtain ⟨s, hs0, hs⟩ := exists_forall_formalSectionsMap_eq f t F hsurj s₀
  have hiso := isIso_formalFunctionsComparison f t F
  have h₂ := ConcreteCategory.congr_hom
    (ofCompatibleFamily_comp_completedStalkToFormalSectionsHom f t F hiso s hs)
    (1 : T.presheaf.stalk t)
  rw [ConcreteCategory.comp_apply, ModuleCat.toSpanSingletonHom_apply, one_smul, hs0] at h₂
  obtain ⟨z, hz⟩ := exists_stalkToFormalSections_eq f t F 0
    (ofCompatibleFamily f t F hiso s hs 1)
  exact ⟨z, by rw [hz]; exact h₂ ▸ hs₀⟩

/-- **Formal triviality gives a section of `F` near `t` which is non-zero on the fibre.**

The germ produced by
`AlgebraicGeometry.Scheme.Modules.exists_stalkToFormalSections_zero_ne_zero`, spelled out as a
section of `F` over `f ⁻¹ᵁ V` for an open neighbourhood `V` of `t`. -/
theorem exists_formalSectionsOfNhds_zero_ne_zero [IsLocallyNoetherian T] [IsProper f]
    [F.IsCoherent] (h0 : Nontrivial (formalSections f t F 0))
    (hsurj : ∀ n : ℕ, Function.Surjective (formalSectionsMap f t F n.le_succ)) :
    ∃ (V : T.Opens) (hV : t ∈ V) (s : Γ((pushforward f).obj F, V)),
      formalSectionsOfNhds f t F 0 V hV s ≠ 0 := by
  obtain ⟨z, hz⟩ := exists_stalkToFormalSections_zero_ne_zero f t F h0 hsurj
  obtain ⟨V, hV, s, rfl⟩ := ((pushforward f).obj F).presheaf.exists_germ_eq z
  refine ⟨V, hV, s, ?_⟩
  have key : stalkToFormalSections f t F 0
      (((pushforward f).obj F).presheaf.germ V t hV s) =
      formalSectionsOfNhds f t F 0 V hV s :=
    TopCat.Presheaf.stalkDesc_germ _ _ _ _ _ V hV s
  rwa [key] at hz

/-- **Restricting a section of `f_* F` near `t` to the scheme-theoretic fibre `W_t`.** A section
of `f_* F` over an open neighbourhood `V` of `t` is a section of `F` over `f ⁻¹ᵁ V`, which
contains the whole fibre over `t`, so it restricts to a global section of `F_t`. -/
def fiberSectionsOfNhds (V : T.Opens) (hV : t ∈ V) :
    Γ((pushforward f).obj F, V) ⟶ Γ((restrictToFiber f t).obj F, ⊤) :=
  eqToHom (pushforward_obj_obj f F V) ≫
    sectionsPullbackLE (f.fiberι t) F (f.preimage_fiberι_eq_top hV).ge

/-- Restricting to the fibre `W_t` and then transporting along the isomorphism
`W ×_T T₀ ≅ W_t` is restricting to `W ×_T T₀`. -/
lemma fiberSectionsOfNhds_comp (V : T.Opens) (hV : t ∈ V) :
    fiberSectionsOfNhds f t F V hV ≫
        sectionsPullbackOver (infinitesimalBaseChangeZeroIsoFiber f t).hom
          (infinitesimalBaseChangeZeroIsoFiber_hom_fiberι f t) F =
      formalSectionsOfNhds f t F 0 V hV := by
  have h₃ : (⊤ : (infinitesimalBaseChange f t 0).Opens) ≤
      ((infinitesimalBaseChangeZeroIsoFiber f t).hom ≫ f.fiberι t) ⁻¹ᵁ (f ⁻¹ᵁ V) := by
    rw [infinitesimalBaseChangeZeroIsoFiber_hom_fiberι]
    exact (preimage_infinitesimalBaseChangeFst_eq_top f t 0 hV).ge
  rw [fiberSectionsOfNhds, formalSectionsOfNhds, Category.assoc]
  congr 1
  rw [sectionsPullbackOver, sectionsPullback,
    sectionsPullbackLE_comp_assoc _ _ F _ _ h₃, sectionsPullbackLE_congr]

/-- **Formal triviality gives a section of `F` near `t` which is non-zero on the fibre `W_t`.**

This is `AlgebraicGeometry.Scheme.Modules.exists_formalSectionsOfNhds_zero_ne_zero` read on the
scheme-theoretic fibre, which is the form in which steps 4 and 5 of the blueprint proof of
`prop:cube-formal-triviality` use it. -/
theorem exists_fiberSectionsOfNhds_ne_zero [IsLocallyNoetherian T] [IsProper f] [F.IsCoherent]
    (h0 : Nontrivial (formalSections f t F 0))
    (hsurj : ∀ n : ℕ, Function.Surjective (formalSectionsMap f t F n.le_succ)) :
    ∃ (V : T.Opens) (hV : t ∈ V) (s : Γ((pushforward f).obj F, V)),
      fiberSectionsOfNhds f t F V hV s ≠ 0 := by
  obtain ⟨V, hV, s, hs⟩ := exists_formalSectionsOfNhds_zero_ne_zero f t F h0 hsurj
  exact ⟨V, hV, s, AddCommGrpCat.apply_ne_zero_of_comp_apply_ne_zero
    (fiberSectionsOfNhds_comp f t F V hV) s hs⟩

end FormalSections

/-!
### The projection of a proper variety
-/

section Projection

variable {X T : Scheme.{u}} {K : Type u} [Field K]

/-- **Formal triviality is a section near the point, for the projection of a proper variety.**

Let `X` be a proper variety over a field `K`, let `T` be a locally noetherian `K`-scheme, let
`t` be a point of `T` and let `F` be a coherent sheaf on `X × T` whose pullback to
`(X × T) ×_T Tₙ` is trivial for every `n`. Then `F` has a section over `p_T ⁻¹ᵁ V`, for some
open neighbourhood `V` of `t`, whose restriction to the fibre over `t` is non-zero.

This is steps 1 to 3 of the proof of `prop:cube-formal-triviality` of the blueprint. It rests on
`AlgebraicGeometry.Scheme.Modules.isIso_formalFunctionsComparison`, which is `sorry` by
design. -/
theorem exists_fiberSectionsOfNhds_ne_zero_of_isProper (πX : X ⟶ Spec (.of K))
    [IsProper πX] [GeometricallyIntegral πX] (πT : T ⟶ Spec (.of K)) [IsLocallyNoetherian T]
    (t : T) (F : (Limits.pullback πX πT).Modules) [F.IsCoherent]
    (hF : ∀ n : ℕ, Nonempty
      ((pullback (infinitesimalBaseChangeFst (Limits.pullback.snd πX πT) t n)).obj F ≅
        (infinitesimalBaseChange (Limits.pullback.snd πX πT) t n).structureModules)) :
    ∃ (V : T.Opens) (hV : t ∈ V)
      (s : Γ((pushforward (Limits.pullback.snd πX πT)).obj F, V)),
      fiberSectionsOfNhds (Limits.pullback.snd πX πT) t F V hV s ≠ 0 := by
  set f := Limits.pullback.snd πX πT with hf
  have hiso : ∀ n : ℕ, IsIso (infinitesimalRingToΓ f t n) :=
    fun n ↦ Scheme.isIso_infinitesimalRingToΓ_pullbackSnd πX πT t n
  have hsurjΓ : ∀ n : ℕ, Function.Surjective (infinitesimalRingToΓ f t n) := fun n ↦
    have := hiso n
    (ConcreteCategory.bijective_of_isIso (infinitesimalRingToΓ f t n)).surjective
  exact exists_fiberSectionsOfNhds_ne_zero f t F
    (nontrivial_formalSections_zero f t F (hiso 0) (hF 0).some)
    (fun n ↦ surjective_formalSectionsMap f t F n.le_succ (hF (n + 1)).some (hsurjΓ n))

end Projection

end

end AlgebraicGeometry.Scheme.Modules
