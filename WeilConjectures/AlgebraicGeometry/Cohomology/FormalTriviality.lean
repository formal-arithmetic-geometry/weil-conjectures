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
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.EpiMono
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Integral
public import WeilConjectures.Mathlib.Order.KonigLemma

/-!
# Formal triviality produces a section near the point

Let `f : W ⟶ T` be a proper morphism, let `t` be a point of `T` and let `F` be a coherent sheaf
of `𝒪_W`-modules whose pullback `F⁽ⁿ⁾` to the infinitesimal base change `W ×_T Tₙ` is trivial
for every `n`, where `Tₙ = Spec (𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1))`. This file proves that the stalk of
`f_* F` at `t` then surjects onto `Γ(W ×_T T₀, F⁽⁰⁾)`; in particular, if the latter is
non-trivial, `F` has a section over `f ⁻¹ᵁ V` for some open neighbourhood `V` of `t` which does
not vanish identically on the fibre `W_t`.

This is the first half of `prop:cube-formal-triviality` of the blueprint, steps 1 to 3 of its
proof, and it is the half that consumes the theorem on formal functions.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.surjective_formalSectionsMap`: if `F⁽ⁿ⁾` is trivial then the
  transition map `Γ(W ×_T Tₙ, F⁽ⁿ⁾) ⟶ Γ(W ×_T Tₘ, F⁽ᵐ⁾)` is surjective as soon as
  `Γ(W ×_T Tₙ, 𝒪) ⟶ Γ(W ×_T Tₘ, 𝒪)` is. This is steps 1 and 2 of the blueprint proof: a single
  trivialisation of `F⁽ⁿ⁾` restricts to one of `F⁽ᵐ⁾`, so no compatible choice of generators is
  needed.
- `AlgebraicGeometry.Scheme.Modules.surjective_limit_πZero`: the limit of a tower of surjections
  surjects onto its level-zero term.
- `AlgebraicGeometry.Scheme.Modules.surjective_stalkToFormalSections_zero`: the map from the
  stalk of `f_* F` at `t` to `Γ(W ×_T T₀, F⁽⁰⁾)` is surjective. This is step 3.
- `AlgebraicGeometry.Scheme.Modules.exists_fiberSectionsOfNhds_ne_zero`: consequently, if
  `Γ(W ×_T T₀, F⁽⁰⁾)` is non-trivial, `F` has a section over `f ⁻¹ᵁ V` for an open neighbourhood
  `V` of `t` whose restriction to the scheme-theoretic fibre `W_t` is non-zero. This is the shape
  in which steps 4 and 5 of the blueprint proof use it.
- `AlgebraicGeometry.Scheme.Modules.exists_fiberSectionsOfNhds_pullbackSnd_ne_zero`: the above
  for the projection `X × T ⟶ T` of a proper geometrically integral variety `X` over a field,
  where the hypotheses on the rings of the infinitesimal base changes are automatic. This is the
  only declaration of the file that applies
  `AlgebraicGeometry.Scheme.Modules.isIso_formalFunctionsComparison`, and hence the only one that
  is `sorry`-tainted.

## Implementation notes

* The blueprint chooses generators `sₙ` of `Mₙ := Γ(W ×_T Tₙ, F⁽ⁿ⁾)` compatibly across the tower
  by lifting units of the local rings `Aₙ`. That is not needed: a trivialisation of `F⁽ⁿ⁾`
  pulls back to one of `F⁽ᵐ⁾` for `m ≤ n`, which identifies the transition map `Mₙ ⟶ Mₘ` with
  `Aₙ ⟶ Aₘ` and therefore makes it *surjective*. A compatible family with prescribed level-zero
  term is then produced by lifting through the tower.
* Everything downstream needs only that `(f_* F)_t ⟶ M₀` is surjective, not that `(f_* F)_t` is
  free of rank one, so the faithful flatness of completion does not appear. What replaces it is
  `AlgebraicGeometry.Scheme.Modules.range_completedStalkToFormalSections`: `AdicCompletion.eval`
  at level one has the same image as the map from the uncompleted module, both being the full
  quotient by `𝔪_t`.
* Every statement except the last takes `IsIso (formalFunctionsComparison f t F)` as a
  hypothesis rather than invoking
  `AlgebraicGeometry.Scheme.Modules.isIso_formalFunctionsComparison`, which is `sorry` by
  design. Only the packaged statement for a projection applies it, so it is the only tainted
  declaration here; this follows the policy of
  `WeilConjectures.AlgebraicGeometry.Cohomology.FormalFunctions` that a statement resting on a
  `sorry` should be applied by name and in as few places as possible.
* The tower argument gives surjectivity of `stalkToFormalSections f t F n` at every level `n`,
  not only at `n = 0`, once a compatible family with a prescribed term at level `n` is
  available. Only level zero is used downstream, and only level zero is proved here.

## Blueprint

Steps 1 to 3 of the proof of `prop:cube-formal-triviality`, stated as
`lem:cube-formal-section-near-point`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite IsLocalRing SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

section FormalSections

variable {W T : Scheme.{u}} (f : W ⟶ T) (t : T) (F : W.Modules)

/-!
### The transition maps of the tower of formal sections
-/

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

/-!
### Lifting through the tower
-/

/-- **The limit of a tower of surjections surjects onto its level-zero term.**

Given an element `s₀` of `Γ(W ×_T T₀, F⁽⁰⁾)`, lifting it through the surjective transition maps
produces a compatible family `sₙ`; the cone on the tower with vertex `𝒪_{T, t}` whose `n`-th leg
is `r ↦ r • sₙ` then lifts to the limit, and evaluating the lift at `1` gives a preimage of
`s₀`. -/
theorem surjective_limit_πZero
    (hsurj : ∀ n : ℕ, Function.Surjective (formalSectionsMap f t F n.le_succ)) :
    Function.Surjective (limit.π (formalSectionsSystem f t F) (op 0)) := by
  intro s₀
  obtain ⟨s, hs0, hs⟩ := exists_seq_of_forall_surjective
    (M := fun n ↦ (formalSections f t F n : Type u))
    (fun n ↦ (formalSectionsMap f t F n.le_succ).hom) hsurj s₀
  let c : Cone (formalSectionsSystem f t F) :=
    { pt := ModuleCat.of (T.presheaf.stalk t) (T.presheaf.stalk t)
      π := NatTrans.ofOpSequence
        (fun n ↦ ModuleCat.toSpanSingletonHom (formalSections f t F n) (s n))
        (fun n ↦ by
          rw [formalSectionsSystem_map_succ]
          refine (Category.id_comp _).trans ?_
          refine ((ModuleCat.toSpanSingletonHom_comp
            (formalSectionsMap f t F n.le_succ) (s (n + 1))).trans ?_).symm
          rw [hs n]) }
  have hπ : limit.lift (formalSectionsSystem f t F) c ≫
      limit.π (formalSectionsSystem f t F) (op 0) =
        ModuleCat.toSpanSingletonHom (formalSections f t F 0) (s 0) :=
    limit.lift_π c (op 0)
  refine ⟨limit.lift (formalSectionsSystem f t F) c 1, ?_⟩
  rw [← ConcreteCategory.comp_apply, hπ]
  exact (ModuleCat.toSpanSingletonHom_apply (formalSections f t F 0) (s 0) 1).trans
    ((one_smul _ (s 0)).trans hs0)

/-!
### The section near the point
-/

/-- **The stalk of `f_* F` at `t` surjects onto the level-zero formal sections.**

If all the transition maps of the tower of formal sections are surjective, then the canonical map
from the stalk of `f_* F` at `t` to `Γ(W ×_T T₀, F⁽⁰⁾)` is surjective: a compatible family of
formal sections with prescribed level-zero term is an element of the limit, hence of the completed
stalk, and the completed stalk has the same image in `Γ(W ×_T T₀, F⁽⁰⁾)` as the stalk itself.

This is step 3 of the blueprint proof of `prop:cube-formal-triviality`. -/
theorem surjective_stalkToFormalSections_zero (hiso : IsIso (formalFunctionsComparison f t F))
    (hsurj : ∀ n : ℕ, Function.Surjective (formalSectionsMap f t F n.le_succ)) :
    Function.Surjective (stalkToFormalSections f t F 0) := by
  rw [← LinearMap.range_eq_top, ← range_completedStalkToFormalSections, LinearMap.range_eq_top]
  intro s₀
  obtain ⟨y, hy⟩ := surjective_limit_πZero f t F hsurj s₀
  have hinv : formalFunctionsComparison f t F (inv (formalFunctionsComparison f t F) y) = y := by
    rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]
  refine ⟨inv (formalFunctionsComparison f t F) y, ?_⟩
  rw [← completedStalkToFormalSectionsHom_apply, ← formalFunctionsComparison_π,
    ConcreteCategory.comp_apply, hinv]
  exact hy

/-- **A germ of `f_* F` at `t` which is non-zero on `W ×_T T₀`.**

If the transition maps of the tower are surjective and the level-zero formal sections are
non-trivial, then the map from the stalk of `f_* F` at `t` to `Γ(W ×_T T₀, F⁽⁰⁾)` is non-zero.
Both hypotheses come from triviality of `F⁽ⁿ⁾`, by
`AlgebraicGeometry.Scheme.Modules.surjective_formalSectionsMap` and
`AlgebraicGeometry.Scheme.Modules.nontrivial_sections_of_iso_unit`. -/
theorem exists_stalkToFormalSections_zero_ne_zero (hiso : IsIso (formalFunctionsComparison f t F))
    (h0 : Nontrivial (formalSections f t F 0))
    (hsurj : ∀ n : ℕ, Function.Surjective (formalSectionsMap f t F n.le_succ)) :
    ∃ z : ((pushforward f).obj F).presheaf.stalk t, stalkToFormalSections f t F 0 z ≠ 0 := by
  obtain ⟨s₀, hs₀⟩ := exists_ne (0 : formalSections f t F 0)
  obtain ⟨z, hz⟩ := surjective_stalkToFormalSections_zero f t F hiso hsurj s₀
  refine ⟨z, ?_⟩
  rw [hz]
  exact hs₀

/-- A section of `F` over `f ⁻¹ᵁ V`, for an open neighbourhood `V` of `t`, which is non-zero on
`W ×_T T₀`: the germ produced by
`AlgebraicGeometry.Scheme.Modules.exists_stalkToFormalSections_zero_ne_zero`, spelled out. -/
theorem exists_formalSectionsOfNhds_zero_ne_zero
    (hiso : IsIso (formalFunctionsComparison f t F)) (h0 : Nontrivial (formalSections f t F 0))
    (hsurj : ∀ n : ℕ, Function.Surjective (formalSectionsMap f t F n.le_succ)) :
    ∃ (V : T.Opens) (hV : t ∈ V) (s : Γ((pushforward f).obj F, V)),
      formalSectionsOfNhds f t F 0 V hV s ≠ 0 := by
  obtain ⟨z, hz⟩ := exists_stalkToFormalSections_zero_ne_zero f t F hiso h0 hsurj
  obtain ⟨V, hV, s, rfl⟩ := ((pushforward f).obj F).presheaf.exists_germ_eq z
  refine ⟨V, hV, s, ?_⟩
  have key : stalkToFormalSections f t F 0
      (((pushforward f).obj F).presheaf.germ V t hV s) =
      formalSectionsOfNhds f t F 0 V hV s :=
    TopCat.Presheaf.stalkDesc_germ _ _ _ _ _ V hV s
  rwa [key] at hz

/-- Restricting a section of `f_* F` near `t` to the fibre `W_t` and then transporting along the
isomorphism `W ×_T T₀ ≅ W_t` is restricting it to `W ×_T T₀`:

```
                        fiberSectionsOfNhds f F t V hV
  Γ(f_* F, V) -------------------------------------------------> Γ(F_t, ⊤)
              ╲                                                       |
               ╲  formalSectionsOfNhds f t F 0 V hV                   | pullback of sections
                ╲                                                     | along W ×_T T₀ ≅ W_t
                 ╲                                                    v
                  ────────────────────────────────────> Γ(W ×_T T₀, F⁽⁰⁾)
```
-/
lemma fiberSectionsOfNhds_comp (V : T.Opens) (hV : t ∈ V) :
    fiberSectionsOfNhds f F t V hV ≫
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

/-- **A section of `F` near `t` which is non-zero on the scheme-theoretic fibre `W_t`.**

If the transition maps of the tower of formal sections are surjective and the level-zero formal
sections are non-trivial, then `F` has a section over `f ⁻¹ᵁ V`, for some open neighbourhood `V`
of `t`, whose restriction to `W_t` is non-zero.

Both hypotheses are supplied by triviality of the sheaves `F⁽ⁿ⁾`, and this is the form in which
steps 4 and 5 of the blueprint proof of `prop:cube-formal-triviality` use it. -/
theorem exists_fiberSectionsOfNhds_ne_zero (hiso : IsIso (formalFunctionsComparison f t F))
    (h0 : Nontrivial (formalSections f t F 0))
    (hsurj : ∀ n : ℕ, Function.Surjective (formalSectionsMap f t F n.le_succ)) :
    ∃ (V : T.Opens) (hV : t ∈ V) (s : Γ((pushforward f).obj F, V)),
      fiberSectionsOfNhds f F t V hV s ≠ 0 := by
  obtain ⟨V, hV, s, hs⟩ := exists_formalSectionsOfNhds_zero_ne_zero f t F hiso h0 hsurj
  have h : (fiberSectionsOfNhds f F t V hV ≫
      sectionsPullbackOver (infinitesimalBaseChangeZeroIsoFiber f t).hom
        (infinitesimalBaseChangeZeroIsoFiber_hom_fiberι f t) F) s ≠ 0 := by
    rwa [fiberSectionsOfNhds_comp]
  exact ⟨V, hV, s, AddCommGrpCat.apply_ne_zero_of_comp_apply_ne_zero _ _ h⟩

end FormalSections

/-!
### The projection of a proper variety
-/

section Projection

variable {X T : Scheme.{u}} {K : Type u} [Field K]

/-- **Formal triviality is a section near the point, for the projection of a proper variety.**

Let `X` be a proper geometrically integral variety over a field `K`, let `T` be a locally
noetherian `K`-scheme, let `t` be a point of `T` and let `F` be a coherent sheaf on `X × T` whose
pullback to `(X × T) ×_T Tₙ` is trivial for every `n`. Then `F` has a section over `p_T ⁻¹ᵁ V`,
for some open neighbourhood `V` of `t`, whose restriction to the fibre over `t` is non-zero.

This is steps 1 to 3 of the proof of `prop:cube-formal-triviality` of the blueprint. It is the
only declaration of this file that applies
`AlgebraicGeometry.Scheme.Modules.isIso_formalFunctionsComparison`, which is `sorry` by
design. -/
theorem exists_fiberSectionsOfNhds_pullbackSnd_ne_zero (πX : X ⟶ Spec (.of K))
    [IsProper πX] [GeometricallyIntegral πX] (πT : T ⟶ Spec (.of K)) [IsLocallyNoetherian T]
    (t : T) (F : (Limits.pullback πX πT).Modules) [F.IsCoherent]
    (hF : ∀ n : ℕ, Nonempty
      ((pullback (infinitesimalBaseChangeFst (Limits.pullback.snd πX πT) t n)).obj F ≅
        (infinitesimalBaseChange (Limits.pullback.snd πX πT) t n).structureModules)) :
    ∃ (V : T.Opens) (hV : t ∈ V)
      (s : Γ((pushforward (Limits.pullback.snd πX πT)).obj F, V)),
      fiberSectionsOfNhds (Limits.pullback.snd πX πT) F t V hV s ≠ 0 := by
  set f := Limits.pullback.snd πX πT
  have hiso : ∀ n : ℕ, IsIso (infinitesimalRingToΓ f t n) :=
    fun n ↦ Scheme.isIso_infinitesimalRingToΓ_pullbackSnd πX πT t n
  have hsurjΓ : ∀ n : ℕ, Function.Surjective (infinitesimalRingToΓ f t n) := fun n ↦
    have := hiso n
    (ConcreteCategory.bijective_of_isIso (infinitesimalRingToΓ f t n)).surjective
  have := Scheme.nontrivial_infinitesimalBaseChangeΓ f t 0 (hiso 0)
  exact exists_fiberSectionsOfNhds_ne_zero f t F (isIso_formalFunctionsComparison f t F)
    (nontrivial_sections_of_iso_unit (hF 0).some)
    (fun n ↦ surjective_formalSectionsMap f t F n.le_succ (hF (n + 1)).some (hsurjΓ n))

end Projection

end

end AlgebraicGeometry.Scheme.Modules
