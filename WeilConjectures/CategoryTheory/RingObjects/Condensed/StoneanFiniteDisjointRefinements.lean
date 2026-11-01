/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.FiniteDisjointCover
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Coherent.CoherentTopology
import Mathlib.Data.Fintype.EquivFin

/-! # Finite partition refinements over a Stonean profinite space

Source: Gleason projectivity, Stacks Project Tags 08YN and 0F63.
(blueprint: lem-zl-stonean-finite-disjoint-refinements).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace Profinite

private theorem finiteDisjointRefinements (T : Profinite.{u})
    [ExtremallyDisconnected T] :
    (coherentTopology Profinite).HasFiniteDisjointRefinements T := by
  classical
  intro S hS
  obtain ⟨α, hα, Y₀, π₀, heff, hmem₀⟩ :=
    (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily S).1 hS
  let := hα
  let := Fintype.ofFinite α
  let e := (Fintype.equivFin α).symm
  let Y : Fin (Fintype.card α) → Profinite.{u} := fun i ↦ Y₀ (e i)
  let π : ∀ i, Y i ⟶ T := fun i ↦ π₀ (e i)
  have hsurj : ∀ x : T, ∃ (i : Fin (Fintype.card α)) (y : Y i), π i y = x := by
    intro x
    have hsurj₀ : ∀ x : T, ∃ (a : α) (y : Y₀ a), π₀ a y = x :=
      ((effectiveEpiFamily_tfae Y₀ π₀).out 0 2).1 heff
    obtain ⟨a, y, hy⟩ := hsurj₀ x
    refine ⟨e.symm a, ?_⟩
    change ∃ y, π₀ (e (e.symm a)) y = x
    rw [e.apply_symm_apply]
    exact ⟨y, hy⟩
  let p := CompHausLike.finiteCoproduct.desc Y π
  have hp : Function.Surjective p := by
    intro x
    obtain ⟨i, y, hy⟩ := hsurj x
    exact ⟨⟨i, y⟩, hy⟩
  let : Epi p := (epi_iff_surjective p).2 hp
  let : Projective T := projective_of_extrDisc inferInstance
  let s : T ⟶ CompHausLike.finiteCoproduct Y := Projective.factorThru (𝟙 T) p
  have hs : s ≫ p = 𝟙 T := Projective.factorThru_comp (𝟙 T) p
  let Z (i : Fin (Fintype.card α)) :=
    CompHausLike.pullback (CompHausLike.finiteCoproduct.ι Y i) s
  let f (i : Fin (Fintype.card α)) : Z i ⟶ T :=
    CompHausLike.pullback.snd (CompHausLike.finiteCoproduct.ι Y i) s
  let g (i : Fin (Fintype.card α)) : Z i ⟶ Y i :=
    CompHausLike.pullback.fst (CompHausLike.finiteCoproduct.ι Y i) s
  have hfac (i) : g i ≫ π i = f i := by
    rw [← CompHausLike.finiteCoproduct.ι_desc Y π i, ← Category.assoc,
      CompHausLike.pullback.condition, Category.assoc, hs, Category.comp_id]
  have hcover : EffectiveEpiFamily Z f := effectiveEpiFamily_of_jointly_surjective Z f (by
    intro x
    rcases h : s x with ⟨i, y⟩
    exact ⟨i, ⟨(y, x), h.symm⟩, rfl⟩)
  refine ⟨Fintype.card α, Z, f, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact coherentTopology.mem_sieves_of_hasEffectiveEpiFamily _
      ⟨Fin (Fintype.card α), inferInstance, Z, f, hcover, fun i ↦ Sieve.ofArrows_mk Z f i⟩
  · intro i
    apply ConcreteCategory.mono_of_injective
    intro x y hxy
    apply Subtype.ext
    apply Prod.ext
    · exact (CompHausLike.finiteCoproduct.ι_injective Y i)
        (x.property.trans ((congrArg s hxy).trans y.property.symm))
    · exact hxy
  · intro i j hij V a b hab
    have hempty : IsEmpty V := by
      constructor
      intro x
      have h : (a x).val.2 = (b x).val.2 := by
        exact ConcreteCategory.congr_hom hab x
      have heq : (CompHausLike.finiteCoproduct.ι Y i) (a x).val.1 =
          (CompHausLike.finiteCoproduct.ι Y j) (b x).val.1 :=
        (a x).property.trans ((congrArg s h).trans (b x).property.symm)
      exact hij (congrArg Sigma.fst heq)
    apply coherentTopology.mem_sieves_of_hasEffectiveEpiFamily
    refine ⟨PEmpty, inferInstance, (fun i ↦ PEmpty.elim i),
      (fun i ↦ PEmpty.elim i), ?_, fun i ↦ PEmpty.elim i⟩
    exact effectiveEpiFamily_of_jointly_surjective _ _ (fun x ↦ isEmptyElim x)
  · intro i
    rw [← hfac]
    exact S.downward_closed (hmem₀ (e i)) (g i)

private theorem over_refinements {C : Type*} [Category* C]
    (J : GrothendieckTopology C) {T : C} (W : Over T)
    (hW : J.HasFiniteDisjointRefinements W.left) :
    (J.over T).HasFiniteDisjointRefinements W := by
  intro S hS
  obtain ⟨n, Y, f, hf, hmem⟩ := hW _ ((J.mem_over_iff S).1 hS)
  let Z (i : Fin n) : Over T := Over.mk (f i ≫ W.hom)
  let a (i : Fin n) : Z i ⟶ W := Over.homMk (f i)
  refine ⟨n, Z, a, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [J.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact hf.ofArrows_mem
  · intro i
    have := hf.mono i
    exact (Over.forget T).mono_of_mono_map (inferInstanceAs (Mono (f i)))
  · intro i j hij V b c hbc
    rw [J.mem_over_iff]
    simpa only [map_bot] using hf.bot_mem i j hij b.left c.left (congrArg
      (fun h ↦ h.left) hbc)
  · intro i
    exact (Sieve.overEquiv_iff S (f i)).1 (hmem i)

/-- The terminal object in the coherent slice over a Stonean profinite space
admits finite disjoint refinements.

Source: Gleason projectivity, Stacks Project Tags 08YN and 0F63
(blueprint: lem-zl-stonean-finite-disjoint-refinements).

Proof: a coherent covering sieve contains a finite effective epimorphic family.
The map from its finite disjoint union is surjective, hence splits by projectivity
of the Stonean target. Pull back its summand inclusions along the section. These
are a finite disjoint cover, each factoring through an original member. Empty
intersections have an empty coherent cover. Finally lift the cover to the slice
using the equivalence between sieves on an object of the slice and its underlying
object; this preserves the covering and disjointness conditions. -/
theorem terminalOver_hasFiniteDisjointRefinements (T : Profinite.{u})
    [ExtremallyDisconnected T] :
    ((coherentTopology Profinite).over T).HasFiniteDisjointRefinements (Over.mk (𝟙 T)) :=
  over_refinements _ _ (finiteDisjointRefinements T)

end Profinite
