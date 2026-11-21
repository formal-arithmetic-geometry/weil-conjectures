/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import WeilConjectures.CategoryTheory.TraceFormula.ToposFiniteCoverCalculus

/-! # Site objects refining the inverse image of a covering family

Source: Stacks Project, Sites, Tag 00WN, and Modules on Sites, Tag 03DO (5).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The sections of inverse images of sheafified representables form a cover.

Source: Stacks Project, Sites, Tag 00WN; Modules on Sites, Tag 03DO (5). -/
theorem inverseImage_section_cover
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (L : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (R : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (adj : L ⊣ R) [PreservesFiniteLimits L]
    {ι : Type u} (Y : ι → D) (hY : K.CoversTop Y) :
    J.CoversTop (fun j : Σ i : ι, Σ V : C,
      (L.obj ((presheafToSheaf K (Type u)).obj (yoneda.obj (Y i)))).obj.obj (op V) ↦
        j.2.1) := by
  classical
  let T : Sheaf K (Type u) := Sheaf.terminal K Types.isTerminalPUnit
  let H : ι → Sheaf K (Type u) := fun i =>
    (presheafToSheaf K (Type u)).obj (yoneda.obj (Y i))
  let p : ∀ i, H i ⟶ T := fun i =>
    (Sheaf.isTerminalTerminal K Types.isTerminalPUnit).from (H i)
  have hp : Epi (Sigma.desc p) := by
    refine ((topos_finite_cover_calculus K).1 ι H T p).mpr ?_
    intro U y
    refine ⟨Sieve.ofObjects Y U, hY U, ?_⟩
    intro V a ha
    rcases ha with ⟨i, ⟨b⟩⟩
    refine ⟨i, (toSheafify K (yoneda.obj (Y i))).app (op V) b, ?_⟩
    simpa [p, T, Sheaf.terminal] using (show PUnit.unit = y from Subsingleton.elim _ _)
  let q : ∀ i, L.obj (H i) ⟶ L.obj T := fun i => L.map (p i)
  have hq : Epi (Sigma.desc q) := by
    constructor
    intro Z g h e
    apply (adj.homEquiv _ _).injective
    apply (cancel_epi (Sigma.desc p)).1
    apply Sigma.hom_ext
    intro i
    change p i ≫ (adj.homEquiv T Z) g = p i ≫ (adj.homEquiv T Z) h
    rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_left]
    have ei := congrArg (fun k => Sigma.ι (fun i => L.obj (H i)) i ≫ k) e
    simpa [q, Functor.map_comp, Category.assoc] using ei
  have hc : J.CoversTop (fun j : Σ i : ι, Σ V : C,
      (L.obj (H i)).obj.obj (op V) ↦ j.2.1) := by
    intro U
    have hterm : IsTerminal (L.obj T) :=
      (Sheaf.isTerminalTerminal K Types.isTerminalPUnit).isTerminalObj L
    let eT := hterm.uniqueUpToIso (Sheaf.isTerminalTerminal J Types.isTerminalPUnit)
    let y : (L.obj T).obj.obj (op U) := eT.inv.hom.app (op U) PUnit.unit
    obtain ⟨S, hS, hlift⟩ :=
      ((topos_finite_cover_calculus J).1 ι (fun i => L.obj (H i)) (L.obj T) q).mp hq U y
    apply J.superset_covering (fun V a ha => ?_) hS
    obtain ⟨i, x, hx⟩ := hlift V a ha
    exact ⟨⟨i, V, x⟩, ⟨𝟙 V⟩⟩
  exact hc

end CategoryTheory
