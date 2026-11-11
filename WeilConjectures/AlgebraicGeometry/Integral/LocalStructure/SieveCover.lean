/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Sites.Proetale

/-! # Pro-étale covers from covering sieves

A property of morphisms into a scheme `S` which holds for the structure maps of all members of
a covering sieve of the terminal object of `S_proét` holds for all members of some small
pro-étale cover of `S`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency.types false in
/-- A property satisfied by the structure maps of the members of a covering sieve of the
terminal object of `S_proét` is satisfied by the members of a small pro-étale cover of `S`.
(auxiliary; not a blueprint node). -/
theorem exists_cover_of_mem_proEt_topology {S : Scheme.{u}}
    (P : ∀ {Y : Scheme.{u}}, (Y ⟶ S) → Prop) (V : Sieve (⊤_ S.ProEt))
    (hV : V ∈ Scheme.ProEt.topology S (⊤_ S.ProEt))
    (hP : ∀ (U : S.ProEt) (f : U ⟶ ⊤_ S.ProEt), V f → P (Y := U.left) U.hom) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage S, ∀ i, P (C.f i) := by
  classical
  have hT : IsTerminal (Scheme.ProEt.mk (𝟙 S)) :=
    MorphismProperty.Over.mkIdTerminal _ _
  let t : Scheme.ProEt.mk (𝟙 S) ≅ ⊤_ S.ProEt := hT.uniqueUpToIso terminalIsTerminal
  obtain ⟨R, hR, hRV⟩ := Scheme.ProEt.mem_topology_iff.mp hV
  obtain ⟨I, U, f, rfl⟩ := R.exists_eq_ofArrows
  have hc : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
      Scheme.proetalePrecoverage S := by
    let C₀ : Scheme.Cover Scheme.proetalePrecoverage (⊤_ S.ProEt).left :=
      ⟨⟨I, fun i ↦ (U i).left, fun i ↦ (f i).left⟩, by
        simpa only [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows,
          Functor.comp_obj, Functor.comp_map, Scheme.ProEt.forget,
          MorphismProperty.Over.forget, MorphismProperty.Comma.forget, Over.forget,
          Comma.fst, PreZeroHypercover.presieve₀] using hR⟩
    have : IsIso t.inv.left :=
      (Scheme.ProEt.forget S ⋙ Over.forget S).map_isIso t.inv
    have he (i : I) : (f i).left ≫ t.inv.left = (U i).hom := by
      have ht := MorphismProperty.Over.w t.inv
      change t.inv.left = (⊤_ S.ProEt).hom at ht
      rw [ht]
      exact MorphismProperty.Over.w (f i)
    have h := (C₀.pushforward t.inv.left
      (Precoverage.mem_coverings_of_isIso _)).mem₀
    change (Presieve.ofArrows (fun i ↦ (U i).left)
      (fun i ↦ (f i).left ≫ t.inv.left)) ∈ _ at h
    rw [show (fun i ↦ (f i).left ≫ t.inv.left) = (fun i ↦ (U i).hom)
      from funext he] at h
    exact h
  let C : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage S :=
    ⟨⟨I, fun i ↦ (U i).left, fun i ↦ (U i).hom⟩, hc⟩
  have : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
    inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage @WeaklyEtale))
  let q := Precoverage.ZeroHypercover.Small.restrictFun.{u} C
  let D : Scheme.Cover.{u} Scheme.proetalePrecoverage S :=
    ⟨⟨Precoverage.ZeroHypercover.Small.Index.{u} C,
      fun i ↦ (U (q i)).left, fun i ↦ (U (q i)).hom⟩,
      Precoverage.ZeroHypercover.Small.mem₀ C⟩
  exact ⟨D, fun i ↦ hP (U (q i)) (f (q i)) (hRV _ _ ⟨q i⟩)⟩

end AlgebraicGeometry.Scheme
