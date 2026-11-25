/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf

/-! # Proper shrinking around a fibrewise nonvanishing section

## References

* [Stacks Project, Tags 0BF1 and 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A section nonvanishing on a proper fibre makes the line bundle come from the base
on an open neighbourhood, universally for all schemes mapping into that neighbourhood
(Stacks, Tags 0BF1, 0BF2 and 01CY). -/
theorem proper_fibre_generator_pullback_locus {X S : Scheme.{v}} (f : X ⟶ S)
    [IsProper f] (L : X.Modules) [L.IsInvertible]
    {W : Scheme.{v}} (k : W ⟶ S) (w : W)
    (σ : Γ((Modules.tensorPullback (pullback.fst f k)).obj L, ⊤))
    (hσ : ∀ x : (pullback f k : Scheme.{v}), (pullback.snd f k) x = w →
      x ∈ Modules.nonvanishingLocus
        ((Modules.tensorPullback (pullback.fst f k)).obj L) σ) :
    ∃ V : W.Opens, w ∈ V ∧ ∀ {T : Scheme.{v}} (h : T ⟶ W), Set.range h ⊆ V →
      ∃ (N : T.Modules) (_ : N.IsFiniteLocallyFree),
        Nonempty ((Modules.tensorPullback (pullback.fst f (h ≫ k))).obj L ≅
          (Modules.tensorPullback (pullback.snd f (h ≫ k))).obj N) := by
  classical
  let Y : Scheme.{v} := pullback f k
  let p : Y ⟶ W := pullback.snd f k
  let M : Y.Modules := (Modules.tensorPullback (pullback.fst f k)).obj L
  let eM : Modules.tensorPullback (pullback.fst f k) ≅
      Modules.pullback (pullback.fst f k) :=
    (Classical.choose (Modules.exists_tensorPullbackAdjunction (pullback.fst f k))).leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction (pullback.fst f k))
  have : M.IsInvertible := Modules.IsInvertible.of_iso (eM.app L).symm
  obtain ⟨D, hD, _, hdiv⟩ := Modules.nonvanishing_section_trivializes Y M σ
  let V : W.Opens := ⟨(p '' (D : Set Y)ᶜ)ᶜ,
    (p.isClosedMap _ D.isOpen.isClosed_compl).isOpen_compl⟩
  have hwV : w ∈ V := by
    rintro ⟨x, hx, hpw⟩
    apply hx
    rw [hD]
    exact hσ x hpw
  refine ⟨V, hwV, ?_⟩
  intro T h hh
  let q : pullback f (h ≫ k) ⟶ Y :=
    pullback.lift (pullback.fst f (h ≫ k)) (pullback.snd f (h ≫ k) ≫ h)
      (by simp only [Category.assoc, pullback.condition])
  have hqfst : q ≫ pullback.fst f k = pullback.fst f (h ≫ k) := by
    simp [q]
  have hqsnd : q ≫ p = pullback.snd f (h ≫ k) ≫ h := by
    simp [q, p]
  have hqD (x : (pullback f (h ≫ k) : Scheme.{v})) : q x ∈ D := by
    by_contra hx
    have hxV := hh ⟨(pullback.snd f (h ≫ k)) x, rfl⟩
    apply hxV
    refine ⟨q x, hx, ?_⟩
    change (q ≫ p) x = _
    rw [hqsnd]
    rfl
  have hgenD : Modules.IsFreeGenerator
      (M.presheaf.map (homOfLE (le_top : D ≤ ⊤)).op σ) := by
    intro A hAD
    have hcoeff : Function.Bijective (fun a : Γ(Y, A) ↦
        a • M.presheaf.map (homOfLE (le_top : A ≤ ⊤)).op σ) := by
      constructor
      · intro a b hab
        obtain ⟨c, hc, huniq⟩ := hdiv A hAD
          (a • M.presheaf.map (homOfLE (le_top : A ≤ ⊤)).op σ)
        exact (huniq a rfl).trans (huniq b hab).symm
      · intro t
        obtain ⟨a, ha, _⟩ := hdiv A hAD t
        exact ⟨a, ha.symm⟩
    simpa only [Modules.presheaf_map_homOfLE_map_homOfLE] using hcoeff
  have hqtop : q ⁻¹ᵁ D = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    exact hqD x
  obtain ⟨τ, hτ⟩ : ∃ τ : Γ((Modules.pullback q).obj M, ⊤),
      Modules.IsFreeGenerator τ := by
    have hgen := hgenD.pullback_unit_app q
    exact ⟨_, hgen.map hqtop.ge⟩
  have := Modules.isIso_homOfGlobalSection hτ
  let R := (Modules.tensorPullback q).obj M
  let eq : Modules.tensorPullback q ≅ Modules.pullback q :=
    (Classical.choose (Modules.exists_tensorPullbackAdjunction q)).leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction q)
  let eR : R ≅ SheafOfModules.unit (pullback f (h ≫ k)).ringCatSheaf :=
    eq.app M ≪≫ (asIso (Modules.homOfGlobalSection _ τ)).symm
  obtain ⟨ecomp⟩ := Modules.nonempty_tensorPullbackComp q (pullback.fst f k)
  let eL : (Modules.tensorPullback (pullback.fst f (h ≫ k))).obj L ≅ R :=
    (eqToIso (by rw [hqfst]) :
      (Modules.tensorPullback (pullback.fst f (h ≫ k))).obj L ≅
        (Modules.tensorPullback (q ≫ pullback.fst f k)).obj L) ≪≫ ecomp.app L
  have hunit := (Modules.tensorPullbackObjUnitToUnit_isIso
    (pullback.snd f (h ≫ k))).1
  let : IsIso (Modules.tensorPullbackObjUnitToUnit (pullback.snd f (h ≫ k))) := hunit
  have : (SheafOfModules.unit T.ringCatSheaf).IsInvertible :=
    SheafOfModules.instIsInvertibleUnit.{v, v, v}
  refine ⟨SheafOfModules.unit T.ringCatSheaf,
    SheafOfModules.IsInvertible.isFiniteLocallyFree.{v, v, v} _, ?_⟩
  exact ⟨eL ≪≫ eR ≪≫ (asIso
    (Modules.tensorPullbackObjUnitToUnit (pullback.snd f (h ≫ k)))).symm⟩

end AlgebraicGeometry.Scheme
