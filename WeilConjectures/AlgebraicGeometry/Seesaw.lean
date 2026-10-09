/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import WeilConjectures.AlgebraicGeometry.Modules.IntegralSections

/-!
# The seesaw principle: closedness of the locus of triviality

Let `f : P ⟶ T` be proper, flat, locally of finite presentation and with geometrically integral
fibres, and let `M`, `N` be invertible modules on `P`. The set of points `t ∈ T` such that `M`
and `N` become isomorphic on the fibre `P_t` is closed in `T` (Stacks, Tags 0BDP and 0BF0; this
is the closedness half of Mumford's seesaw theorem).

On the fibre `P_t`, which is integral and proper over `κ(t)`, `M_t ≅ N_t` holds if and only if
both `M_t ⊗ N_tᵛ` and `N_t ⊗ M_tᵛ` have nonzero global sections
(`AlgebraicGeometry.Scheme.Modules.nonempty_iso_unit_of_tensorObj_iso_unit`). Both conditions
are closed in `t` by the upper semicontinuity of `t ↦ dim H⁰(P_t, -)`
(`AlgebraicGeometry.Scheme.Modules.upperSemicontinuous_hFiber`).

## Main statements

- `AlgebraicGeometry.Scheme.Modules.isClosed_setOf_nonempty_iso_fiber`: the locus of points
  over which `M` and `N` are isomorphic on the fibre is closed.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Tensor inverses are unique: if `A ⊗ B ≅ 𝒪` and `B ⊗ C ≅ 𝒪`, then `A ≅ C`. -/
lemma nonempty_iso_of_tensorObj_iso_unit_of_tensorObj_iso_unit {X : Scheme.{u}}
    {A B C : X.Modules} (e₁ : A ⊗ B ≅ 𝟙_ X.Modules) (e₂ : B ⊗ C ≅ 𝟙_ X.Modules) :
    Nonempty (A ≅ C) :=
  ⟨(ρ_ A).symm ≪≫ whiskerLeftIso A e₂.symm ≪≫ (α_ A B C).symm ≪≫ whiskerRightIso e₁ C ≪≫ λ_ C⟩

/-- `(M ⊗ Nᵛ) ⊗ (N ⊗ Mᵛ) ≅ 𝒪` for invertible modules `M`, `N`. -/
lemma nonempty_tensorObj_dual_tensorObj_tensorObj_dual_iso_unit {X : Scheme.{u}}
    (M N : X.Modules) [M.IsInvertible] [N.IsInvertible] :
    Nonempty ((M ⊗ Nᵛ) ⊗ (N ⊗ Mᵛ) ≅ 𝟙_ X.Modules) := by
  obtain ⟨dM⟩ := nonempty_tensorObj_dual_iso_unit M
  obtain ⟨dN⟩ := nonempty_tensorObj_dual_iso_unit N
  exact ⟨α_ _ _ _ ≪≫ whiskerLeftIso M ((α_ _ _ _).symm ≪≫ whiskerRightIso (β_ _ _ ≪≫ dN) _ ≪≫
    λ_ _) ≪≫ dM⟩

/-- On a `k`-scheme whose `H⁰(X, F)` is finite-dimensional, `h⁰(X, F) > 0` if and only if `F` has
a nonzero global section. -/
lemma pos_finrankH_zero_iff {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    (F : X.Modules) [FiniteDimensional k (F.H 0)] :
    0 < F.finrankH k 0 ↔ ∃ s : Γ(F, ⊤), s ≠ 0 := by
  rw [finrankH, Module.finrank_pos_iff_exists_ne_zero]
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨H.zeroLinearEquiv F x, by simpa using hx⟩,
    fun ⟨s, hs⟩ ↦ ⟨(H.zeroLinearEquiv F).symm s, by simpa using hs⟩⟩

variable {P T : Scheme.{u}}

/-- **The seesaw principle: the locus of triviality on the fibres is closed** (Stacks, Tags 0BDP
and 0BF0). Let `f : P ⟶ T` be proper, flat, locally of finite presentation and with geometrically
integral fibres, and let `M`, `N` be invertible modules on `P`. The set of points `t ∈ T` such
that `M` and `N` become isomorphic on the fibre `P_t` is closed.

On the integral fibre `P_t`, proper over `κ(t)`, `M_t ≅ N_t` if and only if `M_t ⊗ N_tᵛ` and
`N_t ⊗ M_tᵛ` both have nonzero global sections
(`AlgebraicGeometry.Scheme.Modules.nonempty_iso_unit_of_tensorObj_iso_unit`), i.e. if and only if
`h⁰(P_t, (M ⊗ Nᵛ)_t) ≥ 1` and `h⁰(P_t, (N ⊗ Mᵛ)_t) ≥ 1`. Both conditions are closed by upper
semicontinuity (`AlgebraicGeometry.Scheme.Modules.upperSemicontinuous_hFiber`). -/
theorem isClosed_setOf_nonempty_iso_fiber (f : P ⟶ T) [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] [GeometricallyIntegral f] (M N : P.Modules) [M.IsInvertible]
    [N.IsInvertible] :
    IsClosed {t : T | Nonempty ((Modules.pullback (f.fiberι t)).obj M ≅
      (Modules.pullback (f.fiberι t)).obj N)} := by
  have := isGrothendieckAbelian P
  have hfp {X : Scheme.{u}} (L : X.Modules) [L.IsInvertible] : L.IsFinitePresentation := by
    have : SheafOfModules.IsInvertible.{u, u, u} L := IsInvertible.sheafOfModules_isInvertible L
    have : SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
      SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
    exact SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  have hopen (L : P.Modules) [L.IsInvertible] : IsOpen {t | L.hFiber f 0 t < 1} :=
    have := hfp L
    have : SheafOfModules.IsInvertible.{u, u, u} L := IsInvertible.sheafOfModules_isInvertible L
    (upperSemicontinuous_hFiber f L (isFlatOver_of_isInvertible f L) 0).isOpen_preimage 1
  -- the fibrewise criterion
  have key (t : T) : Nonempty ((Modules.pullback (f.fiberι t)).obj M ≅
      (Modules.pullback (f.fiberι t)).obj N) ↔
      0 < (M ⊗ Nᵛ).hFiber f 0 t ∧ 0 < (N ⊗ Mᵛ).hFiber f 0 t := by
    let := f.fiberOverSpecResidueField t
    set g := f.fiberι t
    have : IsProper (f.fiberToSpecResidueField t) :=
      inferInstanceAs (IsProper (pullback.snd f (T.fromSpecResidueField t)))
    have hfield : IsField Γ(f.fiber t, ⊤) :=
      isField_of_universallyClosed (T.residueField t) (f.fiberToSpecResidueField t)
    have hfd (L : P.Modules) [L.IsInvertible] :
        FiniteDimensional (T.residueField t) (((Modules.pullback g).obj L).H 0) := by
      have : IsProper (f.fiber t ↘ Spec (T.residueField t)) := ‹IsProper (f.fiberToSpecResidueField t)›
      have := hfp ((Modules.pullback g).obj L)
      exact finiteDimensional_H_of_isProper _ 0
    have hpos (L : P.Modules) [L.IsInvertible] : 0 < L.hFiber f 0 t ↔
        ∃ s : Γ((Modules.pullback g).obj L, ⊤), s ≠ 0 :=
      have := hfd L
      pos_finrankH_zero_iff _
    rw [hpos, hpos]
    constructor
    · rintro ⟨e⟩
      have hne (L : P.Modules) (d : (Modules.pullback g).obj L ≅ 𝟙_ (f.fiber t).Modules) :
          ∃ s : Γ((Modules.pullback g).obj L, ⊤), s ≠ 0 := by
        refine ⟨d.inv.app ⊤ (1 : Γ(f.fiber t, ⊤)), fun h ↦ one_ne_zero (α := Γ(f.fiber t, ⊤)) ?_⟩
        exact (bijective_app_of_iso d.symm ⊤).1 (h.trans (map_zero _).symm)
      exact ⟨hne _ (nonempty_pullback_tensorObj_dual_iso_unit g M N e).some,
        hne _ (nonempty_pullback_tensorObj_dual_iso_unit g N M e.symm).some⟩
    · rintro ⟨⟨s, hs⟩, ⟨s', hs'⟩⟩
      obtain ⟨u⟩ := nonempty_tensorObj_dual_tensorObj_tensorObj_dual_iso_unit M N
      obtain ⟨μ⟩ := nonempty_pullback_tensorObj_iso g (M ⊗ Nᵛ) (N ⊗ Mᵛ)
      obtain ⟨d⟩ := nonempty_iso_unit_of_tensorObj_iso_unit hfield
        (μ.symm ≪≫ (Modules.pullback g).mapIso u ≪≫ pullbackObjUnitIso g) hs hs'
      obtain ⟨μM⟩ := nonempty_pullback_tensorObj_iso g M Nᵛ
      obtain ⟨μN⟩ := nonempty_pullback_tensorObj_iso g Nᵛ N
      obtain ⟨dN⟩ := nonempty_tensorObj_dual_iso_unit N
      exact nonempty_iso_of_tensorObj_iso_unit_of_tensorObj_iso_unit (μM.symm ≪≫ d)
        (μN.symm ≪≫ (Modules.pullback g).mapIso (β_ _ _ ≪≫ dN) ≪≫ pullbackObjUnitIso g)
  have hset : {t : T | Nonempty ((Modules.pullback (f.fiberι t)).obj M ≅
      (Modules.pullback (f.fiberι t)).obj N)} =
      {t | (M ⊗ Nᵛ).hFiber f 0 t < 1}ᶜ ∩ {t | (N ⊗ Mᵛ).hFiber f 0 t < 1}ᶜ := by
    ext t
    simp only [Set.mem_ofPred_eq, key, Set.mem_inter_iff, Set.mem_compl_iff, not_lt,
      Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]
  rw [hset]
  exact (hopen _).isClosed_compl.inter (hopen _).isClosed_compl

end AlgebraicGeometry.Scheme.Modules
