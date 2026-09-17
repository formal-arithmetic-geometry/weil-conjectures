/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.BaseChange
public import WeilConjectures.AlgebraicGeometry.Modules.FibrewiseCriteria
public import WeilConjectures.AlgebraicGeometry.Modules.Flat
public import WeilConjectures.AlgebraicGeometry.Modules.TrivialLineBundle
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Integral
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-!
# The seesaw theorem

Let `X` be a proper variety over a field `K`, let `T` be a reduced `K`-scheme of finite type and
let `L` be a line bundle on `X × T` whose restriction `L_t` to the fibre `X_t` is trivial for
every closed point `t` of `T`. The **seesaw theorem** says that `M := p_{T*} L` is again a line
bundle and that the counit `ε : p_T^* M ⟶ L` of the adjunction `p_T^* ⊣ p_{T*}` is an
isomorphism: `L` is the pullback of a line bundle on the base. Its **triviality form** adds the
hypothesis that `L` is trivial on one slice `{x₀} × T` and concludes that `L` itself is trivial.

The two inputs which are `sorry` by design are consumed as black boxes: the semicontinuity of
`h⁰` (`AlgebraicGeometry.Scheme.Modules.isClosed_setOf_le_finrankFiberSections`) and Grauert's
theorem (`AlgebraicGeometry.Scheme.Modules.invertible_pushforward_of_finrankFiberSections_eq_one`
and `AlgebraicGeometry.Scheme.Modules.isIso_fiberBaseChangeMap_of_finrankFiberSections_eq`).
Nothing else in this file is `sorry`.

## Main results

- `AlgebraicGeometry.Scheme.Modules.finrankFiberSections_pullbackSnd_eq_one` (blueprint
  `lem:cube-h0-constant`): **`h⁰` is identically one** on a `K`-scheme of finite type `T`, as
  soon as the restriction of `L` to the fibre over every closed point of `T` is trivial.
- `AlgebraicGeometry.Scheme.Modules.isIso_counit_pullbackSnd` together with
  `AlgebraicGeometry.Scheme.Modules.invertible_pushforward_pullbackSnd` (blueprint
  `thm:cube-seesaw`): **the seesaw theorem.**
- `AlgebraicGeometry.Scheme.Modules.nonempty_iso_structureModules_pullbackSnd` (blueprint
  `cor:cube-seesaw-trivial`): **the triviality form of the seesaw theorem.**

All four are proved in the generality they are used in, for an arbitrary proper morphism
`f : W ⟶ T` over a reduced Noetherian Jacobson base, and then specialised to the projection: see
`AlgebraicGeometry.Scheme.Modules.finrankFiberSections_eq_of_forall_closedPoint`,
`AlgebraicGeometry.Scheme.Modules.isIso_counit_of_restrictToFiber_iso` and
`AlgebraicGeometry.Scheme.Modules.nonempty_iso_structureModules_of_section`.

## Implementation notes

* **Closed points, not `K`-rational points.** The blueprint states the hypothesis "`L_t` is
  trivial" for `t ∈ T(k)`, over an algebraically closed `k`; the statements below ask for it at
  every *closed point* of `T` instead. Over an algebraically closed field the two agree
  (`AlgebraicGeometry.pointEquivClosedPoint`), and the closed-point form is what the Jacobson
  argument uses and what holds over any field.
* `SheafOfModules.Invertible` is a `Prop`-valued `def`, not a class, so every statement below
  takes it as an explicit hypothesis `hL : L.Invertible`, and its consequences
  `SheafOfModules.Invertible.isCoherent` and `SheafOfModules.Invertible.flatOver` are theorems
  and not instances. The specialisations to the projection introduce them, together with the
  Noetherian and Jacobson properties of the base, through the private lemma
  `AlgebraicGeometry.Scheme.Modules.seesawHypotheses`.

## Blueprint

`lem:cube-h0-constant`, `thm:cube-seesaw` and `cor:cube-seesaw-trivial` of
`blueprint/src/version/detailed/curve_estimates/27_theorem_of_the_cube.tex`; the flatness input
`lem:cube-projection-proper-flat` (4) is `SheafOfModules.Invertible.flatOver` in
`WeilConjectures.AlgebraicGeometry.Modules.Flat`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory SheafOfModules TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-! ### The counit of the free-module adjunction on a fibre -/

section Fibres

variable {W T : Scheme.{u}}

/-- **The evaluation map `Γ(W_t, G) ⊗_{κ(t)} 𝒪_{W_t} ⟶ G` is non-zero on the fibre at a point
where some global section of `G` is non-zero.** -/
lemma fiberMap_fiberFreeAdjunction_counit_ne_zero (f : W ⟶ T) (t : T) {G : (f.fiber t).Modules}
    (w : f.fiber t) (σ : Γ(G, ⊤)) (hσ : fiberMk G w σ ≠ 0) :
    fiberMap ((fiberFreeAdjunction f t).counit.app G) w ≠ 0 := by
  refine fiberMap_ne_zero_of_fiberMk_ne_zero _ w
    ((fiberFreeAdjunction f t).unit.app ((fiberSectionsFunctor f t).obj G) σ) ?_
  have h : Hom.app ((fiberFreeAdjunction f t).counit.app G) ⊤
      ((fiberFreeAdjunction f t).unit.app ((fiberSectionsFunctor f t).obj G) σ) = σ := by
    have h' := ConcreteCategory.congr_hom
      ((fiberFreeAdjunction f t).right_triangle_components G) σ
    rwa [ConcreteCategory.comp_apply] at h'
  rwa [h]

end Fibres

/-! ### `h⁰` is constant -/

section ConstantH0

variable {W T : Scheme.{u}}

/-- **The fibrewise dimension of the global sections of a line bundle is one at a point where
the fibre is trivial**, provided the fibre of `f` there is a proper geometrically integral
scheme over the residue field. -/
theorem finrankFiberSections_eq_one_of_restrictToFiber_iso (f : W ⟶ T) [IsProper f]
    (F : W.Modules) (t : T) [GeometricallyIntegral (f.fiberToSpecResidueField t)]
    (e : (restrictToFiber f t).obj F ≅ (f.fiber t).structureModules) :
    finrankFiberSections f F t = 1 := by
  let _ : (f.fiber t).Over (Spec (.of ↥(T.residueField t))) := ⟨f.fiberToSpecResidueField t⟩
  have : IsProper ((f.fiber t) ↘ Spec (.of ↥(T.residueField t))) :=
    inferInstanceAs (IsProper (f.fiberToSpecResidueField t))
  have : GeometricallyIntegral ((f.fiber t) ↘ Spec (.of ↥(T.residueField t))) :=
    inferInstanceAs (GeometricallyIntegral (f.fiberToSpecResidueField t))
  exact finrank_sections_eq_one_of_iso_unit_of_geometricallyIntegral
    (K := ↥(T.residueField t)) (X := f.fiber t) (L := (restrictToFiber f t).obj F) e

/-- **`h⁰` is constant as soon as it is constant on the closed points** of a Noetherian Jacobson
base.

The locus `{h⁰ ≥ n + 1}` is closed by semicontinuity and misses every closed point, hence is
empty; the locus `{h⁰ ≥ n}` is closed and contains every closed point, which are dense, hence is
everything.

This is `lem:cube-h0-constant` of the blueprint, for an arbitrary value `n` in place of `1`. -/
theorem finrankFiberSections_eq_of_forall_closedPoint {n : ℕ} [JacobsonSpace T] [IsNoetherian T]
    (f : W ⟶ T) [IsProper f] (F : W.Modules) [F.IsCoherent] [F.FlatOver f]
    (h : ∀ t ∈ closedPoints T, finrankFiberSections f F t = n) (t : T) :
    finrankFiberSections f F t = n := by
  have hcs : IsClosed {s : T | n + 1 ≤ finrankFiberSections f F s} :=
    isClosed_setOf_le_finrankFiberSections f F (n + 1)
  have hc : IsClosed {s : T | n ≤ finrankFiberSections f F s} :=
    isClosed_setOf_le_finrankFiberSections f F n
  have hlt : finrankFiberSections f F t < n + 1 := by
    by_contra hcon
    obtain ⟨s, hs, hsc⟩ :=
      nonempty_inter_closedPoints (Z := {s : T | n + 1 ≤ finrankFiberSections f F s})
        ⟨t, not_lt.1 hcon⟩ hcs.isLocallyClosed
    rw [Set.mem_ofPred_eq, h s hsc] at hs
    omega
  have hge : n ≤ finrankFiberSections f F t := by
    have hsub : closedPoints T ⊆ {s : T | n ≤ finrankFiberSections f F s} :=
      fun x hx ↦ (h x hx).ge
    have hcl := closure_mono hsub
    rw [closure_closedPoints, hc.closure_eq] at hcl
    exact hcl (Set.mem_univ t)
  omega

end ConstantH0

/-! ### The seesaw theorem -/

section Seesaw

variable {W T : Scheme.{u}} (f : W ⟶ T) {L : W.Modules}

/-- **The counit is non-zero on the fibre at a point lying over a point where `L` is trivial.**

On the fibre over `t` the counit is, by `lem:cube-counit-fibre` and Grauert's theorem, the
evaluation map of the one-dimensional space `Γ(W_t, L_t)`, and a trivialisation of `L_t`
provides a nowhere vanishing section. -/
lemma fiberMap_counit_ne_zero_of_restrictToFiber_iso [IsReduced T] [IsNoetherian T] [IsProper f]
    (hL : L.Invertible) [L.FlatOver f] (h1 : ∀ s : T, finrankFiberSections f L s = 1) (t : T)
    (e : (restrictToFiber f t).obj L ≅ (f.fiber t).structureModules) (w : W) (hw : f w = t) :
    fiberMap ((pullbackPushforwardAdjunction f).counit.app L) w ≠ 0 := by
  have := hL.isCoherent
  have hM : ((pushforward f).obj L).Invertible :=
    invertible_pushforward_of_finrankFiberSections_eq_one f L h1
  have : ((Modules.pullback (T.fromSpecResidueField t)).obj
      ((pushforward f).obj L)).IsQuasicoherent :=
    have := (SheafOfModules.Invertible.pullback (T.fromSpecResidueField t) hM).isLocallyFree
    inferInstance
  have : IsIso (fiberBaseChangeMap f L t) :=
    isIso_fiberBaseChangeMap_of_finrankFiberSections_eq f L t h1
  obtain ⟨σ, hσ⟩ := exists_forall_fiberMk_ne_zero e
  obtain ⟨w', hw'⟩ : w ∈ Set.range (f.fiberι t) := by rwa [f.range_fiberι t]
  intro hzero
  rw [← hw', ← fiberMap_pullback_map_eq_zero_iff (f.fiberι t) w'
    ((pullbackPushforwardAdjunction f).counit.app L)] at hzero
  have key := congrArg (fun ψ ↦ fiberMap ψ w') (fiberFreeComparison_comp_map_counit f L t)
  simp only [fiberMap_comp] at key
  rw [hzero, comp_zero] at key
  refine fiberMap_fiberFreeAdjunction_counit_ne_zero f t w' σ (hσ w') ?_
  rw [← Preadditive.IsIso.comp_left_eq_zero
    (fiberMap ((fiberFreeFunctor f t).map (fiberBaseChangeMap f L t)) w')]
  exact key.symm

/-- **The seesaw theorem.** Let `f : W ⟶ T` be a proper morphism over a reduced Noetherian
Jacobson base, let `L` be a line bundle on `W` which is flat over `T` with constant fibrewise
`h⁰ = 1`, and suppose that the restriction of `L` to the fibre over every closed point of `T` is
trivial. Then the counit `ε : f^* f_* L ⟶ L` is an isomorphism.

The direct image `f_* L` is a line bundle by Grauert's theorem, so `ε` is a morphism of line
bundles and it is enough to see that it is non-zero on every fibre. The locus where it vanishes
is closed, its image in `T` is closed because `f` is proper, and that image misses every closed
point of `T`; a non-empty closed subset of a Jacobson space contains a closed point, so the
locus is empty.

This is `thm:cube-seesaw` of the blueprint. -/
theorem isIso_counit_of_restrictToFiber_iso [IsReduced T] [IsNoetherian T] [JacobsonSpace T]
    [IsProper f] (hL : L.Invertible) [L.FlatOver f]
    (h1 : ∀ s : T, finrankFiberSections f L s = 1)
    (htriv : ∀ t ∈ closedPoints T,
      Nonempty ((restrictToFiber f t).obj L ≅ (f.fiber t).structureModules)) :
    IsIso ((pullbackPushforwardAdjunction f).counit.app L) := by
  have hM : ((pushforward f).obj L).Invertible :=
    have := hL.isCoherent
    invertible_pushforward_of_finrankFiberSections_eq_one f L h1
  refine isIso_of_forall_fiberMap_ne_zero (SheafOfModules.Invertible.pullback f hM) hL _
    fun w ↦ ?_
  by_contra hw
  have hNclosed :
      IsClosed {v : W | fiberMap ((pullbackPushforwardAdjunction f).counit.app L) v = 0} :=
    isClosed_setOf_fiberMap_eq_zero (SheafOfModules.Invertible.pullback f hM) hL _
  have himg := f.isClosedMap _ hNclosed
  obtain ⟨t, ⟨v, hv, hvt⟩, htc⟩ :=
    nonempty_inter_closedPoints (Z := f.base '' _) ⟨f w, w, hw, rfl⟩ himg.isLocallyClosed
  obtain ⟨e⟩ := htriv t htc
  exact fiberMap_counit_ne_zero_of_restrictToFiber_iso f hL h1 t e v hvt hv

/-- **The seesaw theorem, triviality form.** In the situation of
`AlgebraicGeometry.Scheme.Modules.isIso_counit_of_restrictToFiber_iso`, if moreover the pullback
of `L` along some section `s` of `f` is trivial, then `L` itself is trivial: the counit
identifies `L` with `f^* (f_* L)`, and pulling that back along `s` identifies `f_* L` with
`s^* L`.

This is `cor:cube-seesaw-trivial` of the blueprint. -/
theorem nonempty_iso_structureModules_of_section [IsReduced T] [IsNoetherian T] [JacobsonSpace T]
    [IsProper f] (hL : L.Invertible) [L.FlatOver f]
    (h1 : ∀ s : T, finrankFiberSections f L s = 1)
    (htriv : ∀ t ∈ closedPoints T,
      Nonempty ((restrictToFiber f t).obj L ≅ (f.fiber t).structureModules))
    (s : T ⟶ W) (hs : s ≫ f = 𝟙 T)
    (hsec : Nonempty ((Modules.pullback s).obj L ≅ T.structureModules)) :
    Nonempty (L ≅ W.structureModules) := by
  obtain ⟨e⟩ := hsec
  have := isIso_counit_of_restrictToFiber_iso f hL h1 htriv
  let ε := asIso ((pullbackPushforwardAdjunction f).counit.app L)
  exact ⟨ε.symm ≪≫ (Modules.pullback f).mapIso
    ((pullbackSectionIso f s hs ((pushforward f).obj L)).symm ≪≫
      (Modules.pullback s).mapIso ε ≪≫ e) ≪≫ Modules.pullbackUnitIso f⟩

end Seesaw

/-! ### The seesaw theorem for the projection `X × T ⟶ T` -/

section Projection

variable {T : Scheme.{u}} {K : Type u} [Field K] {X : Scheme.{u}}
  (πX : X ⟶ Spec (.of K)) (πT : T ⟶ Spec (.of K))

variable [IsProper πX] [GeometricallyIntegral πX] [LocallyOfFiniteType πT] [QuasiCompact πT]
  {L : (Limits.pullback πX πT).Modules} (hL : L.Invertible)

omit [IsProper πX] [GeometricallyIntegral πX] in
include hL in
/-- The standing hypotheses of the seesaw theorem for the projection `p_T : X × T ⟶ T`: the base
is Noetherian and Jacobson, and `L` is coherent and flat over the base. This is
`lem:cube-projection-proper-flat` of the blueprint, packaged so that each of the statements
below introduces all four facts at once. -/
private theorem seesawHypotheses :
    IsNoetherian T ∧ JacobsonSpace T ∧ L.IsCoherent ∧
      L.FlatOver (Limits.pullback.snd πX πT) :=
  ⟨isNoetherian_of_locallyOfFiniteType πT, LocallyOfFiniteType.jacobsonSpace πT, hL.isCoherent,
    hL.flatOver _⟩

include hL in
/-- **`h⁰` is identically one for a line bundle on `X × T`** which is trivial on the fibre over
every closed point of `T`. This is `lem:cube-h0-constant` of the blueprint. -/
theorem finrankFiberSections_pullbackSnd_eq_one
    (htriv : ∀ t ∈ closedPoints T,
      Nonempty ((restrictToFiber (Limits.pullback.snd πX πT) t).obj L ≅
        ((Limits.pullback.snd πX πT).fiber t).structureModules))
    (t : T) : finrankFiberSections (Limits.pullback.snd πX πT) L t = 1 := by
  obtain ⟨_, _, _, _⟩ := seesawHypotheses πX πT hL
  exact finrankFiberSections_eq_of_forall_closedPoint _ L
    (fun s hs ↦ finrankFiberSections_eq_one_of_restrictToFiber_iso _ L s (htriv s hs).some) t

include hL in
/-- **The direct image `p_{T*} L` is a line bundle on `T`.** This is the first half of
`thm:cube-seesaw` of the blueprint, and is Grauert's theorem in rank one. -/
theorem invertible_pushforward_pullbackSnd [IsReduced T]
    (htriv : ∀ t ∈ closedPoints T,
      Nonempty ((restrictToFiber (Limits.pullback.snd πX πT) t).obj L ≅
        ((Limits.pullback.snd πX πT).fiber t).structureModules)) :
    ((pushforward (Limits.pullback.snd πX πT)).obj L).Invertible := by
  obtain ⟨_, _, _, _⟩ := seesawHypotheses πX πT hL
  exact invertible_pushforward_of_finrankFiberSections_eq_one _ L
    (finrankFiberSections_pullbackSnd_eq_one πX πT hL htriv)

include hL in
/-- **The seesaw theorem.** For a proper variety `X` over a field `K`, a reduced `K`-scheme `T`
of finite type and a line bundle `L` on `X × T` whose restriction to the fibre over every closed
point of `T` is trivial, the counit `p_T^* p_{T*} L ⟶ L` is an isomorphism; together with
`AlgebraicGeometry.Scheme.Modules.invertible_pushforward_pullbackSnd` this says that `L` is the
pullback of a line bundle on `T`.

This is `thm:cube-seesaw` of the blueprint. -/
theorem isIso_counit_pullbackSnd [IsReduced T]
    (htriv : ∀ t ∈ closedPoints T,
      Nonempty ((restrictToFiber (Limits.pullback.snd πX πT) t).obj L ≅
        ((Limits.pullback.snd πX πT).fiber t).structureModules)) :
    IsIso ((pullbackPushforwardAdjunction (Limits.pullback.snd πX πT)).counit.app L) := by
  obtain ⟨_, _, _, _⟩ := seesawHypotheses πX πT hL
  exact isIso_counit_of_restrictToFiber_iso _ hL
    (finrankFiberSections_pullbackSnd_eq_one πX πT hL htriv) htriv

include hL in
/-- **The seesaw theorem, triviality form.** If in addition the restriction of `L` to the slice
`{x₀} × T` through a rational point `x₀` of `X` is trivial, then `L` is trivial.

This is `cor:cube-seesaw-trivial` of the blueprint. -/
theorem nonempty_iso_structureModules_pullbackSnd [IsReduced T]
    (htriv : ∀ t ∈ closedPoints T,
      Nonempty ((restrictToFiber (Limits.pullback.snd πX πT) t).obj L ≅
        ((Limits.pullback.snd πX πT).fiber t).structureModules))
    (x₀ : Spec (.of K) ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 _)
    (hsec : Nonempty ((Modules.pullback (sliceInclusionSnd πX πT x₀ hx₀)).obj L ≅
      T.structureModules)) :
    Nonempty (L ≅ (Limits.pullback πX πT).structureModules) := by
  obtain ⟨_, _, _, _⟩ := seesawHypotheses πX πT hL
  exact nonempty_iso_structureModules_of_section _ hL
    (finrankFiberSections_pullbackSnd_eq_one πX πT hL htriv) htriv
    (sliceInclusionSnd πX πT x₀ hx₀) (sliceInclusionSnd_snd πX πT x₀ hx₀) hsec

end Projection

end AlgebraicGeometry.Scheme.Modules
