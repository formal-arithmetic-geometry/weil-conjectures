/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Semicontinuity
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
public import WeilConjectures.AlgebraicGeometry.Modules.TrivialityCriterion

/-!
# The triviality locus of a line bundle is closed

Let `X` be a proper geometrically integral variety over a field `K`, let `T` be a Noetherian
`K`-scheme and let `L` be a line bundle on `X × T`. The set of points `t` of `T` at which the
restriction `L_t` of `L` to the fibre `X_t` is a trivial line bundle is **closed** in `T`.

The proof is the one of the blueprint. By the triviality criterion read on a fibre
(`AlgebraicGeometry.Scheme.Modules.nonempty_restrictToFiber_iso_structureModules_iff_nontrivial`),
the bundle `L_t` is trivial exactly when both `Γ(X_t, L_t)` and `Γ(X_t, N_t)` are non-zero, where
`N` is a tensor inverse of `L`. Non-vanishing of a fibrewise space of sections is the inequality
`1 ≤ h⁰`, and each of the two loci `{t | 1 ≤ h⁰}` is closed by the semicontinuity of `h⁰`
(`AlgebraicGeometry.Scheme.Modules.isClosed_setOf_le_finrankFiberSections`). The triviality locus
is their intersection.

## Main statements

All three are in the namespace `AlgebraicGeometry.Scheme.Modules`.

- `nonempty_restrictToFiber_iso_structureModules_iff`: the restriction of `L` to the fibre over
  `t` is trivial if and only if both fibrewise dimensions `h⁰(L, t)` and `h⁰(N, t)` are at least
  one.
- `isClosed_setOf_nonempty_restrictToFiber_iso_structureModules`: **the triviality locus is
  closed**, for an arbitrary proper flat morphism `f : W ⟶ T` onto a Noetherian base all of whose
  fibres are geometrically integral.
- `isClosed_setOf_nonempty_restrictToFiber_pullbackSnd_iso_structureModules` (blueprint
  `cor:cube-triviality-closed`): the same statement for the projection `p_T : X × T ⟶ T`, which
  is the form the blueprint states.

## Implementation notes

* The pointwise criterion carries the tensor inverse of `L` as an explicit isomorphism
  `e : L ⊗ N ≅ 𝟙_ W.Modules`, as the triviality criterion it feeds does, because `N` occurs in
  its statement. Its restriction to a fibre is obtained from the monoidal structure of the
  pullback functor, `CategoryTheory.Functor.Monoidal.mapIsoTensorUnit`. The two closedness
  statements take `hL : L.Invertible` instead, as the seesaw theorems do: `N` does not occur in
  their conclusion, and `SheafOfModules.Invertible.tensorInv` produces one.
* The predicate is spelled `Nonempty ((restrictToFiber f t).obj L ≅ (f.fiber t).structureModules)`
  rather than with the monoidal unit `𝟙_ ((f.fiber t).Modules)`, so that it is literally the
  hypothesis `htriv` of the seesaw theorem in `WeilConjectures.AlgebraicGeometry.Seesaw`. The two
  differ by `AlgebraicGeometry.Scheme.Modules.nonempty_iso_structureModules_iff`.
* Everything here is `sorry`-tainted through `isClosed_setOf_le_finrankFiberSections`, which is
  `sorry` by design; nothing in this file is.

## Blueprint

`isClosed_setOf_nonempty_restrictToFiber_pullbackSnd_iso_structureModules` implements
`cor:cube-triviality-closed` of the chapter on the theorem of the cube.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

section General

variable {W T : Scheme.{u}}

/-- **Triviality of `L` on the fibre over `t` is the inequality `1 ≤ h⁰` for the two fibrewise
spaces of sections** `Γ(W_t, L_t)` and `Γ(W_t, N_t)`, where `N` is a tensor inverse of `L`.

This is
`AlgebraicGeometry.Scheme.Modules.nonempty_restrictToFiber_iso_structureModules_iff_nontrivial`
with the non-vanishing of a finite-dimensional space rewritten as `1 ≤ h⁰`. -/
theorem nonempty_restrictToFiber_iso_structureModules_iff (f : W ⟶ T) [IsProper f]
    {L N : W.Modules} (e : L ⊗ N ≅ 𝟙_ W.Modules) (t : T)
    [GeometricallyIntegral (f.fiberToSpecResidueField t)] :
    Nonempty ((restrictToFiber f t).obj L ≅ (f.fiber t).structureModules) ↔
      1 ≤ finrankFiberSections f L t ∧ 1 ≤ finrankFiberSections f N t := by
  have : L.IsCoherent := (SheafOfModules.Invertible.left (R := W.sheaf) e).isCoherent
  have : N.IsCoherent := (SheafOfModules.Invertible.right (R := W.sheaf) e).isCoherent
  rw [nonempty_restrictToFiber_iso_structureModules_iff_nontrivial f e t,
    one_le_finrankFiberSections_iff f L t, one_le_finrankFiberSections_iff f N t]

/-- **The triviality locus of a line bundle is closed**, for a proper flat morphism `f : W ⟶ T`
onto a Noetherian base whose fibres are all geometrically integral: the set of points `t` of `T`
at which the restriction of `L` to the fibre `W_t` is a trivial line bundle is closed in `T`. -/
theorem isClosed_setOf_nonempty_restrictToFiber_iso_structureModules [IsNoetherian T] (f : W ⟶ T)
    [IsProper f] [Flat f] {L : W.Modules} (hL : L.Invertible)
    (hgeom : ∀ t : T, GeometricallyIntegral (f.fiberToSpecResidueField t)) :
    IsClosed {t : T | Nonempty ((restrictToFiber f t).obj L ≅ (f.fiber t).structureModules)} := by
  set N : W.Modules := hL.tensorInv with hNdef
  have hN : N.Invertible := hNdef ▸ SheafOfModules.invertible_tensorInv hL
  have : L.IsCoherent := hL.isCoherent
  have : N.IsCoherent := hN.isCoherent
  have : L.FlatOver f := hL.flatOver f
  have : N.FlatOver f := hN.flatOver f
  have hset : {t : T | Nonempty ((restrictToFiber f t).obj L ≅ (f.fiber t).structureModules)} =
      {t : T | 1 ≤ finrankFiberSections f L t} ∩ {t : T | 1 ≤ finrankFiberSections f N t} := by
    ext t
    have := hgeom t
    exact nonempty_restrictToFiber_iso_structureModules_iff f hL.tensorInvIso t
  rw [hset]
  exact (isClosed_setOf_le_finrankFiberSections f L 1).inter
    (isClosed_setOf_le_finrankFiberSections f N 1)

end General

section Projection

variable {T : Scheme.{u}} {K : Type u} [Field K] {X : Scheme.{u}}
  (πX : X ⟶ Spec (.of K)) (πT : T ⟶ Spec (.of K))

variable [IsProper πX] [GeometricallyIntegral πX] [IsNoetherian T]
  {L : (Limits.pullback πX πT).Modules}

/-- **The triviality locus of a line bundle on `X × T` is closed.** For `X` a proper
geometrically integral variety over a field `K`, `T` a Noetherian `K`-scheme and `L` a line
bundle on `X × T`, the set of points `t` of `T` at which the restriction `L_t` of `L` to the
fibre `X_t` is a trivial line bundle is closed in `T`.

This is `cor:cube-triviality-closed` of the blueprint. -/
theorem isClosed_setOf_nonempty_restrictToFiber_pullbackSnd_iso_structureModules
    (hL : L.Invertible) :
    IsClosed {t : T | Nonempty ((restrictToFiber (Limits.pullback.snd πX πT) t).obj L ≅
      ((Limits.pullback.snd πX πT).fiber t).structureModules)} :=
  isClosed_setOf_nonempty_restrictToFiber_iso_structureModules _ hL fun _ ↦ inferInstance

end Projection

end AlgebraicGeometry.Scheme.Modules
