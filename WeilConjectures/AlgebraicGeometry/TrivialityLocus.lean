/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Semicontinuity
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
public import WeilConjectures.AlgebraicGeometry.Modules.TrivialityCriterion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Integral
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor

/-!
# The triviality locus of a line bundle is closed

Let `X` be a proper geometrically integral variety over a field `K`, let `T` be a Noetherian
`K`-scheme and let `L` be a line bundle on `X × T`. The set of points `t` of `T` at which the
restriction `L_t` of `L` to the fibre `X_t` is a trivial line bundle is **closed** in `T`.

The proof is the one of the blueprint. By the triviality criterion over a field
(`AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_iff_of_geometricallyIntegral`),
applied on the fibre `X_t` over the residue field `κ(t)` — which is not assumed algebraically
closed — the bundle `L_t` is trivial exactly when both `Γ(X_t, L_t)` and `Γ(X_t, N_t)` are
non-zero, where `N` is a tensor inverse of `L`. Non-vanishing of a fibrewise space of sections is
the inequality `1 ≤ h⁰`, and each of the two loci `{t | 1 ≤ h⁰}` is closed by the semicontinuity
of `h⁰` (`AlgebraicGeometry.Scheme.Modules.isClosed_setOf_le_finrankFiberSections`). The
triviality locus is their intersection.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.nonempty_restrictToFiber_iso_structureModules_iff`:
  the restriction of `L` to the fibre over `t` is trivial if and only if both fibrewise
  dimensions `h⁰(L, t)` and `h⁰(N, t)` are at least one.
- `AlgebraicGeometry.Scheme.Modules.isClosed_setOf_nonempty_restrictToFiber_iso`: **the
  triviality locus is closed**, for an arbitrary proper flat morphism `f : W ⟶ T` onto a
  Noetherian base all of whose fibres are geometrically integral.
- `AlgebraicGeometry.Scheme.Modules.isClosed_setOf_nonempty_restrictToFiber_pullbackSnd_iso`
  (blueprint `cor:cube-triviality-closed`): the same statement for the projection
  `p_T : X × T ⟶ T`, which is the form the blueprint states.

## Implementation notes

* The tensor inverse of `L` is carried as an explicit isomorphism `e : L ⊗ N ≅ 𝟙_ W.Modules`,
  not through an inverse operation, exactly as in the triviality criterion it feeds. Its
  restriction to a fibre is obtained from the monoidal structure of the pullback functor,
  `CategoryTheory.Functor.Monoidal.mapIsoTensorUnit`.
* The predicate is spelled `Nonempty ((restrictToFiber f t).obj L ≅ (f.fiber t).structureModules)`
  rather than with the monoidal unit `𝟙_ ((f.fiber t).Modules)`, so that it is literally the
  hypothesis `htriv` of the seesaw theorem in `WeilConjectures.AlgebraicGeometry.Seesaw`. The two
  differ by `AlgebraicGeometry.Scheme.Modules.tensorUnitIsoUnit`.
* Everything here is `sorry`-tainted through `isClosed_setOf_le_finrankFiberSections`, which is
  `sorry` by design; nothing in this file is.

## Blueprint

`isClosed_setOf_nonempty_restrictToFiber_pullbackSnd_iso` implements `cor:cube-triviality-closed`
of the chapter on the theorem of the cube.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory SheafOfModules TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

section Fibre

variable {W T : Scheme.{u}}

/-- **The restriction to a fibre of a tensor-inverse pair is a tensor-inverse pair.** If `N` is a
tensor inverse of `L` on `W`, then `N_t` is a tensor inverse of `L_t` on the fibre of
`f : W ⟶ T` over `t`; this is the monoidality of the pullback functor. -/
noncomputable def restrictToFiberIsoTensorUnit (f : W ⟶ T) {L N : W.Modules}
    (e : L ⊗ N ≅ 𝟙_ W.Modules) (t : T) :
    (restrictToFiber f t).obj L ⊗ (restrictToFiber f t).obj N ≅ 𝟙_ ((f.fiber t).Modules) :=
  Functor.Monoidal.mapIsoTensorUnit (restrictToFiber f t) e

/-- **Triviality of `L` on the fibre over `t` is the non-vanishing of the two fibrewise spaces of
sections** `Γ(W_t, L_t)` and `Γ(W_t, N_t)`, where `N` is a tensor inverse of `L`.

This is the triviality criterion over a field
(`AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_iff_of_geometricallyIntegral`) read on
the fibre `W_t`, which is proper and geometrically integral over the residue field `κ(t)`, with
the non-vanishing of a finite-dimensional space rewritten as `1 ≤ h⁰`. -/
theorem nonempty_restrictToFiber_iso_structureModules_iff (f : W ⟶ T) [IsProper f]
    {L N : W.Modules} (e : L ⊗ N ≅ 𝟙_ W.Modules) (t : T)
    [GeometricallyIntegral (f.fiberToSpecResidueField t)] :
    Nonempty ((restrictToFiber f t).obj L ≅ (f.fiber t).structureModules) ↔
      1 ≤ finrankFiberSections f L t ∧ 1 ≤ finrankFiberSections f N t := by
  have hL : L.IsCoherent := (SheafOfModules.Invertible.left (R := W.sheaf) e).isCoherent
  have hN : N.IsCoherent := (SheafOfModules.Invertible.right (R := W.sheaf) e).isCoherent
  let _ : (f.fiber t).Over (Spec (.of ↥(T.residueField t))) := ⟨f.fiberToSpecResidueField t⟩
  have : IsProper ((f.fiber t) ↘ Spec (.of ↥(T.residueField t))) :=
    inferInstanceAs (IsProper (f.fiberToSpecResidueField t))
  have : GeometricallyIntegral ((f.fiber t) ↘ Spec (.of ↥(T.residueField t))) :=
    inferInstanceAs (GeometricallyIntegral (f.fiberToSpecResidueField t))
  have hunit : Nonempty ((restrictToFiber f t).obj L ≅ (f.fiber t).structureModules) ↔
      Nonempty ((restrictToFiber f t).obj L ≅ 𝟙_ ((f.fiber t).Modules)) :=
    ⟨fun ⟨i⟩ ↦ ⟨i ≪≫ (tensorUnitIsoUnit (f.fiber t)).symm⟩,
      fun ⟨i⟩ ↦ ⟨i ≪≫ tensorUnitIsoUnit (f.fiber t)⟩⟩
  rw [hunit, nonempty_iso_tensorUnit_iff_of_geometricallyIntegral (X := f.fiber t)
      ↥(T.residueField t) (restrictToFiberIsoTensorUnit f e t),
    one_le_finrankFiberSections_iff f L t, one_le_finrankFiberSections_iff f N t]

end Fibre

section General

variable {W T : Scheme.{u}}

/-- **The triviality locus of a line bundle is closed**, for a proper flat morphism `f : W ⟶ T`
onto a Noetherian base whose fibres are all geometrically integral: the set of points `t` of `T`
at which the restriction of `L` to the fibre `W_t` is a trivial line bundle is closed in `T`.

The tensor inverse of `L` is carried as an explicit isomorphism `e : L ⊗ N ≅ 𝒪_W`. -/
theorem isClosed_setOf_nonempty_restrictToFiber_iso [IsNoetherian T] (f : W ⟶ T) [IsProper f]
    [Flat f] {L N : W.Modules} (e : L ⊗ N ≅ 𝟙_ W.Modules)
    (hgeom : ∀ t : T, GeometricallyIntegral (f.fiberToSpecResidueField t)) :
    IsClosed {t : T | Nonempty ((restrictToFiber f t).obj L ≅ (f.fiber t).structureModules)} := by
  have hL := SheafOfModules.Invertible.left (R := W.sheaf) e
  have hN := SheafOfModules.Invertible.right (R := W.sheaf) e
  have : L.IsCoherent := hL.isCoherent
  have : N.IsCoherent := hN.isCoherent
  have : L.FlatOver f := hL.flatOver f
  have : N.FlatOver f := hN.flatOver f
  have hset : {t : T | Nonempty ((restrictToFiber f t).obj L ≅ (f.fiber t).structureModules)} =
      {t : T | 1 ≤ finrankFiberSections f L t} ∩ {t : T | 1 ≤ finrankFiberSections f N t} := by
    ext t
    have := hgeom t
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact nonempty_restrictToFiber_iso_structureModules_iff f e t
  rw [hset]
  exact (isClosed_setOf_le_finrankFiberSections f L 1).inter
    (isClosed_setOf_le_finrankFiberSections f N 1)

end General

section Projection

variable {T : Scheme.{u}} {K : Type u} [Field K] {X : Scheme.{u}}
  (πX : X ⟶ Spec (.of K)) (πT : T ⟶ Spec (.of K))

variable [IsProper πX] [GeometricallyIntegral πX] [LocallyOfFiniteType πT] [QuasiCompact πT]
  {L N : (Limits.pullback πX πT).Modules}

/-- **The triviality locus of a line bundle on `X × T` is closed.** For `X` a proper
geometrically integral variety over a field `K`, `T` a `K`-scheme of finite type and `L` a line
bundle on `X × T`, the set of points `t` of `T` at which the restriction `L_t` of `L` to the
fibre `X_t` is a trivial line bundle is closed in `T`.

The tensor inverse of `L` is carried as an explicit isomorphism `e : L ⊗ N ≅ 𝒪_{X × T}`.

This is `cor:cube-triviality-closed` of the blueprint. -/
theorem isClosed_setOf_nonempty_restrictToFiber_pullbackSnd_iso
    (e : L ⊗ N ≅ 𝟙_ (Limits.pullback πX πT).Modules) :
    IsClosed {t : T | Nonempty ((restrictToFiber (Limits.pullback.snd πX πT) t).obj L ≅
      ((Limits.pullback.snd πX πT).fiber t).structureModules)} := by
  have : IsNoetherian T := isNoetherian_of_locallyOfFiniteType πT
  exact isClosed_setOf_nonempty_restrictToFiber_iso _ e fun _ ↦ inferInstance

end Projection

end AlgebraicGeometry.Scheme.Modules
