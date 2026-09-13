/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Semicontinuity
public import WeilConjectures.AlgebraicGeometry.Modules.Picard
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Grauert's theorem in degree zero, and the counit on a fibre

Let `f : W ⟶ T` be a morphism of schemes, let `F` be a sheaf of `𝒪_W`-modules and let `t : T`.
The scheme-theoretic fibre `W_t` sits in a commutative square

```
            v
     W_t ───────→ W
      │           │
    g │           │ f
      ↓           ↓
 Spec κ(t) ─────→ T
            u
```

and the base change map `(f_* F)(t) ⟶ Γ(W_t, F_t)`, from the fibre of the direct image at `t` to
the global sections of the restriction of `F` to the fibre, is
`AlgebraicGeometry.Scheme.Modules.fiberBaseChangeMap` of
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`. Grauert's theorem says that for `T`
reduced and Noetherian, `f` proper and `F` coherent and flat over `T` with constant fibrewise
dimension `r`, the direct image `f_* F` is locally free and the base change map is an
isomorphism at every point; that is stated here, and is `sorry` by design.

The one thing that is proved is the compatibility that the chapter consumes: the restriction to
the fibre of the counit `ε : f^* f_* F ⟶ F` is, under the canonical comparison with
`(f_* F)(t) ⊗_{κ(t)} 𝒪_{W_t}`, the base change map followed by the evaluation map.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.isLocallyFree_pushforward_of_finrankFiberSections_eq` and
  `AlgebraicGeometry.Scheme.Modules.isIso_fiberBaseChangeMap_of_finrankFiberSections_eq`
  (blueprint `prop:cube-grauert`): **Grauert's theorem**. For `T` reduced Noetherian, `f` proper
  and `F` coherent and flat over `T` with `h⁰ ≡ r`, the direct image `f_* F` is locally free and
  the base change map is an isomorphism at every point of `T`. Both are `sorry` by design; see
  the implementation notes.
- `AlgebraicGeometry.Scheme.Modules.invertible_pushforward_of_finrankFiberSections_eq_one`
  (blueprint `prop:cube-grauert` (1) for `r = 1`): in the same situation with `h⁰ ≡ 1`, the
  direct image `f_* F` is an invertible sheaf. This is the form the chapter consumes, and it too
  is `sorry` by design.
- `AlgebraicGeometry.Scheme.Modules.finrank_fiber_pushforward_of_finrankFiberSections_eq`: the
  rank assertion of `prop:cube-grauert` (1), namely that the fibres of `f_* F` are
  `r`-dimensional. This is **proved** from the base change statement.
- `AlgebraicGeometry.Scheme.Modules.fiberFreeComparison_comp_map_counit` (blueprint
  `lem:cube-counit-fibre`): **the counit on a fibre is the evaluation map.** This is proved.

## Implementation notes

* The Grauert statements are `sorry` **by design**: the blueprint marks `prop:cube-grauert` as
  an open obligation. It follows from [Stacks, 0B91] — for `f` proper of finite presentation and
  `F` of finite presentation and flat over the base, `Rf_* F` is a perfect complex whose
  formation commutes with arbitrary base change — together with the fact that a perfect complex
  on a reduced Noetherian scheme with constant degree-zero Betti number has locally free
  degree-zero cohomology. What is missing for those ingredients is not the cohomology of a sheaf
  of modules, which the project has in every degree as
  `AlgebraicGeometry.Scheme.Modules.H` of `WeilConjectures.AlgebraicGeometry.Cohomology.Basic`,
  but the higher direct images `R^i f_*`, perfect complexes on the base, and their base change.
  The statements are `theorem`s and not `instance`s on purpose, so that every place depending on
  them is visible in the source.
* Part (1) of the blueprint statement asserts that `f_* F` is locally free **of rank `r`**. It is
  formalised here in two pieces: `isLocallyFree_pushforward_of_finrankFiberSections_eq` gives
  local freeness, and `finrank_fiber_pushforward_of_finrankFiberSections_eq` gives the rank, in
  the form that every fibre of `f_* F` is `r`-dimensional — sheaves of modules in this project
  carry no rank function, so "of rank `r`" cannot be said directly. The two together are the
  content of the blueprint statement.
* `invertible_pushforward_of_finrankFiberSections_eq_one` is the case `r = 1`, stated separately
  because it is what the chapter consumes and because the bridge from "locally free with
  one-dimensional fibres" to `SheafOfModules.Invertible` is not available: see the TODO in
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`. Once that bridge exists this
  statement should be deduced from the two above rather than assumed.
* The base change transformation is defined as the **mate**
  (`CategoryTheory.mateEquiv`) of the canonical comparison of pullbacks along the two sides of
  the fibre square; see `AlgebraicGeometry.Scheme.Modules.baseChange`. This is the reason
  `fiberFreeComparison_comp_map_counit` is short: `CategoryTheory.mateEquiv_counit` is exactly
  the statement that the mate, pulled back and composed with the counit downstairs, is the
  comparison composed with the counit upstairs.
* The identity of `lem:cube-counit-fibre` holds for any `f` and `F`, so no hypothesis is imposed
  on the statement. Under the hypotheses of Grauert the two vertical maps of its square become
  isomorphisms: the base change map by
  `isIso_fiberBaseChangeMap_of_finrankFiberSections_eq`, and the comparison by
  `AlgebraicGeometry.Scheme.Modules.isIso_fiberFreeComparison`, since `f_* F` is then locally
  free and in particular quasi-coherent.

## References

* [Stacks, 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Hartshorne, *Algebraic geometry*][hartshorne1977], III, Theorem 12.11
* [Mumford, *Abelian varieties*][MumfordAbelianVarieties], §5

## Blueprint

`isLocallyFree_pushforward_of_finrankFiberSections_eq`,
`finrank_fiber_pushforward_of_finrankFiberSections_eq`,
`invertible_pushforward_of_finrankFiberSections_eq_one` and
`isIso_fiberBaseChangeMap_of_finrankFiberSections_eq` implement `prop:cube-grauert`, and
`fiberFreeComparison_comp_map_counit` implements `lem:cube-counit-fibre` of the chapter on the
theorem of the cube.
-/

@[expose] public section

universe u

open CategoryTheory SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {W T : Scheme.{u}} (f : W ⟶ T) (F : W.Modules) (t : T)

/-- **The counit on a fibre is the evaluation map.** For `ε : f^* f_* F ⟶ F` the counit of the
adjunction `f^* ⊣ f_*`, the square

```
   (f_* F)(t) ⊗ 𝒪_{W_t} ──── β ⊗ 𝒪 ────→ Γ(W_t, F_t) ⊗ 𝒪_{W_t}
            │                                       │
 comparison │                                       │ ev
            ↓                                       ↓
   (f^* f_* F)|_{W_t} ────── ε|_{W_t} ───────────→ F_t
```

commutes, where the left vertical map is
`AlgebraicGeometry.Scheme.Modules.fiberFreeComparison`, `β` is the base change map
`AlgebraicGeometry.Scheme.Modules.fiberBaseChangeMap` and `ev` is the counit of
`AlgebraicGeometry.Scheme.Modules.fiberFreeAdjunction`. This is `lem:cube-counit-fibre` of the
blueprint.

Under the hypotheses of Grauert's theorem the left vertical map and `β` are isomorphisms, so the
square identifies `ε|_{W_t}` with the evaluation map `Γ(W_t, F_t) ⊗_{κ(t)} 𝒪_{W_t} ⟶ F_t`; but
the identity itself holds for any `f` and `F`. -/
@[reassoc]
theorem fiberFreeComparison_comp_map_counit :
    fiberFreeComparison f t ((pushforward f).obj F) ≫
        (restrictToFiber f t).map ((pullbackPushforwardAdjunction f).counit.app F) =
      (fiberFreeFunctor f t).map (fiberBaseChangeMap f F t) ≫
        (fiberFreeAdjunction f t).counit.app ((restrictToFiber f t).obj F) := by
  rw [fiberFreeAdjunction_counit_app, fiberBaseChangeMap_eq, fiberFreeFunctor_map]
  have hnat := (tilde.adjunction (R := T.residueField t)).counit_naturality
    ((fiberBaseChange f t).natTrans.app F)
  simp only [Functor.comp_obj] at hnat
  rw [← Category.assoc, ← Functor.map_comp, hnat, Functor.map_comp, Category.assoc,
    map_baseChange_comp_counit, fiberFreeComparison]
  exact Category.assoc _ _ _

/-- **Grauert's theorem, part (1).** For a reduced Noetherian scheme `T`, a proper morphism
`f : W ⟶ T` and a coherent sheaf `F` of `𝒪_W`-modules which is flat over `T` and whose fibrewise
dimension `h⁰` is constant equal to `r`, the direct image `f_* F` is a locally free sheaf of
`𝒪_T`-modules. This is the local freeness half of `prop:cube-grauert` (1) of the blueprint; the
rank half is `finrank_fiber_pushforward_of_finrankFiberSections_eq`.

This is `sorry` by design; see the implementation notes of this file. -/
theorem isLocallyFree_pushforward_of_finrankFiberSections_eq [IsReduced T] [IsNoetherian T]
    [IsProper f] [F.IsCoherent] [F.FlatOver f] {r : ℕ}
    (hr : ∀ s : T, finrankFiberSections f F s = r) :
    ((pushforward f).obj F).IsLocallyFree :=
  sorry

/-- **Grauert's theorem, part (2).** In the situation of
`AlgebraicGeometry.Scheme.Modules.isLocallyFree_pushforward_of_finrankFiberSections_eq`, the base
change map `(f_* F)(t) ⟶ Γ(W_t, F_t)` is an isomorphism of `κ(t)`-vector spaces, for every
`t : T`. This is `prop:cube-grauert` (2) of the blueprint.

This is `sorry` by design; see the implementation notes of this file. -/
theorem isIso_fiberBaseChangeMap_of_finrankFiberSections_eq [IsReduced T] [IsNoetherian T]
    [IsProper f] [F.IsCoherent] [F.FlatOver f] {r : ℕ}
    (hr : ∀ s : T, finrankFiberSections f F s = r) :
    IsIso (fiberBaseChangeMap f F t) :=
  sorry

/-- **The rank assertion of Grauert's theorem, part (1)**: in the situation of
`AlgebraicGeometry.Scheme.Modules.isLocallyFree_pushforward_of_finrankFiberSections_eq`, every
fibre of `f_* F` is an `r`-dimensional vector space. Together with local freeness this is the
statement "`f_* F` is locally free of rank `r`" of `prop:cube-grauert` (1).

Unlike the two statements it depends on, this one is proved: the base change map identifies the
fibre `(f_* F)(t)` with `Γ(W_t, F_t)`, whose dimension is `r` by hypothesis. -/
theorem finrank_fiber_pushforward_of_finrankFiberSections_eq [IsReduced T] [IsNoetherian T]
    [IsProper f] [F.IsCoherent] [F.FlatOver f] {r : ℕ}
    (hr : ∀ s : T, finrankFiberSections f F s = r) :
    Module.finrank (T.residueField t) (((pushforward f).obj F).fiber t) = r := by
  have := isIso_fiberBaseChangeMap_of_finrankFiberSections_eq f F t hr
  rw [(asIso (fiberBaseChangeMap f F t)).toLinearEquiv.finrank_eq]
  exact hr t

/-- **Grauert's theorem in rank one.** For a reduced Noetherian scheme `T`, a proper morphism
`f : W ⟶ T` and a coherent sheaf `F` of `𝒪_W`-modules which is flat over `T` and whose fibrewise
dimension `h⁰` is constant equal to one, the direct image `f_* F` is an invertible sheaf of
`𝒪_T`-modules. This is `prop:cube-grauert` (1) of the blueprint for `r = 1`, in the form the
chapter on the theorem of the cube consumes.

This is `sorry` by design; see the implementation notes of this file. -/
theorem invertible_pushforward_of_finrankFiberSections_eq_one [IsReduced T] [IsNoetherian T]
    [IsProper f] [F.IsCoherent] [F.FlatOver f] (h1 : ∀ s : T, finrankFiberSections f F s = 1) :
    ((pushforward f).obj F).Invertible :=
  sorry

end AlgebraicGeometry.Scheme.Modules
