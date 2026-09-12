/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Cohomology.Semicontinuity
public import WeilConjectures.AlgebraicGeometry.Modules.Picard

/-!
# The base change map for the direct image, and Grauert's theorem in degree zero

Let `f : W ⟶ T` be a morphism of schemes, let `F` be a sheaf of `𝒪_W`-modules and let `t : T`.
The scheme-theoretic fibre `W_t` sits in a commutative square

```
  W_t ⟶ W
   |     |
   v     v
Spec κ(t) ⟶ T
```

and the mate of the induced comparison of pullbacks is a natural map `u^* f_* F ⟶ g_* F_t` of
sheaves of modules on `Spec κ(t)`. Taking global sections turns it into the **base change map**
`(f_* F)(t) ⟶ Γ(W_t, F_t)` from the fibre of the direct image at `t` to the global sections of
the restriction of `F` to the fibre. Grauert's theorem says that for `T` reduced and Noetherian,
`f` proper and `F` coherent and flat over `T` with constant fibrewise dimension, the direct image
is a line bundle and the base change map is an isomorphism at every point; that is stated here,
and is `sorry` by design.

The one thing that is proved is the compatibility that the chapter consumes: the restriction to
the fibre of the counit `ε : f^* f_* F ⟶ F` is, under the canonical comparison with
`(f_* F)(t) ⊗_{κ(t)} 𝒪_{W_t}`, the base change map followed by the evaluation map.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.fiberBaseChange`: the base change natural transformation
  `u^* ∘ f_* ⟶ g_* ∘ v^*` attached to the fibre square above, as the mate of the canonical
  comparison `g^* u^* ≅ v^* f^*` of pullbacks.
- `AlgebraicGeometry.Scheme.Modules.fiberBaseChangeMap` (blueprint `prop:cube-grauert`): **the
  base change map** `(f_* F)(t) ⟶ Γ(W_t, F_t)`, a `κ(t)`-linear map natural in `F`.
- `AlgebraicGeometry.Scheme.Modules.fiberFreeFunctor`: the functor `V ↦ V ⊗_{κ(t)} 𝒪_{W_t}` from
  `κ(t)`-vector spaces to sheaves of modules on the fibre, left adjoint to
  `AlgebraicGeometry.Scheme.Modules.fiberSectionsFunctor`; the counit of that adjunction is the
  evaluation map `Γ(W_t, F_t) ⊗_{κ(t)} 𝒪_{W_t} ⟶ F_t`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.invertible_pushforward_of_h0_eq_one` and
  `AlgebraicGeometry.Scheme.Modules.isIso_fiberBaseChangeMap_of_h0_eq_one` (blueprint
  `prop:cube-grauert`): **Grauert's theorem** in rank one. For `T` reduced Noetherian, `f` proper
  and `F` coherent and flat over `T` with `h⁰ ≡ 1`, the direct image `f_* F` is an invertible
  sheaf and the base change map is an isomorphism at every point of `T`. Both are `sorry` by
  design; see the implementation notes.
- `AlgebraicGeometry.Scheme.Modules.fiberFreeComparison_comp_map_counit` (blueprint
  `lem:cube-counit-fibre`): **the counit on a fibre is the evaluation map.** This is proved.

## Implementation notes

* The two Grauert statements are `sorry` **by design**: the blueprint marks
  `prop:cube-grauert` as an open obligation. It follows from [Stacks, 0B91] — for `f` proper of
  finite presentation and `F` of finite presentation and flat over the base, `Rf_* F` is a
  perfect complex whose formation commutes with arbitrary base change — together with the fact
  that a perfect complex on a reduced Noetherian scheme with constant degree-zero Betti number
  has locally free degree-zero cohomology. Both ingredients need the cohomology of a sheaf of
  modules in all degrees, which the project does not have. They are stated as `theorem`s and not
  as `instance`s on purpose, so that every place depending on them is visible in the source.
* Grauert's theorem is stated **for rank one only**. This is a deliberate deviation from the
  blueprint, which states it for a constant value `r` of `h⁰` and concludes that `f_* F` is
  locally free of rank `r`. Sheaves of modules in this project carry no rank: `IsLocallyFree`
  records only that the sheaf is locally free, with no rank attached, and there is no
  `𝒪`-module rank function to compare with `r`. The chapter on the theorem of the cube consumes
  only the case `r = 1`, where "locally free of rank one" is exactly `SheafOfModules.Invertible`,
  which is available. When a rank for sheaves of modules exists, the statement should be
  generalised.
* The base change transformation is defined as the **mate** (`CategoryTheory.mateEquiv`) of the
  canonical comparison of pullbacks along the two sides of the fibre square. This is the reason
  `fiberFreeComparison_comp_map_counit` is short: `CategoryTheory.mateEquiv_counit` is exactly
  the statement that the mate, pulled back and composed with the counit downstairs, is the
  comparison composed with the counit upstairs.
* `fiberFreeComparison` is a morphism and not an isomorphism. It is an isomorphism as soon as
  `u^* f_* F` is quasi-coherent — for instance under the hypotheses of Grauert, where `f_* F` is
  invertible — because the comparison `(Γ N)^~ ⟶ N` on `Spec κ(t)` is an isomorphism exactly for
  quasi-coherent `N`, and the other constituent is already an isomorphism. The identity of
  `lem:cube-counit-fibre` holds without any hypothesis, so no hypothesis is imposed.

## References

* [Stacks, 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Hartshorne, *Algebraic geometry*][hartshorne1977], III, Theorem 12.11
* [Mumford, *Abelian varieties*][MumfordAbelianVarieties], §5

## Blueprint

`fiberBaseChangeMap` is the base change map of `prop:cube-grauert`,
`invertible_pushforward_of_h0_eq_one` and `isIso_fiberBaseChangeMap_of_h0_eq_one` implement
`prop:cube-grauert`, and `fiberFreeComparison_comp_map_counit` implements
`lem:cube-counit-fibre` of the chapter on the theorem of the cube.
-/

@[expose] public section

universe u

open CategoryTheory SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {W T : Scheme.{u}} (f : W ⟶ T) (F : W.Modules) (t : T)

/-- The canonical comparison of pullbacks along the two sides of the fibre square of `f` over
`t`: pulling back to `Spec κ(t)` and then to the fibre `W_t` is pulling back to `W` and then
restricting to the fibre. It is an isomorphism, but it is packaged as a 2-square so that the
base change transformation can be obtained as its mate. -/
noncomputable def fiberPullbackTwoSquare :
    TwoSquare (Modules.pullback (T.fromSpecResidueField t)) (Modules.pullback f)
      (Modules.pullback (f.fiberToSpecResidueField t)) (Modules.pullback (f.fiberι t)) :=
  TwoSquare.mk _ _ _ _
    ((pullbackComp (f.fiberToSpecResidueField t) (T.fromSpecResidueField t)).hom ≫
      (pullbackCongr (f.fiber_fac t).symm).hom ≫ (pullbackComp (f.fiberι t) f).inv)

instance : IsIso (fiberPullbackTwoSquare f t).natTrans := by
  rw [fiberPullbackTwoSquare]
  infer_instance

/-- **The base change transformation** `u^* ∘ f_* ⟶ g_* ∘ v^*` for the fibre square of
`f : W ⟶ T` over `t : T`: the mate of `fiberPullbackTwoSquare`. -/
noncomputable def fiberBaseChange :
    TwoSquare (pushforward f) (Modules.pullback (f.fiberι t))
      (Modules.pullback (T.fromSpecResidueField t))
      (pushforward (f.fiberToSpecResidueField t)) :=
  mateEquiv (pullbackPushforwardAdjunction f)
    (pullbackPushforwardAdjunction (f.fiberToSpecResidueField t)) (fiberPullbackTwoSquare f t)

/-- **The base change map** `(f_* F)(t) ⟶ Γ(W_t, F_t)`, from the fibre at `t` of the direct
image of `F` along `f : W ⟶ T` to the global sections of the restriction of `F` to the fibre
`W_t`. It is a `κ(t)`-linear map, and it is natural in `F` by
`AlgebraicGeometry.Scheme.Modules.fiberBaseChangeMap_naturality`.

This is the base change map of `prop:cube-grauert`. -/
noncomputable def fiberBaseChangeMap :
    ((pushforward f).obj F).fiber t ⟶ fiberSections f F t :=
  (moduleSpecΓFunctor (R := T.residueField t)).map ((fiberBaseChange f t).natTrans.app F)

variable {F} in
/-- **The base change map is natural in `F`.** -/
@[reassoc]
lemma fiberBaseChangeMap_naturality {G : W.Modules} (φ : F ⟶ G) :
    fiberMap ((pushforward f).map φ) t ≫ fiberBaseChangeMap f G t =
      fiberBaseChangeMap f F t ≫ (fiberSectionsFunctor f t).map ((restrictToFiber f t).map φ) := by
  have h := congrArg (moduleSpecΓFunctor (R := T.residueField t)).map
    ((fiberBaseChange f t).natTrans.naturality φ)
  rw [Functor.map_comp, Functor.map_comp] at h
  exact h

/-- The functor `V ↦ V ⊗_{κ(t)} 𝒪_{W_t}` from `κ(t)`-vector spaces to sheaves of modules on the
fibre `W_t` of `f : W ⟶ T` over `t`: the pullback along `W_t ⟶ Spec κ(t)` of the quasi-coherent
sheaf attached to `V`. -/
noncomputable def fiberFreeFunctor : ModuleCat (T.residueField t) ⥤ (f.fiber t).Modules :=
  tilde.functor (R := T.residueField t) ⋙ Modules.pullback (f.fiberToSpecResidueField t)

/-- `V ↦ V ⊗_{κ(t)} 𝒪_{W_t}` is left adjoint to taking global sections on the fibre. The counit
of this adjunction at a sheaf `G` on `W_t` is the **evaluation map**
`Γ(W_t, G) ⊗_{κ(t)} 𝒪_{W_t} ⟶ G`, which sends `s ⊗ 1` to `s`. -/
noncomputable def fiberFreeAdjunction : fiberFreeFunctor f t ⊣ fiberSectionsFunctor f t :=
  (tilde.adjunction (R := T.residueField t)).comp
    (pullbackPushforwardAdjunction (f.fiberToSpecResidueField t))

/-- `V ↦ V ⊗_{κ(t)} 𝒪_{W_t}` on morphisms. -/
lemma fiberFreeFunctor_map {V V' : ModuleCat (T.residueField t)} (β : V ⟶ V') :
    (fiberFreeFunctor f t).map β =
      (Modules.pullback (f.fiberToSpecResidueField t)).map
        ((tilde.functor (R := T.residueField t)).map β) :=
  rfl

/-- The mate identity for the base change transformation: the base change map, pulled back to
the fibre and followed by the counit of `g^* ⊣ g_*`, is the comparison of pullbacks followed by
the restriction to the fibre of the counit of `f^* ⊣ f_*`. -/
lemma map_fiberBaseChange_comp_counit :
    (Modules.pullback (f.fiberToSpecResidueField t)).map ((fiberBaseChange f t).natTrans.app F) ≫
        (pullbackPushforwardAdjunction (f.fiberToSpecResidueField t)).counit.app
          ((restrictToFiber f t).obj F) =
      (fiberPullbackTwoSquare f t).natTrans.app ((pushforward f).obj F) ≫
        (restrictToFiber f t).map ((pullbackPushforwardAdjunction f).counit.app F) :=
  mateEquiv_counit _ _ _ F

/-- Naturality of the counit of the tilde-Gamma adjunction, at the base change map. -/
lemma map_fiberBaseChangeMap_comp_counit :
    (tilde.functor (R := T.residueField t)).map (fiberBaseChangeMap f F t) ≫
        (tilde.adjunction (R := T.residueField t)).counit.app
          ((pushforward (f.fiberToSpecResidueField t)).obj ((restrictToFiber f t).obj F)) =
      (tilde.adjunction (R := T.residueField t)).counit.app
          ((Modules.pullback (T.fromSpecResidueField t)).obj ((pushforward f).obj F)) ≫
        (fiberBaseChange f t).natTrans.app F :=
  (tilde.adjunction (R := T.residueField t)).counit_naturality _

/-- The evaluation map `Γ(W_t, G) ⊗_{κ(t)} 𝒪_{W_t} ⟶ G`, spelled out as the counit of the
composite of the tilde-Gamma adjunction on `Spec κ(t)` with `g^* ⊣ g_*`. -/
lemma fiberFreeAdjunction_counit_app (G : (f.fiber t).Modules) :
    (fiberFreeAdjunction f t).counit.app G =
      (Modules.pullback (f.fiberToSpecResidueField t)).map
          ((tilde.adjunction (R := T.residueField t)).counit.app
            ((pushforward (f.fiberToSpecResidueField t)).obj G)) ≫
        (pullbackPushforwardAdjunction (f.fiberToSpecResidueField t)).counit.app G :=
  Adjunction.comp_counit_app _ _ _

/-- The canonical comparison `(f_* F)(t) ⊗_{κ(t)} 𝒪_{W_t} ⟶ (f^* f_* F)|_{W_t}`: the sheaf on
`Spec κ(t)` attached to the fibre `(f_* F)(t)` maps to `u^* f_* F`, and pulling that back to the
fibre and using `fiberPullbackTwoSquare` lands in the restriction of `f^* f_* F`.

It is an isomorphism as soon as `u^* f_* F` is quasi-coherent; see the implementation notes. -/
noncomputable def fiberFreeComparison :
    (fiberFreeFunctor f t).obj (((pushforward f).obj F).fiber t) ⟶
      (restrictToFiber f t).obj ((Modules.pullback f).obj ((pushforward f).obj F)) :=
  (Modules.pullback (f.fiberToSpecResidueField t)).map
      ((tilde.adjunction (R := T.residueField t)).counit.app
        ((Modules.pullback (T.fromSpecResidueField t)).obj ((pushforward f).obj F))) ≫
    (fiberPullbackTwoSquare f t).natTrans.app ((pushforward f).obj F)

/-- **The counit on a fibre is the evaluation map.** For `ε : f^* f_* F ⟶ F` the counit of the
adjunction `f^* ⊣ f_*`, the square

```
  (f_* F)(t) ⊗ 𝒪_{W_t} ---- β ⊗ 𝒪 ----> Γ(W_t, F_t) ⊗ 𝒪_{W_t}
          |                                       |
          | comparison                            | ev
          v                                       v
  (f^* f_* F)|_{W_t} ------ ε|_{W_t} ---------->  F_t
```

commutes, where the left vertical map is `fiberFreeComparison`, `β` is the base change map
`fiberBaseChangeMap` and `ev` is the counit of `fiberFreeAdjunction`. This is
`lem:cube-counit-fibre` of the blueprint.

Under the hypotheses of Grauert's theorem the left vertical map and `β` are isomorphisms, so the
square identifies `ε|_{W_t}` with the evaluation map `Γ(W_t, F_t) ⊗_{κ(t)} 𝒪_{W_t} ⟶ F_t`; but
the identity itself holds for any `f` and `F`. -/
theorem fiberFreeComparison_comp_map_counit :
    fiberFreeComparison f F t ≫
        (restrictToFiber f t).map ((pullbackPushforwardAdjunction f).counit.app F) =
      (fiberFreeFunctor f t).map (fiberBaseChangeMap f F t) ≫
        (fiberFreeAdjunction f t).counit.app ((restrictToFiber f t).obj F) := by
  rw [fiberFreeAdjunction_counit_app, fiberFreeFunctor_map, ← Category.assoc,
    ← Functor.map_comp, map_fiberBaseChangeMap_comp_counit, Functor.map_comp, Category.assoc,
    map_fiberBaseChange_comp_counit, fiberFreeComparison, Category.assoc]

/-- **Grauert's theorem, part (1), in rank one.** For a reduced Noetherian scheme `T`, a proper
morphism `f : W ⟶ T` and a coherent sheaf `F` of `𝒪_W`-modules which is flat over `T` and whose
fibrewise dimension `h⁰` is constant equal to one, the direct image `f_* F` is an invertible
sheaf of `𝒪_T`-modules. This is `prop:cube-grauert` (1) of the blueprint, for `r = 1`.

This is `sorry` by design; see the implementation notes of this file. -/
theorem invertible_pushforward_of_h0_eq_one [IsReduced T] [IsNoetherian T] [IsProper f]
    [F.IsCoherent] (hflat : F.IsFlatOver f) (hh0 : ∀ s : T, h0 f F s = 1) :
    ((pushforward f).obj F).Invertible :=
  sorry

/-- **Grauert's theorem, part (2), in rank one.** In the situation of
`AlgebraicGeometry.Scheme.Modules.invertible_pushforward_of_h0_eq_one`, the base change map
`(f_* F)(t) ⟶ Γ(W_t, F_t)` is an isomorphism of `κ(t)`-vector spaces, for every `t : T`. This is
`prop:cube-grauert` (2) of the blueprint, for `r = 1`.

This is `sorry` by design; see the implementation notes of this file. -/
theorem isIso_fiberBaseChangeMap_of_h0_eq_one [IsReduced T] [IsNoetherian T] [IsProper f]
    [F.IsCoherent] (hflat : F.IsFlatOver f) (hh0 : ∀ s : T, h0 f F s = 1) :
    IsIso (fiberBaseChangeMap f F t) :=
  sorry

end AlgebraicGeometry.Scheme.Modules
