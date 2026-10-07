/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

/-!
# Injectivity of the critical base-change map

Once the base-change property `BC(p, Λ, q - 1)` of
`AlgebraicGeometry.Etale.BaseChangeProperty` is known, the degree-`q` base-change map is
automatically injective: embedding the coefficient sheaf in an injective sheaf and comparing
the two long exact sequences, the degree-`(q - 1)` hypothesis makes two of the vertical arrows
isomorphisms and exhibits the source of the degree-`q` map as the image of the connecting map.

The same diagram gives two statements about the cokernel of the base-change map, which are
what verifies the closed–open splitting hypothesis of the minimal-counterexample lemma in
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField`: the cokernel for a
subsheaf `F ⊆ G` is contained in the cokernel for `G`, and if `G` is injective the cokernel
for `F` is contained in `R^q h_* e⁻¹ G`.

Consequently a failure of `BC(p, Λ, q)` is witnessed by a nonzero element of the cokernel in
a geometric stalk.

## Main statements

- `AlgebraicGeometry.Etale.isZero_baseChangeSourceFunctor_obj_of_injective`: the source of
  the degree-`q` base-change map vanishes on injective sheaves for `q ≠ 0`.
- `AlgebraicGeometry.Etale.baseChangeHomologyMap_comp_map_eq_zero_of_injective`: for `q ≠ 0`,
  the base-change map followed by `R^q h_* e⁻¹` of a map into an injective sheaf is zero.
- `AlgebraicGeometry.Etale.exists_connecting_baseChangeHomologyMap`: the base-change maps
  form a morphism between the two long exact sequences attached to a short exact sequence of
  coefficient sheaves.
- `AlgebraicGeometry.Etale.mono_baseChangeHomologyMap`: the degree-`q` base-change map is a
  monomorphism as soon as `BC(p, Λ, q - 1)` holds.
- `AlgebraicGeometry.Etale.mono_cokernelMap`: the cokernel of the base-change map for a
  subsheaf `F ⊆ G` is contained in the cokernel for `G`.
- `AlgebraicGeometry.Etale.mono_cokernelDesc`: for `G` injective, the cokernel of the
  base-change map for `F ⊆ G` is contained in `R^q h_* e⁻¹ G`.
- `AlgebraicGeometry.Etale.UniversalBaseChangeProperty.mono_baseChangeHomologyMap_and_cokernel`:
  the three statements for every base change of `p`, when `BC(p, Λ, q - 1)` holds universally.

## Implementation notes

The proof follows the blueprint: embed `F` in an injective sheaf `I`, compare the long exact
sequences of `0 ⟶ F ⟶ I ⟶ I / F ⟶ 0` through the base-change maps, and use that the source
of the degree-`q` map vanishes on `I` and that the degree-`(q - 1)` maps are isomorphisms. The
long exact sequences are the homology sequences of the images of the distinguished triangle
`F₁[0] ⟶ F₂[0] ⟶ F₃[0] ⟶ F₁[1]` under the triangulated functors `p^* ∘ Rg_*` and
`Rh_* ∘ e^*`; the base-change maps form a morphism between them because the derived
base-change morphism commutes with the shifts (`AlgebraicGeometry.Etale.commShift_baseChange`).

## References

- Stacks Project, Lemma 59.88.2, <https://stacks.math.columbia.edu/tag/0F03>
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}} {p : X ⟶ S}
  {T Y : Scheme.{u}} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

/-- The source of the base-change map vanishes in nonzero degrees on an injective sheaf `I`:
the derived pushforward of `I` placed in degree `0` is `g_* I` placed in degree `0`, so
`p⁻¹ R^q g_* I = 0` for `q ≠ 0`. This is the injective-acyclicity input of the blueprint
lemma `sbc-lem-bc-injectivity`. -/
lemma Etale.isZero_baseChangeSourceFunctor_obj_of_injective (p : X ⟶ S) (g : T ⟶ S) {q : ℤ}
    (hq : q ≠ 0) (I : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective I] :
    IsZero ((Etale.baseChangeSourceFunctor Λ p g q).obj I) := by
  let e := D+((p)^*[ModuleCat.{u + 1} Λ]).mapIso
      (((g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusObjSingleFunctorIso 0 I) ≪≫
    (((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app _
  refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor _ q).mapIso e)
  rcases hq.lt_or_gt with hq | hq
  · exact DerivedCategory.Plus.isZero_homology_of_isGE
      ((DerivedCategory.Plus.singleFunctor _ 0).obj _) 0 q hq
  · exact DerivedCategory.Plus.isZero_homology_of_isLE
      ((DerivedCategory.Plus.singleFunctor _ 0).obj _) 0 q hq

/-- For `q ≠ 0` and a morphism `α : F ⟶ G` to an injective sheaf `G`, the composite
`p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F ⟶ R^q h_* e⁻¹ G` of the base-change map with `R^q h_* e⁻¹ α`
vanishes: by naturality it factors through `p⁻¹ R^q g_* G`, which is zero. -/
lemma Etale.baseChangeHomologyMap_comp_map_eq_zero_of_injective (sq : IsPullback e h g p)
    {q : ℤ} (hq : q ≠ 0) {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (α : F ⟶ G) [Injective G] :
    Etale.baseChangeHomologyMap Λ sq q F ≫ (Etale.baseChangeTargetFunctor Λ e h q).map α =
      0 := by
  rw [Etale.baseChangeHomologyMap_naturality,
    (Etale.isZero_baseChangeSourceFunctor_obj_of_injective Λ p g hq G).eq_of_tgt
      ((Etale.baseChangeSourceFunctor Λ p g q).map α) 0, zero_comp]

/-- The two long exact sequences of the base-change map. For a short exact sequence
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of sheaves of `Λ`-modules on `T_ét` and `n₀ + 1 = n₁`, there are
connecting maps `δS : p⁻¹ R^{n₀} g_* F₃ ⟶ p⁻¹ R^{n₁} g_* F₁` and
`δT : R^{n₀} h_* e⁻¹ F₃ ⟶ R^{n₁} h_* e⁻¹ F₁` making the two sequences

`p⁻¹ R^{n₀} g_* F₂ ⟶ p⁻¹ R^{n₀} g_* F₃ ⟶ p⁻¹ R^{n₁} g_* F₁ ⟶ p⁻¹ R^{n₁} g_* F₂`,
`R^{n₀} h_* e⁻¹ F₂ ⟶ R^{n₀} h_* e⁻¹ F₃ ⟶ R^{n₁} h_* e⁻¹ F₁ ⟶ R^{n₁} h_* e⁻¹ F₂`

exact, and such that the square

```
p⁻¹ R^{n₀} g_* F₃ --δS--> p⁻¹ R^{n₁} g_* F₁
        |                         |
  bc_{n₀} F₃                bc_{n₁} F₁
        v                         v
R^{n₀} h_* e⁻¹ F₃ --δT--> R^{n₁} h_* e⁻¹ F₁
```

of base-change maps commutes.

This is the long exact sequence input of the blueprint lemma `sbc-lem-bc-injectivity`
(the blueprint lemma `lemma-weil-pbc-five-lemma-transfer` of the proper base change
chapter). It comes from the distinguished triangle of the short exact sequence: its images
under the triangulated functors `p^* ∘ Rg_*` and `Rh_* ∘ e^*` are distinguished, and the
derived base-change morphism `AlgebraicGeometry.Etale.baseChange` is a morphism between them
since it commutes with the shifts (`AlgebraicGeometry.Etale.commShift_baseChange`). -/
theorem Etale.exists_connecting_baseChangeHomologyMap (sq : IsPullback e h g p)
    {E : ShortComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hE : E.ShortExact)
    (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁) :
    ∃ (δS : (Etale.baseChangeSourceFunctor Λ p g n₀).obj E.X₃ ⟶
        (Etale.baseChangeSourceFunctor Λ p g n₁).obj E.X₁)
      (δT : (Etale.baseChangeTargetFunctor Λ e h n₀).obj E.X₃ ⟶
        (Etale.baseChangeTargetFunctor Λ e h n₁).obj E.X₁)
      (wS₁ : (Etale.baseChangeSourceFunctor Λ p g n₀).map E.g ≫ δS = 0)
      (wS₂ : δS ≫ (Etale.baseChangeSourceFunctor Λ p g n₁).map E.f = 0)
      (wT₁ : (Etale.baseChangeTargetFunctor Λ e h n₀).map E.g ≫ δT = 0)
      (wT₂ : δT ≫ (Etale.baseChangeTargetFunctor Λ e h n₁).map E.f = 0),
      (ShortComplex.mk _ _ wS₁).Exact ∧ (ShortComplex.mk _ _ wS₂).Exact ∧
      (ShortComplex.mk _ _ wT₁).Exact ∧ (ShortComplex.mk _ _ wT₂).Exact ∧
      δS ≫ Etale.baseChangeHomologyMap Λ sq n₁ E.X₁ =
        Etale.baseChangeHomologyMap Λ sq n₀ E.X₃ ≫ δT :=
  -- The concrete functors are only passed as data with `rfl` equations: unifying them with
  -- the abstract composites directly makes the kernel unfold the derived functors.
  Functor.exists_homologySequenceδ_whiskerRight
    (DerivedCategory.Plus.homologyFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0)
    (DerivedCategory.Plus.singleFunctor _ 0)
    (Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq)
    (DerivedCategory.Plus.homologyFunctor _) (fun _ ↦ rfl) (Etale.baseChangeSourceFunctor Λ p g)
    (Etale.baseChangeTargetFunctor Λ e h) (Etale.baseChangeHomologyNatTrans Λ sq) rfl E _
    hE.singleTrianglePlus_distinguished n₀ n₁ hn

/-- Blueprint `sk-prop-injectivity` (1): Injectivity of the critical map.

Let `q ≥ 1` and assume `BC(p, Λ, q - 1)`. Then for every Cartesian square

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

with `g` quasi-compact quasi-separated and every sheaf `F` of `Λ`-modules on `T_ét`, the
degree-`q` base-change map `p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is injective. -/
@[stacks 0F03]
theorem Etale.mono_baseChangeHomologyMap (q : ℤ) (hq : 1 ≤ q)
    (hprev : Etale.BaseChangeProperty Λ p (q - 1)) [QuasiCompact g] [QuasiSeparated g]
    (sq : IsPullback e h g p) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Mono (Etale.baseChangeHomologyMap Λ sq q F) := by
  have hS : (ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
      (cokernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_cokernel _ }
  obtain ⟨δS, δT, wS₁, wS₂, wT₁, -, hS₁, hS₂, hT₁, -, hδ⟩ :=
    Etale.exists_connecting_baseChangeHomologyMap Λ sq hS (q - 1) q (by lia)
  have := hprev g e h sq (Injective.under F)
  have := hprev g e h sq (cokernel (Injective.ι F))
  have hI := Etale.isZero_baseChangeSourceFunctor_obj_of_injective Λ p g (q := q) (by lia)
    (Injective.under F)
  have : Epi δS := hS₂.epi_f (hI.eq_of_tgt _ _)
  exact Abelian.mono_of_epi_of_epi_of_mono
    (ComposableArrows.homMk₂ (Etale.baseChangeHomologyMap Λ sq (q - 1) (Injective.under F))
      (Etale.baseChangeHomologyMap Λ sq (q - 1) (cokernel (Injective.ι F)))
      (Etale.baseChangeHomologyMap Λ sq q F)
      (Etale.baseChangeHomologyMap_naturality Λ sq (q - 1) _).symm hδ :
      ComposableArrows.mk₂ _ δS ⟶ ComposableArrows.mk₂ _ δT)
    hS₁.exact_toComposableArrows hT₁.exact_toComposableArrows
    (inferInstanceAs (Epi δS)) (inferInstanceAs (Epi (Etale.baseChangeHomologyMap Λ sq _ _)))
    (inferInstanceAs (Mono (Etale.baseChangeHomologyMap Λ sq _ _)))

/-- Blueprint `sk-prop-injectivity` (3): the cokernel of the critical map sits inside the
higher direct image of an injective sheaf.

In the situation of `AlgebraicGeometry.Etale.mono_baseChangeHomologyMap`, if `F` is a
subsheaf of an injective sheaf `G`, then the map `R^q h_* e⁻¹ F ⟶ R^q h_* e⁻¹ G` kills the
image of the base-change map for `F` — the source of the base-change map for `G` vanishes,
`G` being injective and `q` positive — and the induced map from the cokernel is injective.
The vanishing that makes the map out of the cokernel exist is
`AlgebraicGeometry.Etale.baseChangeHomologyMap_comp_map_eq_zero_of_injective`. -/
@[stacks 0F03]
theorem Etale.mono_cokernelDesc (q : ℤ) (hq : 1 ≤ q)
    (hprev : Etale.BaseChangeProperty Λ p (q - 1)) [QuasiCompact g] [QuasiSeparated g]
    (sq : IsPullback e h g p) {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (α : F ⟶ G) [Mono α] [Injective G] :
    Mono (cokernel.desc (Etale.baseChangeHomologyMap Λ sq q F)
      ((Etale.baseChangeTargetFunctor Λ e h q).map α)
      (Etale.baseChangeHomologyMap_comp_map_eq_zero_of_injective Λ sq (by lia) α)) := by
  have hα := Etale.baseChangeHomologyMap_comp_map_eq_zero_of_injective Λ sq (q := q) (by lia) α
  have hS : (ShortComplex.mk α (cokernel.π α) (cokernel.condition α)).ShortExact :=
    { exact := ShortComplex.exact_cokernel α }
  obtain ⟨δS, δT, -, wS₂, -, wT₂, -, hS₂, -, hT₂, hδ⟩ :=
    Etale.exists_connecting_baseChangeHomologyMap Λ sq hS (q - 1) q (by lia)
  have := hprev g e h sq (cokernel α)
  have hG := Etale.isZero_baseChangeSourceFunctor_obj_of_injective Λ p g (q := q) (by lia) G
  have : Epi δS := hS₂.epi_f (hG.eq_of_tgt _ _)
  let φ : ShortComplex.mk (Etale.baseChangeHomologyMap Λ sq (q - 1) (cokernel α) ≫ δT)
      ((Etale.baseChangeTargetFunctor Λ e h q).map α)
      (by simp [wT₂]) ⟶
      ShortComplex.mk (Etale.baseChangeHomologyMap Λ sq q F)
        ((Etale.baseChangeTargetFunctor Λ e h q).map α) hα :=
    { τ₁ := δS
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [hδ] }
  refine ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 ?_).mono_cokernelDesc
  let ψ : ShortComplex.mk (Etale.baseChangeHomologyMap Λ sq (q - 1) (cokernel α) ≫ δT)
      ((Etale.baseChangeTargetFunctor Λ e h q).map α)
      (by simp [wT₂]) ⟶ ShortComplex.mk _ _ wT₂ :=
    { τ₁ := Etale.baseChangeHomologyMap Λ sq (q - 1) (cokernel α)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).2 hT₂

/-- Blueprint `sk-prop-injectivity` (2): the cokernel of the critical map grows with the
coefficient sheaf.

In the situation of `AlgebraicGeometry.Etale.mono_baseChangeHomologyMap`, if `F` is a
subsheaf of `G`, then the map induced on the cokernels of the two base-change maps by the
naturality `AlgebraicGeometry.Etale.baseChangeHomologyMap_naturality` is injective. -/
@[stacks 0F03]
theorem Etale.mono_cokernelMap (q : ℤ) (hq : 1 ≤ q)
    (hprev : Etale.BaseChangeProperty Λ p (q - 1)) [QuasiCompact g] [QuasiSeparated g]
    (sq : IsPullback e h g p) {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (α : F ⟶ G) [Mono α] :
    Mono (cokernel.map (Etale.baseChangeHomologyMap Λ sq q F)
      (Etale.baseChangeHomologyMap Λ sq q G) ((Etale.baseChangeSourceFunctor Λ p g q).map α)
      ((Etale.baseChangeTargetFunctor Λ e h q).map α)
      (Etale.baseChangeHomologyMap_naturality Λ sq q α)) := by
  have hzero {K : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
      (β : K ⟶ Injective.under G) :=
    Etale.baseChangeHomologyMap_comp_map_eq_zero_of_injective Λ sq (q := q) (by lia) β
  have hfac : cokernel.map (Etale.baseChangeHomologyMap Λ sq q F)
      (Etale.baseChangeHomologyMap Λ sq q G) ((Etale.baseChangeSourceFunctor Λ p g q).map α)
      ((Etale.baseChangeTargetFunctor Λ e h q).map α)
      (Etale.baseChangeHomologyMap_naturality Λ sq q α) ≫
      cokernel.desc _ _ (hzero (Injective.ι G)) =
        cokernel.desc _ _ (hzero (α ≫ Injective.ι G)) := by
    refine coequalizer.hom_ext ?_
    simp
  have := Etale.mono_cokernelDesc Λ q hq hprev sq (α ≫ Injective.ι G)
  rw [← hfac] at this
  exact mono_of_mono _ (cokernel.desc _ _ (hzero (Injective.ι G)))

/-- Blueprint `sbc-lem-bc-injectivity`: Injectivity of the critical map and its cokernel.

Assume that `BC(p, Λ, q - 1)` holds universally for some `q ≥ 1`, and let `p' : X' ⟶ S'` be
the base change of `p` along `a : S' ⟶ S`. Then for every Cartesian square

```
Y --e--> T
|        |
h        g
v        v
X' -p'-> S'
```

with `g` quasi-compact quasi-separated:

1. the base-change map `p'⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is injective for every `F`;
2. for a subsheaf `F ⊆ G`, the cokernel of the base-change map for `F` injects into the one
   for `G`;
3. if moreover `G` is injective, the cokernel of the base-change map for `F` injects into
   `R^q h_* e⁻¹ G`.

Only `BC(p', Λ, q - 1)`, which is part of the universal hypothesis, enters, through
`AlgebraicGeometry.Etale.mono_baseChangeHomologyMap`,
`AlgebraicGeometry.Etale.mono_cokernelMap` and `AlgebraicGeometry.Etale.mono_cokernelDesc`. -/
@[stacks 0F03]
theorem Etale.UniversalBaseChangeProperty.mono_baseChangeHomologyMap_and_cokernel {q : ℤ}
    (hq : 1 ≤ q) (huniv : Etale.UniversalBaseChangeProperty Λ p (q - 1)) {S' X' : Scheme.{u}}
    {a : S' ⟶ S} {b : X' ⟶ X} {p' : X' ⟶ S'} (hp : IsPullback b p' p a) {g : T ⟶ S'}
    {h : Y ⟶ X'} [QuasiCompact g] [QuasiSeparated g] (sq : IsPullback e h g p') :
    (∀ F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      Mono (Etale.baseChangeHomologyMap Λ sq q F)) ∧
    (∀ {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (α : F ⟶ G) [Mono α],
      Mono (cokernel.map (Etale.baseChangeHomologyMap Λ sq q F)
        (Etale.baseChangeHomologyMap Λ sq q G) ((Etale.baseChangeSourceFunctor Λ p' g q).map α)
        ((Etale.baseChangeTargetFunctor Λ e h q).map α)
        (Etale.baseChangeHomologyMap_naturality Λ sq q α))) ∧
    (∀ {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (α : F ⟶ G) [Mono α]
      [Injective G],
      Mono (cokernel.desc (Etale.baseChangeHomologyMap Λ sq q F)
        ((Etale.baseChangeTargetFunctor Λ e h q).map α)
        (Etale.baseChangeHomologyMap_comp_map_eq_zero_of_injective Λ sq (by lia) α))) :=
  have hprev : Etale.BaseChangeProperty Λ p' (q - 1) := huniv a b p' hp
  ⟨Etale.mono_baseChangeHomologyMap Λ q hq hprev sq,
    fun α _ ↦ Etale.mono_cokernelMap Λ q hq hprev sq α,
    fun α _ _ ↦ Etale.mono_cokernelDesc Λ q hq hprev sq α⟩

end AlgebraicGeometry
