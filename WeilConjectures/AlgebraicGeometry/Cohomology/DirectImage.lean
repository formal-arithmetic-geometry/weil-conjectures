/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Semicontinuity.Defs
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Higher direct images, and cohomology and base change

Let `f : X ⟶ T` be a proper morphism of finite presentation and let `ℱ` be an `𝒪_X`-module of
finite presentation which is flat over `T`. This file states the fundamental finiteness and
base-change results about the higher direct images `R^q f_* ℱ`.

The higher direct images are the right derived functors of the pushforward functor
`AlgebraicGeometry.Scheme.Modules.pushforward f` between the abelian categories `X.Modules`
and `T.Modules`. This is a different construction from the sheaf cohomology `ℱ.H q` of
`WeilConjectures/AlgebraicGeometry/Cohomology/Defs.lean`, which is an `Ext`-group in abelian
sheaves; `nonempty_sections_higherDirectImage_iso_H` below is the comparison between the two,
and it is what lets the statements of this file be combined with the ones phrased through
`ℱ.H q`.

## Implementation notes

Every derived-functor statement below needs injective resolutions in `X.Modules`, carried as
an instance hypothesis `[HasInjectiveResolutions X.Modules]`. Nothing in Mathlib can discharge
it: there is no `IsGrothendieckAbelian` instance for `SheafOfModules` anywhere. The missing
prerequisite is recorded as the explicit statement
`AlgebraicGeometry.Scheme.Modules.isGrothendieckAbelian`; once it is proved and made an
instance, `EnoughInjectives` and hence `HasInjectiveResolutions` follow, and the hypothesis can
be dropped from every statement here and downstream.

Mathlib has no `IsCoherent` class for sheaves of modules. Over a locally Noetherian base
coherence is equivalent to being quasi-coherent and of finite presentation, so that is what the
statements below use; they should be restated with coherence once it exists.

There is no derived category of `X.Modules` with a derived pushforward available, so "`R f_* ℱ`
is perfect" is stated through an explicit bounded complex of finite free modules whose
cohomology computes the higher direct images after every base change. Base change of `f` and `ℱ`
along `g : T' ⟶ T` is spelled out through an explicit pullback square
`IsPullback g' f' f g` and the pullback `(Modules.pullback g').obj ℱ`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.higherDirectImage`: the `q`-th higher direct image
  functor `R^q f_*`, the `q`-th right derived functor of the pushforward.
- `AlgebraicGeometry.Scheme.Modules.IsFlatOver`: flatness of a sheaf of modules over the base
  of a morphism, checked on affine opens.
- `AlgebraicGeometry.Scheme.Modules.hFiber`: the fibre dimension
  `dim_{κ(t)} H^q(X_t, ℱ_t)`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.nonempty_sections_higherDirectImage_iso_H`: over an affine
  base, the global sections of `R^q f_* ℱ` are `H^q(X, ℱ)`.
- `AlgebraicGeometry.Scheme.Modules.exists_finiteFreeComplex_higherDirectImage` and
  `exists_isZero_higherDirectImage_restrict`: over any base, `R f_* ℱ` is locally given by a
  bounded complex of finite free modules compatible with base change, and so vanishes locally in
  large degrees.
- `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage` and
  `exists_isZero_higherDirectImage`: coherence of the higher direct images over a locally
  Noetherian base, and their uniform vanishing in large degrees over a quasi-compact base.
- `AlgebraicGeometry.Scheme.Modules.upperSemicontinuous_hFiber` and
  `exists_isFiniteLocallyFreeOfRank_higherDirectImage_of_isLocallyConstant`: semicontinuity of
  the fibre dimension, and Grauert's theorem over a reduced base.
- `AlgebraicGeometry.Scheme.Modules.isOpen_setOf_hFiber_le`,
  `isZero_higherDirectImage_restrict` and
  `isFiniteLocallyFreeOfRank_higherDirectImage_restrict`: openness of the perfect locus, and
  the shape of `R f_* ℱ` over it.
- `AlgebraicGeometry.Scheme.Modules.isLocallyConstant_hFiber_restrict`,
  `isOpen_setOf_hFiber_eq` and `range_subset_setOf_hFiber_eq_iff`: local constancy of the fibre
  dimension on the perfect locus, openness of the rank-`r` locus, and its functorial
  characterisation through base change.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}}

/-- `X.Modules` is a Grothendieck abelian category.

This is the missing prerequisite of the whole file: together with
`CategoryTheory.IsGrothendieckAbelian.enoughInjectives` it supplies the
`HasInjectiveResolutions X.Modules` instance that every statement below, and every statement
about the Picard functor `F` downstream, currently has to assume. -/
theorem isGrothendieckAbelian (X : Scheme.{u}) : IsGrothendieckAbelian.{u} X.Modules :=
  sorry

/-- The `q`-th **higher direct image** functor `R^q f_*` along a morphism of schemes
`f : X ⟶ T`: the `q`-th right derived functor of the pushforward functor
`AlgebraicGeometry.Scheme.Modules.pushforward f : X.Modules ⥤ T.Modules`.

Both `X.Modules` and `T.Modules` are abelian and the pushforward is additive, so the only
extra input is the existence of injective resolutions in `X.Modules`, which is taken as an
instance hypothesis. -/
noncomputable def higherDirectImage (f : X ⟶ T) [HasInjectiveResolutions X.Modules] (q : ℕ) :
    X.Modules ⥤ T.Modules :=
  (pushforward f).rightDerived q

/-- `ℱ.IsFlatOver f` says that the `𝒪_X`-module `ℱ` is **flat over the base** of the morphism
`f : X ⟶ T`: for every affine open `V` of `T` and every affine open `U` of `X` contained in
`f ⁻¹ᵁ V`, the sections `Γ(ℱ, U)` form a flat `Γ(T, V)`-module, the module structure being
restriction of scalars along `f.appLE V U`.

This is the affine-local form of the stalkwise condition "`ℱ_x` is flat over `𝒪_{T, f x}` for
every `x`", and the two are equivalent. -/
def IsFlatOver (ℱ : X.Modules) (f : X ⟶ T) : Prop :=
  ∀ (V : T.affineOpens) (U : X.affineOpens) (e : U.1 ≤ f ⁻¹ᵁ V.1),
    letI : Module Γ(T, V.1) Γ(ℱ, U.1) := Module.compHom _ (f.appLE V.1 U.1 e).hom
    Module.Flat Γ(T, V.1) Γ(ℱ, U.1)

/-- The `q`-th **fibre dimension** `dim_{κ(t)} H^q(X_t, ℱ_t)` of an `𝒪_X`-module `ℱ` along a
morphism `f : X ⟶ T` at a point `t` of `T`: the fibre `X_t = f.fiber t` is a scheme over the
residue field `κ(t) = T.residueField t`, the restriction `ℱ_t` is the pullback of `ℱ` along
`f.fiberι t`, and the dimension is `AlgebraicGeometry.Scheme.Modules.finrankH` for that base
field. -/
noncomputable def hFiber (ℱ : X.Modules) (f : X ⟶ T) (q : ℕ) (t : T) : ℕ :=
  letI := f.fiberOverSpecResidueField t
  ((Modules.pullback (f.fiberι t)).obj ℱ).finrankH (T.residueField t) q

variable (f : X ⟶ T) (ℱ : X.Modules)

/-- Over an affine base the global sections of the `q`-th higher direct image are the sheaf
cohomology of `ℱ`: `Γ(T, R^q f_* ℱ) ≅ H^q(X, ℱ)`.

This is the comparison between the two cohomology theories used in the Picard-framework block:
the right derived functors of `f_*` inside `X.Modules` on the one hand, and the `Ext`-groups in
abelian sheaves of `AlgebraicGeometry.Scheme.Modules.H` on the other. It holds because
injective objects of `X.Modules` are `Γ`-acyclic. -/
theorem nonempty_sections_higherDirectImage_iso_H [IsAffine T] [QuasiCompact f] [IsSeparated f]
    [HasInjectiveResolutions X.Modules]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    Nonempty (Γ((higherDirectImage f q).obj ℱ, ⊤) ≃+ ℱ.H q) :=
  sorry

section Coherence

variable [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
  [HasInjectiveResolutions X.Modules] [ℱ.IsFinitePresentation]

/-- **Local vanishing of the higher direct images in large degrees.** With `f : X ⟶ T` proper
of finite presentation and `ℱ` an `𝒪_X`-module of finite presentation which is flat over `T`,
every point `t` of `T` has an open neighbourhood `U` and a bound `d` with `R^q f_* ℱ|_U = 0` for
all `q > d`; one can take for `d` a bound on the dimensions of the fibres of `f` over `U`.

The bound is only local on `T`: over `T = ⨆ₙ Spec k` with `X = ⨆ₙ ℙⁿ_k` and `ℱ = 𝒪(-n-1)` on
the `n`-th piece, `R^n f_* ℱ ≠ 0` for every `n`.

(blueprint: `sk-thm-picard-coherence`) -/
theorem exists_isZero_higherDirectImage_restrict (hℱ : ℱ.IsFlatOver f) (t : T) :
    ∃ (U : T.Opens) (d : ℕ), t ∈ U ∧
      ∀ q > d, IsZero (((higherDirectImage f q).obj ℱ).restrict U.ι) :=
  sorry

/-- **Perfectness of the higher direct images, with base change.** With `f : X ⟶ T` proper of
finite presentation and `ℱ` an `𝒪_X`-module of finite presentation which is flat over `T`, every
point `t` of `T` has an open neighbourhood `U` over which `R f_* ℱ` is represented by a bounded
complex `P` of finite free `𝒪_U`-modules whose formation commutes with every base change: the
cohomology of `P` is `R^q f_* ℱ|_U`, and for every `g : T' ⟶ U` the cohomology of the pullback
`g^* P` is `R^q f'_* ℱ'`, where `f' : X' ⟶ T'` is the base change of `f` along `g ≫ U.ι` and
`ℱ'` is the pullback of `ℱ` to `X'`.

Over a Noetherian affine base `P` is Mumford's complex, obtained from the Čech complex of a
finite affine cover, which is a bounded complex of flat modules by the flatness of `ℱ`; the
general case reduces to this by Noetherian approximation of `(f, ℱ)`.

(blueprint: `sk-thm-picard-coherence`) -/
theorem exists_finiteFreeComplex_higherDirectImage (hℱ : ℱ.IsFlatOver f) (t : T) :
    ∃ (U : T.Opens) (P : CochainComplex U.toScheme.Modules ℤ) (d : ℕ), t ∈ U ∧
      P.IsStrictlyGE 0 ∧ P.IsStrictlyLE d ∧
      (∀ n, ∃ r : ℕ, Nonempty (P.X n ≅ SheafOfModules.free (ULift.{u} (Fin r)))) ∧
      (∀ q : ℕ, Nonempty (P.homology q ≅ ((higherDirectImage f q).obj ℱ).restrict U.ι)) ∧
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ)) :=
  sorry

/-- **Coherence of the higher direct images over a locally Noetherian base.** With
`f : X ⟶ T` proper of finite presentation, `T` locally Noetherian and `ℱ` an `𝒪_X`-module of
finite presentation which is flat over `T`, the higher direct image `R^q f_* ℱ` is a coherent
`𝒪_T`-module for every `q`; coherence is spelled as quasi-coherence together with finite
presentation.

The Noetherian hypothesis cannot be dropped: over `T = Spec (k ⊕ V)` with `V` an
infinite-dimensional square-zero ideal, a suitable line bundle on `E × T`, for `E` an elliptic
curve, has a direct image which is not of finite type.

(blueprint: `sk-thm-picard-coherence`) -/
theorem isFinitePresentation_higherDirectImage [IsLocallyNoetherian T] (hℱ : ℱ.IsFlatOver f)
    (q : ℕ) :
    ((higherDirectImage f q).obj ℱ).IsQuasicoherent ∧
      ((higherDirectImage f q).obj ℱ).IsFinitePresentation :=
  sorry

/-- **Vanishing of the higher direct images in large degrees over a quasi-compact base.** In the
situation of `AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage_restrict`, if `T`
is quasi-compact then `R^q f_* ℱ = 0` for all large `q`: finitely many of the neighbourhoods
given there cover `T`.

(blueprint: `sk-thm-picard-coherence`) -/
theorem exists_isZero_higherDirectImage [CompactSpace T] (hℱ : ℱ.IsFlatOver f) :
    ∃ N, ∀ q ≥ N, IsZero ((higherDirectImage f q).obj ℱ) :=
  sorry

/-- **Semicontinuity of the fibre dimension.** With `f : X ⟶ T` proper of finite presentation
and `ℱ` an `𝒪_X`-module of finite presentation which is flat over `T`, the fibre dimension
`t ↦ dim_{κ(t)} H^q(X_t, ℱ_t)` is upper semicontinuous on `T`.

Locally on `T` the fibre dimension is `dim_{κ(t)} H^q(P ⊗ κ(t))` for the bounded complex `P` of
finite free modules of
`AlgebraicGeometry.Scheme.Modules.exists_finiteFreeComplex_higherDirectImage`, and the dimension
of the cohomology of a complex of finite free modules is upper semicontinuous in the point.

(blueprint: `sk-thm-picard-semicon`) -/
theorem upperSemicontinuous_hFiber (hℱ : ℱ.IsFlatOver f) (q : ℕ) :
    UpperSemicontinuous (ℱ.hFiber f q) :=
  sorry

/-- **Grauert's theorem.** In the situation of
`AlgebraicGeometry.Scheme.Modules.upperSemicontinuous_hFiber`, if moreover `T` is reduced and
the `q`-th fibre dimension is locally constant, then `R^q f_* ℱ` is locally free of finite rank,
the rank at a point being the fibre dimension there.

The rank is only attached to a neighbourhood of each point, not to `T` as a whole: on a
disconnected base the fibre dimension can be locally constant without being constant.

(blueprint: `sk-thm-picard-semicon`) -/
theorem exists_isFiniteLocallyFreeOfRank_higherDirectImage_of_isLocallyConstant [IsReduced T]
    (hℱ : ℱ.IsFlatOver f) (q : ℕ) (hq : IsLocallyConstant (ℱ.hFiber f q)) (t : T) :
    ∃ U : T.Opens, t ∈ U ∧
      (((higherDirectImage f q).obj ℱ).restrict U.ι).IsFiniteLocallyFreeOfRank
        (ℱ.hFiber f q t) :=
  sorry

/-- **Openness of the perfect locus.** With `f : X ⟶ T` proper of finite presentation and `ℱ`
an `𝒪_X`-module of finite presentation which is flat over `T`, the locus of points `t` of `T`
at which the fibre cohomology `H^q(X_t, ℱ_t)` vanishes for all `q ≠ i` and has dimension at
most `r` in degree `i` is open in `T`.

(blueprint: `sk-thm-picard-perfect`) -/
theorem isOpen_setOf_hFiber_le (hℱ : ℱ.IsFlatOver f) (i r : ℕ) :
    IsOpen {t : T | (∀ q, q ≠ i → ℱ.hFiber f q t = 0) ∧ ℱ.hFiber f i t ≤ r} :=
  sorry

/-- **The higher direct images vanish off degree `i` over the perfect locus.** Over an open
subscheme of `T` on which the fibre cohomology vanishes outside degree `i` and has dimension
exactly `r` in degree `i`, the higher direct images `R^q f_* ℱ` vanish for `q ≠ i`.

Together with
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_higherDirectImage_restrict` this is
the concrete form of "`R f_* ℱ` is perfect of amplitude `[i, i]`" on that locus, there being no
derived category of `X.Modules` available.

(blueprint: `sk-thm-picard-perfect`) -/
theorem isZero_higherDirectImage_restrict (hℱ : ℱ.IsFlatOver f) (i r : ℕ) (U : T.Opens)
    (hU : ↑U ⊆ {t : T | (∀ q, q ≠ i → ℱ.hFiber f q t = 0) ∧ ℱ.hFiber f i t = r})
    (q : ℕ) (hq : q ≠ i) :
    IsZero (((higherDirectImage f q).obj ℱ).restrict U.ι) :=
  sorry

/-- **The `i`-th higher direct image is finite locally free over the perfect locus.** Over an
open subscheme of `T` on which the fibre cohomology vanishes outside degree `i` and has
dimension exactly `r` in degree `i`, the higher direct image `R^i f_* ℱ` is finite locally free
of rank `r`.

(blueprint: `sk-thm-picard-perfect`) -/
theorem isFiniteLocallyFreeOfRank_higherDirectImage_restrict (hℱ : ℱ.IsFlatOver f) (i r : ℕ)
    (U : T.Opens)
    (hU : ↑U ⊆ {t : T | (∀ q, q ≠ i → ℱ.hFiber f q t = 0) ∧ ℱ.hFiber f i t = r}) :
    (((higherDirectImage f i).obj ℱ).restrict U.ι).IsFiniteLocallyFreeOfRank r :=
  sorry

/-- **The fibre dimension is locally constant on the perfect locus.** On the locus
`U_{i,≤r}` of points `t` of `T` at which `H^q(X_t, ℱ_t)` vanishes for all `q ≠ i` and has
dimension at most `r` in degree `i`, the fibre dimension `t ↦ dim_{κ(t)} H^i(X_t, ℱ_t)` is
locally constant.

(blueprint: `sk-thm-picard-perfect`) -/
theorem isLocallyConstant_hFiber_restrict (hℱ : ℱ.IsFlatOver f) (i r : ℕ) :
    IsLocallyConstant fun t : {t : T | (∀ q, q ≠ i → ℱ.hFiber f q t = 0) ∧ ℱ.hFiber f i t ≤ r} ↦
      ℱ.hFiber f i t :=
  sorry

/-- **Openness of the rank-`r` perfect locus.** The locus `U_{i,r}` of points `t` of `T` at which
the fibre cohomology `H^q(X_t, ℱ_t)` vanishes for all `q ≠ i` and has dimension exactly `r` in
degree `i` is open in `T`.

(blueprint: `sk-thm-picard-perfect`) -/
theorem isOpen_setOf_hFiber_eq (hℱ : ℱ.IsFlatOver f) (i r : ℕ) :
    IsOpen {t : T | (∀ q, q ≠ i → ℱ.hFiber f q t = 0) ∧ ℱ.hFiber f i t = r} :=
  sorry

/-- **Vanishing off degree `i` after base change to the perfect locus.** Let `U` be an open
subscheme of `T` contained in the locus `U_{i,r}` where the fibre cohomology vanishes outside
degree `i` and has dimension `r` in degree `i`. For every `g : T' ⟶ U`, with `f' : X' ⟶ T'` the
base change of `f` along `g ≫ U.ι` and `ℱ'` the pullback of `ℱ` to `X'`, the higher direct
images `R^q f'_* ℱ'` vanish for `q ≠ i`.

(blueprint: `sk-thm-picard-perfect`) -/
theorem isZero_higherDirectImage_of_isPullback (hℱ : ℱ.IsFlatOver f) (i r : ℕ) (U : T.Opens)
    (hU : ↑U ⊆ {t : T | (∀ q, q ≠ i → ℱ.hFiber f q t = 0) ∧ ℱ.hFiber f i t = r})
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    [HasInjectiveResolutions X'.Modules] (h : IsPullback g' f' f (g ≫ U.ι)) (q : ℕ)
    (hq : q ≠ i) :
    IsZero ((higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ)) :=
  sorry

/-- **Local freeness in degree `i` after base change to the perfect locus.** In the situation of
`AlgebraicGeometry.Scheme.Modules.isZero_higherDirectImage_of_isPullback`, the higher direct
image `R^i f'_* ℱ'` is finite locally free of rank `r`: the base-change maps are isomorphisms
over `U_{i,r}`.

(blueprint: `sk-thm-picard-perfect`) -/
theorem isFiniteLocallyFreeOfRank_higherDirectImage_of_isPullback (hℱ : ℱ.IsFlatOver f)
    (i r : ℕ) (U : T.Opens)
    (hU : ↑U ⊆ {t : T | (∀ q, q ≠ i → ℱ.hFiber f q t = 0) ∧ ℱ.hFiber f i t = r})
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    [HasInjectiveResolutions X'.Modules] (h : IsPullback g' f' f (g ≫ U.ι)) :
    ((higherDirectImage f' i).obj ((Modules.pullback g').obj ℱ)).IsFiniteLocallyFreeOfRank r :=
  sorry

/-- **Functorial characterisation of the rank-`r` perfect locus.** A morphism `g : T' ⟶ T`
factors through the locus `U_{i,r}` where the fibre cohomology vanishes outside degree `i` and
has dimension `r` in degree `i` if and only if, with `f' : X' ⟶ T'` the base change of `f` along
`g` and `ℱ'` the pullback of `ℱ` to `X'`, the higher direct images `R^q f'_* ℱ'` vanish for
`q ≠ i` and `R^i f'_* ℱ'` is finite locally free of rank `r`; that is, `R f'_* ℱ'` is a finite
locally free module of rank `r` placed in degree `i`.

(blueprint: `sk-thm-picard-perfect`) -/
theorem range_subset_setOf_hFiber_eq_iff (hℱ : ℱ.IsFlatOver f) (i r : ℕ)
    {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
    [HasInjectiveResolutions X'.Modules] (h : IsPullback g' f' f g) :
    Set.range g.base ⊆ {t : T | (∀ q, q ≠ i → ℱ.hFiber f q t = 0) ∧ ℱ.hFiber f i t = r} ↔
      (∀ q, q ≠ i → IsZero ((higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ))) ∧
        ((higherDirectImage f' i).obj ((Modules.pullback g').obj ℱ)).IsFiniteLocallyFreeOfRank r :=
  sorry

end Coherence

end AlgebraicGeometry.Scheme.Modules
