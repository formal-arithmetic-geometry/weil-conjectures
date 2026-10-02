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
along `g : T' ⟶ T` is spelled out through an explicit cartesian square `sq : IsPullback g' f' f g`
```
X' --g'--> X
|          |
f'         f
v          v
T' --g---> T
```
and the pullback `ℱ' := (Modules.pullback g').obj ℱ`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.higherDirectImage`: the `q`-th higher direct image
  functor `R^q f_*`, the `q`-th right derived functor of the pushforward.
- `AlgebraicGeometry.Scheme.Modules.IsFlatOver`: flatness of a sheaf of modules over the base
  of a morphism, checked on affine opens.
- `AlgebraicGeometry.Scheme.Modules.hFiber`: the fibre dimension
  `dim_{κ(t)} H^q(X_t, ℱ_t)`.
- `AlgebraicGeometry.Scheme.Modules.IsFiniteFreeComplex`: a cochain complex of finite free
  modules concentrated in degrees `[0, d]`.
- `AlgebraicGeometry.Scheme.Modules.perfectLocus` and `perfectLocusOfRank`: the loci `U_i` and
  `U_{i,r}` of points where the fibre cohomology vanishes outside degree `i` (and has dimension
  `r` in degree `i`).

## Main statements

- `AlgebraicGeometry.Scheme.Modules.nonempty_sections_higherDirectImage_iso_H`: over an affine
  base, the global sections of `R^q f_* ℱ` are `H^q(X, ℱ)`.
- `AlgebraicGeometry.Scheme.Modules.nonempty_higherDirectImage_iso_restrict`: the higher direct
  images commute with restriction to an open subscheme of the base.
- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_higherDirectImage`,
  `exists_isZero_higherDirectImage_restrict` and `exists_isZero_higherDirectImage`: for `f`
  quasi-compact and quasi-separated (resp. separated) and `ℱ` quasi-coherent, the higher direct
  images are quasi-coherent, vanish in large degrees locally on `T`, and vanish uniformly in large
  degrees over a quasi-compact `T`.
- `AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage`: over any base,
  `R f_* ℱ` is locally given by a bounded complex of finite free modules compatible with base
  change.
- `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage`: coherence of the
  higher direct images over a locally Noetherian base.
- `AlgebraicGeometry.Scheme.Modules.upperSemicontinuous_hFiber` and
  `exists_isFiniteLocallyFreeOfRank_higherDirectImage_of_isLocallyConstant`: semicontinuity of
  the fibre dimension, and Grauert's theorem over a reduced base.
- `AlgebraicGeometry.Scheme.Modules.isOpen_setOf_hFiber_le`,
  `isLocallyConstant_domRestrict_hFiber` and `isOpen_perfectLocusOfRank`: openness of the perfect
  locus, local constancy of the fibre dimension on it, and openness of the rank-`r` locus.
- `AlgebraicGeometry.Scheme.Modules.isZero_higherDirectImage_of_isPullback`,
  `isFiniteLocallyFreeOfRank_higherDirectImage_of_isPullback` and
  `range_subset_perfectLocusOfRank_iff`: after any base change into the rank-`r` perfect locus
  `R f_* ℱ` is finite locally free of rank `r` in degree `i`, and this characterises the locus.
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

/-- The **perfect locus** `U_i` of an `𝒪_X`-module `ℱ` along `f : X ⟶ T` in degree `i`: the set
of points `t` of `T` at which the fibre cohomology `H^q(X_t, ℱ_t)` vanishes for all `q ≠ i`. -/
def perfectLocus (ℱ : X.Modules) (f : X ⟶ T) (i : ℕ) : Set T :=
  {t | ∀ q ≠ i, ℱ.hFiber f q t = 0}

/-- The **rank-`r` perfect locus** `U_{i,r}` of an `𝒪_X`-module `ℱ` along `f : X ⟶ T`: the set of
points `t` of `T` at which the fibre cohomology `H^q(X_t, ℱ_t)` vanishes for all `q ≠ i` and has
dimension `r` in degree `i`. -/
def perfectLocusOfRank (ℱ : X.Modules) (f : X ⟶ T) (i r : ℕ) : Set T :=
  {t ∈ ℱ.perfectLocus f i | ℱ.hFiber f i t = r}

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

section BaseChange

variable [HasInjectiveResolutions X.Modules]

/-- **The higher direct images commute with restriction to an open subscheme of the base.** Let
`g : T' ⟶ T` be an open immersion, and let `f' : X' ⟶ T'` and `g' : X' ⟶ X` be the base change
of `f` along `g`, in the cartesian square `sq`
```
X' --g'--> X
|          |
f'         f
v          v
T' --g---> T
```
Then `R^q f'_* (g'^* ℱ) ≅ (R^q f_* ℱ)|_{T'}` for every `q`.

This is flat base change along an open immersion, and holds for any `f` and any `ℱ`: restriction
to an open subscheme preserves injective `𝒪_X`-modules and commutes with the pushforward. -/
theorem nonempty_higherDirectImage_iso_restrict {T' X' : Scheme.{u}} (g : T' ⟶ T)
    [IsOpenImmersion g] (g' : X' ⟶ X) (f' : X' ⟶ T') [HasInjectiveResolutions X'.Modules]
    (sq : IsPullback g' f' f g) (q : ℕ) :
    Nonempty ((higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ) ≅
      ((higherDirectImage f q).obj ℱ).restrict g) :=
  sorry

end BaseChange

section QuasiCoherence

variable [QuasiCompact f] [QuasiSeparated f] [HasInjectiveResolutions X.Modules]
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

/-- **Quasi-coherence of the higher direct images.** For `f : X ⟶ T` quasi-compact and
quasi-separated and `ℱ` a quasi-coherent `𝒪_X`-module, the higher direct image `R^q f_* ℱ` is a
quasi-coherent `𝒪_T`-module for every `q` [Stacks, Tag 01XJ].

(blueprint: `sk-thm-picard-coherence`) -/
theorem isQuasicoherent_higherDirectImage (q : ℕ) :
    ((higherDirectImage f q).obj ℱ).IsQuasicoherent :=
  sorry

end QuasiCoherence

section Vanishing

variable [QuasiCompact f] [IsSeparated f] [HasInjectiveResolutions X.Modules]
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

/-- **Local vanishing of the higher direct images in large degrees.** For `f : X ⟶ T`
quasi-compact and separated and `ℱ` a quasi-coherent `𝒪_X`-module, every point `t` of `T` has an
open neighbourhood `U` and a bound `d` with `R^q f_* ℱ|_U = 0` for all `q ≥ d`.

Take for `U` an affine open neighbourhood of `t`: then `f ⁻¹ᵁ U` is covered by finitely many,
say `d`, affine opens whose intersections are affine, and the Čech complex of this cover
computes `R f_* ℱ|_U` [Stacks, Tag 01XD], so `R^q f_* ℱ|_U = 0` for `q ≥ d`.

The bound is only local on `T`: over `T = ⨆ₙ Spec k` with `X = ⨆ₙ ℙⁿ_k` and `ℱ = 𝒪(-n-1)` on
the `n`-th piece, `R^n f_* ℱ ≠ 0` for every `n`.

(blueprint: `sk-thm-picard-coherence`) -/
theorem exists_isZero_higherDirectImage_restrict (t : T) :
    ∃ (U : T.Opens) (d : ℕ), t ∈ U ∧
      ∀ q ≥ d, IsZero (((higherDirectImage f q).obj ℱ).restrict U.ι) :=
  sorry

/-- **Vanishing of the higher direct images in large degrees over a quasi-compact base.** In the
situation of `AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage_restrict`, if `T`
is quasi-compact then `R^q f_* ℱ = 0` for all large `q`: finitely many of the neighbourhoods
given there cover `T`, and one takes for `N` the maximum of their bounds.

(blueprint: `sk-thm-picard-coherence`) -/
theorem exists_isZero_higherDirectImage [CompactSpace T] :
    ∃ N, ∀ q ≥ N, IsZero ((higherDirectImage f q).obj ℱ) :=
  sorry

end Vanishing

/-- `IsFiniteFreeComplex P d` says that the cochain complex `P` of `𝒪_X`-modules is a **bounded
complex of finite free modules in degrees `[0, d]`**: it vanishes outside `[0, d]`, and each
`P.X n` is isomorphic to a free module `𝒪_X^r` of finite rank. -/
structure IsFiniteFreeComplex (P : CochainComplex X.Modules ℤ) (d : ℕ) : Prop where
  isStrictlyGE : P.IsStrictlyGE 0
  isStrictlyLE : P.IsStrictlyLE d
  exists_iso_free (n : ℤ) :
    ∃ r : ℕ, Nonempty (P.X n ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r)))

section Coherence

variable [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
  [HasInjectiveResolutions X.Modules] [ℱ.IsFinitePresentation]

/-- **Perfectness of the higher direct images, with base change.** With `f : X ⟶ T` proper of
finite presentation and `ℱ` an `𝒪_X`-module of finite presentation which is flat over `T`, every
point `t` of `T` has an open neighbourhood `U` over which `R f_* ℱ` is represented by a bounded
complex `P` of finite free `𝒪_U`-modules whose formation commutes with every base change: for
every `g : T' ⟶ U`, with `f' : X' ⟶ T'` the base change of `f` along `g ≫ U.ι` in the cartesian
square `sq`
```
X' ------g'-------> X
|                   |
f'                  f
v                   v
T' --g--> U --U.ι--> T
```
and `ℱ'` the pullback of `ℱ` to `X'`, the cohomology of the pullback `g^* P` is `R^q f'_* ℱ'`.

Taking `g = 𝟙 U` and for `sq` the square `(isPullback_morphismRestrict f U).flip`, and
combining with `AlgebraicGeometry.Scheme.Modules.nonempty_higherDirectImage_iso_restrict`, the
cohomology of `P` itself is `R^q f_* ℱ|_U`.

The isomorphisms are only required to exist for each `g` and `q` separately: they are not
asserted to be the canonical base-change maps, nor to be compatible with composition of the
`g`. This suffices for semicontinuity of the fibre dimension and for the perfect locus, but not
for the clause of Grauert's theorem saying that the canonical maps
`R^q f_* ℱ ⊗ κ(t) → H^q(X_t, ℱ_t)` are isomorphisms; stating that needs the base-change map of
higher direct images, which is not available.

The proof needs, over a Noetherian affine base, Mumford's complex, obtained from the Čech complex
of a finite affine cover, which is a bounded complex of flat modules by the flatness of `ℱ`,
together with `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage`; the
general case reduces to this by Noetherian approximation of `(f, ℱ)` [EGA IV₃, §8 and §11.2].
Alternatively, it follows from Kiehl's theorem that `R f_* ℱ` is pseudo-coherent, and finite
Tor-amplitude coming from flatness [Stacks, Tags 0B91 and 0A1H].

(blueprint: `sk-thm-picard-coherence`) -/
theorem exists_isFiniteFreeComplex_higherDirectImage (hℱ : ℱ.IsFlatOver f) (t : T) :
    ∃ (U : T.Opens) (P : CochainComplex U.toScheme.Modules ℤ) (d : ℕ), t ∈ U ∧
      IsFiniteFreeComplex P d ∧
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ)) :=
  sorry

/-- **Coherence of the higher direct images over a locally Noetherian base.** With
`f : X ⟶ T` proper, `T` locally Noetherian and `ℱ` a coherent `𝒪_X`-module, the higher direct
image `R^q f_* ℱ` is a coherent `𝒪_T`-module for every `q` [EGA III₁, 3.2.1],
[Stacks, Tag 02O5]. Coherence is spelled as quasi-coherence together with finite presentation;
quasi-coherence of `R^q f_* ℱ` is
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_higherDirectImage`, so only finite
presentation is stated here.

The Noetherian hypothesis cannot be dropped, even for `ℱ` flat over `T`. Let `k` be a field,
`V` an infinite-dimensional `k`-vector space, `T = Spec (k ⊕ V)` with `V` a square-zero ideal,
`E` an elliptic curve over `k` and `f : E × T ⟶ T` the projection. Line bundles on `E × T`
which are trivial on `E` are classified by `H¹(E, 𝒪_E) ⊗_k V ≅ V`; let `ℒ` be the one with class
a nonzero `v ∈ V`. The sequence `0 ⟶ 𝒪_E ⊗_k V ⟶ ℒ ⟶ 𝒪_E ⟶ 0` has connecting map
`k ⟶ H¹(E, 𝒪_E) ⊗_k V` sending `1` to `v`, so `f_* ℒ` corresponds to the module `V`, which is
killed by `V` and infinite-dimensional over `k`, hence not of finite type over `k ⊕ V`.

(blueprint: `sk-thm-picard-coherence`) -/
theorem isFinitePresentation_higherDirectImage [IsLocallyNoetherian T]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    ((higherDirectImage f q).obj ℱ).IsFinitePresentation :=
  sorry

/-- **Semicontinuity of the fibre dimension.** With `f : X ⟶ T` proper of finite presentation
and `ℱ` an `𝒪_X`-module of finite presentation which is flat over `T`, the fibre dimension
`t ↦ dim_{κ(t)} H^q(X_t, ℱ_t)` is upper semicontinuous on `T`.

Locally on `T` the fibre dimension is `dim_{κ(t)} H^q(P ⊗ κ(t))` for the bounded complex `P` of
finite free modules of
`AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage`, and the
dimension of the cohomology of a complex of finite free modules is upper semicontinuous in the
point.

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
an `𝒪_X`-module of finite presentation which is flat over `T`, the locus `U_{i,≤r}` of points `t`
of `T` at which the fibre cohomology `H^q(X_t, ℱ_t)` vanishes for all `q ≠ i` and has dimension at
most `r` in degree `i` is open in `T`.

(blueprint: `sk-thm-picard-perfect`) -/
theorem isOpen_setOf_hFiber_le (hℱ : ℱ.IsFlatOver f) (i r : ℕ) :
    IsOpen {t ∈ ℱ.perfectLocus f i | ℱ.hFiber f i t ≤ r} :=
  sorry

/-- **The fibre dimension is locally constant on the perfect locus.** On the perfect locus `U_i`
of points `t` of `T` at which `H^q(X_t, ℱ_t)` vanishes for all `q ≠ i`, the fibre dimension
`t ↦ dim_{κ(t)} H^i(X_t, ℱ_t)` is locally constant.

Near a point of `U_i`, Nakayama's lemma applied to the bounded complex of finite free modules of
`AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage` makes it
quasi-isomorphic to a single finite free module placed in degree `i`, whose rank is the fibre
dimension.

(blueprint: `sk-thm-picard-perfect`) -/
theorem isLocallyConstant_domRestrict_hFiber (hℱ : ℱ.IsFlatOver f) (i : ℕ) :
    IsLocallyConstant ((ℱ.perfectLocus f i).domRestrict (ℱ.hFiber f i)) :=
  sorry

/-- **Openness of the rank-`r` perfect locus.** The locus `U_{i,r}` of points `t` of `T` at which
the fibre cohomology `H^q(X_t, ℱ_t)` vanishes for all `q ≠ i` and has dimension exactly `r` in
degree `i` is open in `T`.

This follows from `AlgebraicGeometry.Scheme.Modules.isOpen_setOf_hFiber_le`, which makes `U_i`
the union of the open sets `U_{i,≤r}` and hence open, together with
`AlgebraicGeometry.Scheme.Modules.isLocallyConstant_domRestrict_hFiber`: `U_{i,r}` is the preimage
of `{r}` under a locally constant function on `U_i`.

(blueprint: `sk-thm-picard-perfect`) -/
theorem isOpen_perfectLocusOfRank (hℱ : ℱ.IsFlatOver f) (i r : ℕ) :
    IsOpen (ℱ.perfectLocusOfRank f i r) :=
  sorry

/-- **Vanishing off degree `i` after base change to the perfect locus.** Let `g : T' ⟶ T` have
image in the perfect locus `U_i` where the fibre cohomology vanishes outside degree `i`, and let
`f' : X' ⟶ T'` be the base change of `f` along `g`, in the cartesian square `sq`
```
X' --g'--> X
|          |
f'         f
v          v
T' --g---> T
```
with `ℱ'` the pullback of `ℱ` to `X'`. Then the higher direct images `R^q f'_* ℱ'` vanish for
`q ≠ i`.

Taking for `g` the inclusion `U.ι` of an open `U ⊆ U_i` and for `sq` the square
`(isPullback_morphismRestrict f U).flip`, and combining with
`AlgebraicGeometry.Scheme.Modules.nonempty_higherDirectImage_iso_restrict`, gives
`R^q f_* ℱ|_U = 0` for `q ≠ i`.

(blueprint: `sk-thm-picard-perfect`) -/
theorem isZero_higherDirectImage_of_isPullback (hℱ : ℱ.IsFlatOver f) (i : ℕ)
    {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
    [HasInjectiveResolutions X'.Modules] (sq : IsPullback g' f' f g)
    (hg : Set.range g.base ⊆ ℱ.perfectLocus f i) (q : ℕ) (hq : q ≠ i) :
    IsZero ((higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ)) :=
  sorry

/-- **Local freeness in degree `i` after base change to the perfect locus.** In the situation of
`AlgebraicGeometry.Scheme.Modules.isZero_higherDirectImage_of_isPullback`, if the image of `g`
lies in the rank-`r` perfect locus `U_{i,r}`, then the higher direct image `R^i f'_* ℱ'` is
finite locally free of rank `r`.

Taking for `g` the inclusion `U.ι` of an open `U ⊆ U_{i,r}` as in
`AlgebraicGeometry.Scheme.Modules.isZero_higherDirectImage_of_isPullback` shows that
`R^i f_* ℱ|_U` is finite locally free of rank `r`.

(blueprint: `sk-thm-picard-perfect`) -/
theorem isFiniteLocallyFreeOfRank_higherDirectImage_of_isPullback (hℱ : ℱ.IsFlatOver f)
    (i r : ℕ) {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
    [HasInjectiveResolutions X'.Modules] (sq : IsPullback g' f' f g)
    (hg : Set.range g.base ⊆ ℱ.perfectLocusOfRank f i r) :
    ((higherDirectImage f' i).obj ((Modules.pullback g').obj ℱ)).IsFiniteLocallyFreeOfRank r :=
  sorry

/-- **Functorial characterisation of the rank-`r` perfect locus.** Let `g : T' ⟶ T`, and let
`f' : X' ⟶ T'` be the base change of `f` along `g`, in the cartesian square `sq`
```
X' --g'--> X
|          |
f'         f
v          v
T' --g---> T
```
with `ℱ'` the pullback of `ℱ` to `X'`. Then the image of `g` lies in the rank-`r` perfect locus
`U_{i,r}` if and only if `R f'_* ℱ'` is a finite locally free module of rank `r` placed in
degree `i`: the higher direct images `R^q f'_* ℱ'` vanish for `q ≠ i` and `R^i f'_* ℱ'` is
finite locally free of rank `r`.

The forward direction is `AlgebraicGeometry.Scheme.Modules.isZero_higherDirectImage_of_isPullback`
together with
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_higherDirectImage_of_isPullback`. For
the converse, base change further to the fibre over a point `t'` of `T'`: the right-hand side then
gives `H^q(X'_{t'}, ℱ'_{t'}) = 0` for `q ≠ i` and `dim H^i(X'_{t'}, ℱ'_{t'}) = r`, and these
dimensions equal those over `g t'`, since cohomology commutes with the field extension
`κ(g t') ⟶ κ(t')`.

(blueprint: `sk-thm-picard-perfect`) -/
theorem range_subset_perfectLocusOfRank_iff (hℱ : ℱ.IsFlatOver f) (i r : ℕ)
    {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
    [HasInjectiveResolutions X'.Modules] (sq : IsPullback g' f' f g) :
    Set.range g.base ⊆ ℱ.perfectLocusOfRank f i r ↔
      (∀ q ≠ i, IsZero ((higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ))) ∧
        ((higherDirectImage f' i).obj ((Modules.pullback g').obj ℱ)).IsFiniteLocallyFreeOfRank r :=
  sorry

end Coherence

end AlgebraicGeometry.Scheme.Modules
