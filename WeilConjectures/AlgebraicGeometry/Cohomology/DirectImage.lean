/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
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
- `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage` and
  `isZero_higherDirectImage_of_le`: coherence of the higher direct images, and their vanishing
  in large degrees.
- `AlgebraicGeometry.Scheme.Modules.upperSemicontinuous_hFiber` and
  `exists_isFiniteLocallyFreeOfRank_higherDirectImage_of_isLocallyConstant`: semicontinuity of
  the fibre dimension, and Grauert's theorem over a reduced base.
- `AlgebraicGeometry.Scheme.Modules.isOpen_setOf_hFiber_le`,
  `isZero_higherDirectImage_restrict` and
  `isFiniteLocallyFreeOfRank_higherDirectImage_restrict`: openness of the perfect locus, and
  the shape of `R f_* ℱ` over it.
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

/-- **Coherence of the higher direct images.** With `f : X ⟶ T` proper of finite presentation
and `ℱ` an `𝒪_X`-module of finite presentation which is flat over `T`, the higher direct image
`R^q f_* ℱ` is a coherent `𝒪_T`-module for every `q`; coherence is spelled as quasi-coherence
together with finite presentation.

(blueprint: `sk-thm-picard-coherence`) -/
theorem isFinitePresentation_higherDirectImage (hℱ : ℱ.IsFlatOver f) (q : ℕ) :
    ((higherDirectImage f q).obj ℱ).IsQuasicoherent ∧
      ((higherDirectImage f q).obj ℱ).IsFinitePresentation :=
  sorry

/-- **Vanishing of the higher direct images in large degrees.** In the situation of
`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage`, `R^q f_* ℱ = 0` for
all large `q`.

(blueprint: `sk-thm-picard-coherence`) -/
theorem exists_isZero_higherDirectImage (hℱ : ℱ.IsFlatOver f) :
    ∃ N, ∀ q ≥ N, IsZero ((higherDirectImage f q).obj ℱ) :=
  sorry

/-- **Semicontinuity of the fibre dimension.** With `f : X ⟶ T` proper of finite presentation
and `ℱ` an `𝒪_X`-module of finite presentation which is flat over `T`, the fibre dimension
`t ↦ dim_{κ(t)} H^q(X_t, ℱ_t)` is upper semicontinuous on `T`.

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

end Coherence

end AlgebraicGeometry.Scheme.Modules
