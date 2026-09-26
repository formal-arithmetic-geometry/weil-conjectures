/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Semicontinuity.Defs
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

@[expose] public section

/-!
# Higher direct images and cohomology and base change

Let `f : X ⟶ T` be a proper morphism of finite presentation and let `ℱ` be an `𝒪_X`-module of
finite presentation which is flat over `T`. This file states the three fundamental finiteness
and base-change results about the higher direct images `R^q f_* ℱ`.

The higher direct images are the right derived functors of the pushforward functor
`AlgebraicGeometry.Scheme.Modules.pushforward f` between the abelian categories `X.Modules`
and `T.Modules`.

## Main definitions

- `SheafOfModules.IsFiniteLocallyFreeOfRank`: a sheaf of modules is finite locally free of
  rank `r` if it admits locally free local generators data all of whose generating families
  are indexed by a type with exactly `r` elements.
- `AlgebraicGeometry.Scheme.Modules.higherDirectImage`: the `q`-th higher direct image
  functor `R^q f_*`, the `q`-th right derived functor of the pushforward.
- `AlgebraicGeometry.Scheme.Modules.IsFlatOver`: a placeholder for flatness of a sheaf of
  modules over the base of a morphism.
- `AlgebraicGeometry.Scheme.Modules.hFiber`: the fibre dimension
  `dim_{κ(t)} H^q(X_t, ℱ_t)`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage`: coherence of the
  higher direct images.
- `AlgebraicGeometry.Scheme.Modules.upperSemicontinuous_hFiber`: semicontinuity and base
  change.
- `AlgebraicGeometry.Scheme.Modules.isOpen_setOf_hFiber_eq_zero`: openness of the perfect
  locus.
-/

universe v₁ u₁ u

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A sheaf of modules is *finite locally free of rank `r`* if it admits local generators data
which is locally free data (`SheafOfModules.LocalGeneratorsData.IsLocallyFreeData`) and whose
family of generators over each member of the covering is indexed by a type with exactly `r`
elements. Such a sheaf of modules is in particular locally free, hence quasi-coherent. -/
@[stacks 01C6]
class IsFiniteLocallyFreeOfRank (M : SheafOfModules.{u} R) (r : ℕ) : Prop where
  exists_localGeneratorsData : ∃ q : LocalGeneratorsData.{u₁} M, ∃ _ : q.IsLocallyFreeData,
    ∀ i, Nonempty ((q.generators i).I ≃ Fin r)

theorem IsFiniteLocallyFreeOfRank.isLocallyFree (M : SheafOfModules.{u} R) (r : ℕ)
    [h : M.IsFiniteLocallyFreeOfRank r] : M.IsLocallyFree :=
  have := h.exists_localGeneratorsData.choose_spec.choose
  ⟨_, this⟩

end SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}}

/-- The `q`-th **higher direct image** functor `R^q f_*` along a morphism of schemes
`f : X ⟶ T`: the `q`-th right derived functor of the pushforward functor
`AlgebraicGeometry.Scheme.Modules.pushforward f : X.Modules ⥤ T.Modules`.

Both `X.Modules` and `T.Modules` are abelian and the pushforward is additive, so the only
extra input is the existence of injective resolutions in `X.Modules`, which is taken as an
instance hypothesis. -/
noncomputable def higherDirectImage (f : X ⟶ T) [HasInjectiveResolutions X.Modules] (q : ℕ) :
    X.Modules ⥤ T.Modules :=
  (pushforward f).rightDerived q

-- TODO(unify): sk-thm-picard-semicon
/-- `ℱ.IsFlatOver f` says that the `𝒪_X`-module `ℱ` is **flat over the base** of the morphism
`f : X ⟶ T`, i.e. that for every point `x` of `X` the stalk `ℱ_x` is a flat module over the
local ring `𝒪_{T, f x}`.

There is no notion of flatness of a sheaf of modules over a base anywhere in Mathlib or in
this project — neither stalks of sheaves of modules as modules over the stalks of the
structure sheaf, nor a tensor product of sheaves of modules, are available — so this is a
placeholder to be replaced once the relevant foundations exist. -/
def IsFlatOver (ℱ : X.Modules) (_f : X ⟶ T) : Prop := sorry

/-- The `q`-th **fibre dimension** `dim_{κ(t)} H^q(X_t, ℱ_t)` of an `𝒪_X`-module `ℱ` along a
morphism `f : X ⟶ T` at a point `t` of `T`: the fibre `X_t = f.fiber t` is a scheme over the
residue field `κ(t) = T.residueField t`, the restriction `ℱ_t` is the pullback of `ℱ` along
`f.fiberι t`, and the dimension is `AlgebraicGeometry.Scheme.Modules.h` for that base
field. -/
noncomputable def hFiber (ℱ : X.Modules) (f : X ⟶ T) (q : ℕ) (t : T) : ℕ :=
  letI := f.fiberOverSpecResidueField t
  ((Modules.pullback (f.fiberι t)).obj ℱ).h (T.residueField t) q

variable (f : X ⟶ T) (ℱ : X.Modules)

/-- Blueprint `sk-thm-picard-coherence`: Coherence of the higher direct images

With `f : X ⟶ T` proper of finite presentation and `ℱ` an `𝒪_X`-module of finite
presentation which is flat over `T`, the higher direct image `R^q f_* ℱ` is a coherent
`𝒪_T`-module for every `q`, and it vanishes for `q ≫ 0`.

There is no `IsCoherent` class for sheaves of modules anywhere in Mathlib or in this project.
Over a locally Noetherian base, coherence is equivalent to being quasi-coherent and of finite
presentation, so we state the conclusion as
`SheafOfModules.IsQuasicoherent` together with `SheafOfModules.IsFinitePresentation`, which is
the usable substitute; it should be replaced by coherence once that notion exists. -/
theorem isFinitePresentation_higherDirectImage [IsProper f] [LocallyOfFinitePresentation f]
    [QuasiCompact f] [HasInjectiveResolutions X.Modules] [ℱ.IsFinitePresentation]
    (hℱ : ℱ.IsFlatOver f) :
    (∀ q, ((higherDirectImage f q).obj ℱ).IsQuasicoherent ∧
        ((higherDirectImage f q).obj ℱ).IsFinitePresentation) ∧
      ∃ N, ∀ q ≥ N, IsZero ((higherDirectImage f q).obj ℱ) :=
  sorry

/-- Blueprint `sk-thm-picard-semicon`: Semicontinuity and base change

With `f : X ⟶ T` proper of finite presentation and `ℱ` an `𝒪_X`-module of finite
presentation which is flat over `T`, the fibre dimension
`t ↦ dim_{κ(t)} H^q(X_t, ℱ_t)` is upper semicontinuous on `T` for every `q`. If moreover `T`
is reduced and this function is locally constant, then `R^q f_* ℱ` is finite locally free (in
particular flat) and the base-change maps in degree `q` are isomorphisms.

The blueprint statement also asserts the existence of canonical base-change maps
`R^q f_* ℱ ⊗_{𝒪_T} κ(t) → H^q(X_t, ℱ_t)` and their bijectivity in the locally constant case.
There is no tensor product of sheaves of modules in Mathlib or in this project, so that
comparison map cannot yet be built; only the finite local freeness conclusion is recorded
here, and the base-change comparison awaits a tensor product of sheaves of modules. -/
theorem upperSemicontinuous_hFiber [IsProper f] [LocallyOfFinitePresentation f]
    [QuasiCompact f] [HasInjectiveResolutions X.Modules] [ℱ.IsFinitePresentation]
    (hℱ : ℱ.IsFlatOver f) :
    (∀ q, UpperSemicontinuous (ℱ.hFiber f q)) ∧
      (IsReduced T → ∀ q, IsLocallyConstant (ℱ.hFiber f q) →
        ∃ r, ((higherDirectImage f q).obj ℱ).IsFiniteLocallyFreeOfRank r) :=
  sorry

/-- Blueprint `sk-thm-picard-perfect`: Openness of the perfect locus

With `f : X ⟶ T` proper of finite presentation and `ℱ` an `𝒪_X`-module of finite
presentation which is flat over `T`, the locus of points `t` of `T` at which the fibre
cohomology `H^q(X_t, ℱ_t)` vanishes for all `q ≠ i` and has dimension at most `r` in degree
`i` is open in `T`; over any open subscheme contained in the locus where moreover the `i`-th
fibre dimension is exactly `r`, the higher direct images `R^q f_* ℱ` vanish for `q ≠ i` and
`R^i f_* ℱ` is finite locally free of rank `r`.

This is the concrete form of the blueprint statement that `R f_* ℱ` is perfect of amplitude
`[i, i]` on the locus: there is no derived category of `X.Modules` available, so the
condition is spelt out by the vanishing of the individual higher direct images together with
a rank bound. -/
theorem isOpen_setOf_hFiber_eq_zero [IsProper f] [LocallyOfFinitePresentation f]
    [QuasiCompact f] [HasInjectiveResolutions X.Modules] [ℱ.IsFinitePresentation]
    (hℱ : ℱ.IsFlatOver f) (i r : ℕ) :
    IsOpen {t : T | (∀ q, q ≠ i → ℱ.hFiber f q t = 0) ∧ ℱ.hFiber f i t ≤ r} ∧
      ∀ U : T.Opens, (↑U ⊆ {t : T | (∀ q, q ≠ i → ℱ.hFiber f q t = 0) ∧
          ℱ.hFiber f i t = r}) →
        (∀ q, q ≠ i → IsZero (((higherDirectImage f q).obj ℱ).restrict U.ι)) ∧
          (((higherDirectImage f i).obj ℱ).restrict U.ι).IsFiniteLocallyFreeOfRank r :=
  sorry

end AlgebraicGeometry.Scheme.Modules
