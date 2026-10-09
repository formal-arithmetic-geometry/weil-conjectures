/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Semicontinuity.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplex
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.Algebra.BigOperators.Intervals
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived

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
an instance hypothesis `[HasInjectiveResolutions X.Modules]`. It can be discharged by
`AlgebraicGeometry.Scheme.Modules.isGrothendieckAbelian`, which gives `EnoughInjectives` and
hence `HasInjectiveResolutions`; it is not an instance, so the hypothesis is kept in the
statements here and downstream.

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
- `AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeInDegree`: a family of cohomology sheaves
  is that of a finite locally free module of rank `r` placed in degree `i`.
- `AlgebraicGeometry.Scheme.Modules.perfectLocus` and `perfectLocusOfRank`: the perfect locus
  `U_i` of points where the fibre cohomology vanishes outside degree `i`, and the locus `U_{i,r}`
  where moreover it has dimension `r` in degree `i`.
- `AlgebraicGeometry.Scheme.Modules.eulerCharFiber`: the Euler characteristic of the fibres.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.nonempty_sections_higherDirectImage_iso_H` and
  `exists_bijective_semilinearMap_sections_higherDirectImage_H`: over an affine base, the global
  sections of `R^q f_* ℱ` are `H^q(X, ℱ)`, linearly over `Γ(T, ⊤)`. Hence
  (`hFiber_eq_finrank_sections_higherDirectImage`) the fibre dimension is the dimension of the
  higher direct image of the fibre to the point; over a field `K`, the sections of `R^q f_* ℱ`
  are `H^q(X, ℱ)` as `K`-vector spaces
  (`nonempty_moduleSpecΓFunctor_obj_higherDirectImage_linearEquiv_H`).
- `AlgebraicGeometry.Scheme.Modules.nonempty_higherDirectImage_iso_restrict`: the higher direct
  images commute with restriction to an open subscheme of the base.
- `AlgebraicGeometry.Scheme.Modules.isZero_higherDirectImage_of_isAffineHom` and
  `isQuasicoherent_pushforward_of_isAffineHom`: the higher direct images along an affine morphism
  vanish, and its pushforward preserves quasi-coherence.
- `AlgebraicGeometry.Scheme.Modules.nonempty_higherDirectImage_tensorObj_pullback_iso`: the
  projection formula `R^q f_* (ℱ ⊗ f^* 𝒩) ≅ R^q f_* ℱ ⊗ 𝒩` for an invertible `𝒩`.
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
- `AlgebraicGeometry.Scheme.Modules.finiteDimensional_H_of_isProper`: the cohomology of a
  coherent sheaf on a proper scheme over a field is finite-dimensional.
- `AlgebraicGeometry.Scheme.Modules.upperSemicontinuous_hFiber` and
  `exists_isFiniteLocallyFreeOfRank_higherDirectImage_of_isLocallyConstant`: semicontinuity of
  the fibre dimension, and Grauert's theorem over a reduced base.
- `AlgebraicGeometry.Scheme.Modules.IsFiniteFreeComplex.exists_opens_range_subset_iff`: the
  locus where a bounded complex of finite free modules is finite locally free of rank `r` in
  degree `i` is open, and characterised by pullbacks.
- `AlgebraicGeometry.Scheme.Modules.exists_forall_hFiber_eq_zero`: locally on `T`, the fibre
  cohomology vanishes in large degrees.
- `AlgebraicGeometry.Scheme.Modules.isOpen_setOf_hFiber_le`: openness of the loci `U_{i,≤r}`, and
  hence of the perfect locus `U_i`.
- `AlgebraicGeometry.Scheme.Modules.isLocallyConstant_eulerCharFiber`: the fibre Euler
  characteristic is locally constant; hence so is the fibre dimension on `U_i`
  (`isLocallyConstant_hFiber_restrict`), and `U_{i,r}` is open (`isOpen_perfectLocusOfRank`,
  `isOpen_setOf_hFiber_eq`).
- `AlgebraicGeometry.Scheme.Modules.hFiber_pullback_of_isPullback`: the fibre dimension is
  invariant under base change.
- `AlgebraicGeometry.Scheme.Modules.isZero_higherDirectImage_of_isPullback` and
  `isFiniteLocallyFreeOfRank_higherDirectImage_of_isPullback`: after base change into `U_{i,r}`,
  `R f'_* ℱ'` is finite locally free of rank `r` placed in degree `i`; in particular
  (`isZero_higherDirectImage_restrict` and `isFiniteLocallyFreeOfRank_higherDirectImage_restrict`)
  so is `R f_* ℱ` over an open subscheme contained in `U_{i,r}`.
- `AlgebraicGeometry.Scheme.Modules.nonempty_higherDirectImage_iso_pullback_of_isPullback`: after
  base change into `U_i`, `R^i f'_* ℱ' ≅ g^* R^i f_* ℱ`.
- `AlgebraicGeometry.Scheme.Modules.range_subset_perfectLocusOfRank_iff`,
  `range_subset_setOf_hFiber_eq_iff` and
  `exists_opens_range_subset_iff_isFiniteLocallyFreeInDegree`: this shape of `R f'_* ℱ'`
  characterises the morphisms into `U_{i,r}`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}}

/-- `X.Modules` is a Grothendieck abelian category (`SheafOfModules.isGrothendieckAbelian`).

Together with `CategoryTheory.IsGrothendieckAbelian.enoughInjectives` it supplies the
`HasInjectiveResolutions X.Modules` instance that every statement below, and every statement
about the Picard functor `F` downstream, assumes. -/
theorem isGrothendieckAbelian (X : Scheme.{u}) : IsGrothendieckAbelian.{u} X.Modules :=
  SheafOfModules.isGrothendieckAbelian X.ringCatSheaf

/-- The `q`-th **higher direct image** functor `R^q f_*` along a morphism of schemes
`f : X ⟶ T`: the `q`-th right derived functor of the pushforward functor
`AlgebraicGeometry.Scheme.Modules.pushforward f : X.Modules ⥤ T.Modules`.

Both `X.Modules` and `T.Modules` are abelian and the pushforward is additive, so the only
extra input is the existence of injective resolutions in `X.Modules`, which is taken as an
instance hypothesis. -/
noncomputable def higherDirectImage (f : X ⟶ T) [HasInjectiveResolutions X.Modules] (q : ℕ) :
    X.Modules ⥤ T.Modules :=
  (pushforward f).rightDerived q

/-- **The higher direct images are linear over the base.** Applying `R^q f_*` to multiplication
by `f^♯ a` on `M` gives multiplication by `a` on `R^q f_* M`. -/
lemma higherDirectImage_map_smulHom (f : X ⟶ T) [HasInjectiveResolutions X.Modules] (q : ℕ)
    (M : X.Modules)
    (a : Γ(T, ⊤)) :
    (higherDirectImage f q).map (M.smulHom (f.appTop a)) =
      ((higherDirectImage f q).obj M).smulHom a :=
  (pushforward f).rightDerived_map_app_eq
    { app M := M.smulHom (f.appTop a), naturality _ _ φ := (smulHom_naturality φ _).symm }
    { app N := N.smulHom a, naturality _ _ φ := (smulHom_naturality φ _).symm }
    (fun M ↦ pushforward_map_smulHom f M a) q M

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

/-- **An invertible module is flat over the base of a flat morphism.** If `f : X ⟶ T` is flat
and `ℱ` is an invertible `𝒪_X`-module, then `ℱ` is flat over `T`: on an affine open `U` the
sections `Γ(ℱ, U)` form an invertible, hence flat, `Γ(X, U)`-module, and `Γ(X, U)` is flat over
`Γ(T, V)` by flatness of `f`. -/
theorem isFlatOver_of_isInvertible (f : X ⟶ T) [Flat f] (ℱ : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} ℱ] : ℱ.IsFlatOver f := by
  intro V U e
  let := (f.appLE V.1 U.1 e).hom.toAlgebra
  have : Module.Flat Γ(T, V.1) Γ(X, U.1) := HasRingHomProperty.appLE @Flat f ‹_› V U e
  have := flat_sections_of_isInvertible ℱ U.2
  let : Module Γ(T, V.1) Γ(ℱ, U.1) := Module.compHom _ (f.appLE V.1 U.1 e).hom
  have : IsScalarTower Γ(T, V.1) Γ(X, U.1) Γ(ℱ, U.1) := ⟨fun a b m ↦ mul_smul _ _ _⟩
  exact Module.Flat.trans Γ(T, V.1) Γ(X, U.1) Γ(ℱ, U.1)

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

/-- The **rank-`r` perfect locus** `U_{i,r}` of an `𝒪_X`-module `ℱ` along `f : X ⟶ T`: the set
of points `t` of the perfect locus `U_i` at which `H^i(X_t, ℱ_t)` has dimension `r`. -/
def perfectLocusOfRank (ℱ : X.Modules) (f : X ⟶ T) (i r : ℕ) : Set T :=
  {t ∈ ℱ.perfectLocus f i | ℱ.hFiber f i t = r}

/-- The **fibre Euler characteristic** `Σ_q (-1)^q dim_{κ(t)} H^q(X_t, ℱ_t)` of an `𝒪_X`-module
`ℱ` along `f : X ⟶ T` at a point `t` of `T`. -/
noncomputable def eulerCharFiber (ℱ : X.Modules) (f : X ⟶ T) (t : T) : ℤ :=
  ∑ᶠ q : ℕ, (-1) ^ q * (ℱ.hFiber f q t : ℤ)

/-- The fibre dimensions only depend on the isomorphism class of the module. -/
lemma hFiber_congr {ℱ 𝒢 : X.Modules} (e : ℱ ≅ 𝒢) (f : X ⟶ T) (q : ℕ) (t : T) :
    ℱ.hFiber f q t = 𝒢.hFiber f q t :=
  letI := f.fiberOverSpecResidueField t
  finrankH_congr _ ((Modules.pullback (f.fiberι t)).mapIso e) q

/-- The fibre Euler characteristic only depends on the isomorphism class of the module. -/
lemma eulerCharFiber_congr {ℱ 𝒢 : X.Modules} (e : ℱ ≅ 𝒢) (f : X ⟶ T) :
    ℱ.eulerCharFiber f = 𝒢.eulerCharFiber f := by
  ext t
  simp only [eulerCharFiber, hFiber_congr e]

/-- **The fibre dimension over a field.** For a scheme `X` over a field `K`, through
`f : X ⟶ Spec K`, and a quasi-coherent `𝒪_X`-module `ℱ`, the fibre dimension of `ℱ` at the
unique point of `Spec K` is `dim_K H^q(X, ℱ)`: the fibre of `f` is `X` itself, base changed along
the isomorphism `Spec κ(s) ≅ Spec K`. -/
theorem hFiber_eq_finrankH {K : Type u} [Field K] (f : X ⟶ Spec (.of K)) (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) (s : Spec (.of K)) :
    ℱ.hFiber f q s = letI : X.Over (Spec (.of K)) := ⟨f⟩; ℱ.finrankH K q := by
  let φ := (Spec (.of K)).fromSpecResidueField s
  have : IsClosedImmersion φ := isClosed_singleton_iff_isClosedImmersion.1 (by
    rw [← (Set.subsingleton_of_subsingleton).eq_singleton_of_mem (Set.mem_univ s)]
    exact isClosed_univ)
  have : Surjective φ := ⟨fun t ↦ ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩
  have : IsIso φ := isIso_of_isClosedImmersion_of_surjective φ
  have : IsIso (f.fiberι s) := by unfold Scheme.Hom.fiberι; infer_instance
  have : IsIso (Spec.preimage φ) := by
    have : IsIso (Scheme.Spec.map (Spec.preimage φ).op) := by
      change IsIso (Spec.map (Spec.preimage φ))
      rw [Spec.map_preimage]
      infer_instance
    have := isIso_of_reflects_iso (Spec.preimage φ).op Scheme.Spec
    exact isIso_of_op _
  have hfac : f.fiberι s ≫ f = f.fiberToSpecResidueField s ≫ Spec.map (Spec.preimage φ) := by
    rw [Spec.map_preimage]
    exact pullback.condition
  let : X.Over (Spec (.of K)) := ⟨f⟩
  let : (f.fiber s).Over (Spec (.of K)) :=
    ⟨f.fiberToSpecResidueField s ≫ Spec.map (Spec.preimage φ)⟩
  have : (inv (f.fiberι s)).IsOver (Spec (.of K)) := ⟨by
    change inv _ ≫ (_ ≫ _) = f
    rw [← hfac, IsIso.inv_hom_id_assoc]⟩
  -- change the base field from `κ(s)` to `K`, then transport along `f.fiberι s`
  refine (finrankH_eq_of_comp_specMap (k := K) (L := (Spec (.of K)).residueField s)
    (Spec.preimage φ) (f.fiberToSpecResidueField s) _ q).symm.trans ?_
  rw [← finrankH_pushforward_of_isAffineHom K (inv (f.fiberι s)) ℱ q]
  exact finrankH_congr K ((pullbackIsoPushforwardInv (f.fiberι s)).app ℱ) q

/-- **The fibre Euler characteristic over a field** is the Euler characteristic, in the
situation of `AlgebraicGeometry.Scheme.Modules.hFiber_eq_finrankH`. -/
theorem eulerCharFiber_eq_eulerChar {K : Type u} [Field K] (f : X ⟶ Spec (.of K))
    (ℱ : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (s : Spec (.of K)) :
    ℱ.eulerCharFiber f s = letI : X.Over (Spec (.of K)) := ⟨f⟩; ℱ.eulerChar K := by
  simp only [eulerCharFiber, eulerChar, hFiber_eq_finrankH f ℱ _ s]

@[simp]
theorem mem_perfectLocus (ℱ : X.Modules) (f : X ⟶ T) (i : ℕ) (t : T) :
    t ∈ ℱ.perfectLocus f i ↔ ∀ q ≠ i, ℱ.hFiber f q t = 0 :=
  Iff.rfl

@[simp]
theorem mem_perfectLocusOfRank (ℱ : X.Modules) (f : X ⟶ T) (i r : ℕ) (t : T) :
    t ∈ ℱ.perfectLocusOfRank f i r ↔ t ∈ ℱ.perfectLocus f i ∧ ℱ.hFiber f i t = r :=
  Iff.rfl

theorem perfectLocusOfRank_subset (ℱ : X.Modules) (f : X ⟶ T) (i r : ℕ) :
    ℱ.perfectLocusOfRank f i r ⊆ ℱ.perfectLocus f i :=
  fun _ ht ↦ ht.1

variable (f : X ⟶ T) (ℱ : X.Modules)

/-- **The sections of the higher direct images over an affine base, naturally.** Over an affine
base, for `f` quasi-compact and separated, the global sections of `R^q f_* ℱ` are the sheaf
cohomology `H^q(X, ℱ)`, by additive isomorphisms natural in the quasi-coherent module `ℱ`.

This is the comparison between the right derived functors of `f_*` inside `X.Modules` and the
`Ext`-groups in abelian sheaves of `AlgebraicGeometry.Scheme.Modules.H`. It holds because
injective `𝒪_X`-modules are flasque, the pushforward of a flasque module is flasque, flasque
sheaves are acyclic for `H`, and, `T` being affine and `R^p f_* ℱ` quasi-coherent, the global
sections functor of `T` is exact on them [Stacks, Tags 01XJ and 0BDY]. -/
theorem exists_addEquiv_sections_higherDirectImage_H [IsAffine T] [QuasiCompact f]
    [IsSeparated f] [HasInjectiveResolutions X.Modules] (q : ℕ) :
    ∃ e : ∀ (ℱ : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ],
        Γ((higherDirectImage f q).obj ℱ, ⊤) ≃+ ℱ.H q,
      ∀ (ℱ 𝒢 : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
        [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) 𝒢] (φ : ℱ ⟶ 𝒢)
        (x : Γ((higherDirectImage f q).obj ℱ, ⊤)),
        e 𝒢 (((higherDirectImage f q).map φ).app ⊤ x) = H.map φ q (e ℱ x) :=
  sorry

/-- **The sections of the higher direct images over an affine base, linearly.** Over an affine
base the global sections of the `q`-th higher direct image are the sheaf cohomology of `ℱ`,
`Γ(T, R^q f_* ℱ) ≅ H^q(X, ℱ)`, by an isomorphism which is linear along `f^♯ : Γ(T, ⊤) → Γ(X, ⊤)`.

This is the comparison between the two cohomology theories used in the Picard-framework block:
the right derived functors of `f_*` inside `X.Modules` on the one hand, and the `Ext`-groups in
abelian sheaves of `AlgebraicGeometry.Scheme.Modules.H` on the other. The additive comparison
is `AlgebraicGeometry.Scheme.Modules.exists_addEquiv_sections_higherDirectImage_H`; being natural
in `ℱ`, it is compatible with multiplication by global functions of `T`, which `R^q f_*` turns
into multiplication by their images in `Γ(X, ⊤)`
(`AlgebraicGeometry.Scheme.Modules.higherDirectImage_map_smulHom`).

Over `T = Spec κ` for a field `κ`, this is the identification of the `q`-th direct image to a
point with `H^q` as `κ`-vector spaces, used in the local model of the proof of
`thm-pc-semicontinuity-base-change`. -/
theorem exists_bijective_semilinearMap_sections_higherDirectImage_H [IsAffine T] [QuasiCompact f]
    [IsSeparated f] [HasInjectiveResolutions X.Modules]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    ∃ e : Γ((higherDirectImage f q).obj ℱ, ⊤) →ₛₗ[f.appTop.hom] ℱ.H q, Function.Bijective e := by
  obtain ⟨e, he⟩ := exists_addEquiv_sections_higherDirectImage_H f q
  refine ⟨{ toFun := e ℱ, map_add' := map_add _, map_smul' := fun a x ↦ ?_ }, (e ℱ).bijective⟩
  have h : a • x = ((higherDirectImage f q).map (ℱ.smulHom (f.appTop a))).app ⊤ x := by
    rw [higherDirectImage_map_smulHom, smulHom_app_apply]
    congr 1
    exact (congrArg (fun φ ↦ φ a) (T.presheaf.map_id _)).symm
  rw [h, he]
  rfl

/-- Over an affine base the global sections of the `q`-th higher direct image are the sheaf
cohomology of `ℱ`: `Γ(T, R^q f_* ℱ) ≅ H^q(X, ℱ)`. See
`AlgebraicGeometry.Scheme.Modules.exists_bijective_semilinearMap_sections_higherDirectImage_H`
for the linearity of this isomorphism. -/
theorem nonempty_sections_higherDirectImage_iso_H [IsAffine T] [QuasiCompact f] [IsSeparated f]
    [HasInjectiveResolutions X.Modules]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    Nonempty (Γ((higherDirectImage f q).obj ℱ, ⊤) ≃+ ℱ.H q) :=
  have ⟨e, he⟩ := exists_bijective_semilinearMap_sections_higherDirectImage_H f ℱ q
  ⟨AddEquiv.ofBijective e.toAddMonoidHom he⟩

/-- **The fibre dimension is the dimension of the direct image to the point.** For `f`
quasi-compact and separated, `h^q(t) = dim_{κ(t)} H^q(X_t, ℱ_t)` is the dimension of the global
sections of `R^q (f_t)_* ℱ_t` for the fibre `f_t : X_t ⟶ Spec κ(t)`, as a vector space over the
field `Γ(Spec κ(t), ⊤) ≅ κ(t)`. -/
theorem hFiber_eq_finrank_sections_higherDirectImage [QuasiCompact f] [IsSeparated f] (t : T)
    [HasInjectiveResolutions (f.fiber t).Modules]
    [SheafOfModules.IsQuasicoherent (R := (f.fiber t).ringCatSheaf)
      ((Modules.pullback (f.fiberι t)).obj ℱ)] (q : ℕ) :
    ℱ.hFiber f q t = Module.finrank Γ(Spec (T.residueField t), ⊤)
      Γ((higherDirectImage (f.fiberToSpecResidueField t) q).obj
        ((Modules.pullback (f.fiberι t)).obj ℱ), ⊤) := by
  have : IsSeparated (f.fiberToSpecResidueField t) := by
    unfold Scheme.Hom.fiberToSpecResidueField
    infer_instance
  have : QuasiCompact (f.fiberToSpecResidueField t) := by
    unfold Scheme.Hom.fiberToSpecResidueField
    infer_instance
  obtain ⟨e, he⟩ := exists_bijective_semilinearMap_sections_higherDirectImage_H
    (f.fiberToSpecResidueField t) ((Modules.pullback (f.fiberι t)).obj ℱ) q
  let j := (AddEquiv.ofBijective e.toAddMonoidHom he).symm
  let := f.fiberOverSpecResidueField t
  refine congrArg Cardinal.toNat (rank_eq_of_equiv_equiv _ j
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (T.residueField t)).inv) ?_)
  intro c h
  obtain ⟨y, rfl⟩ := he.2 h
  have hc : c • e y = e ((Scheme.ΓSpecIso (T.residueField t)).inv c • y) := by
    rw [smul_H_eq_globalSectionsRingHom_smul, e.map_smulₛₗ]
    rfl
  have hj (z) : j (e z) = z := (AddEquiv.ofBijective e.toAddMonoidHom he).symm_apply_apply z
  rw [hc, hj, hj]

/-- **The direct images to the spectrum of a field.** For a scheme `X` over a field `K`, with
structure morphism quasi-compact and separated, and a quasi-coherent `𝒪_X`-module `ℱ`, the
global sections of `R^q f_* ℱ` are `H^q(X, ℱ)` as `K`-vector spaces. This is
`AlgebraicGeometry.Scheme.Modules.exists_bijective_semilinearMap_sections_higherDirectImage_H`
over `Spec K`, where `K` acts on both sides through `Γ(Spec K, ⊤)`. -/
theorem nonempty_moduleSpecΓFunctor_obj_higherDirectImage_linearEquiv_H (K : Type u) [Field K]
    [X.Over (Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))] [IsSeparated (X ↘ Spec (.of K))]
    [HasInjectiveResolutions X.Modules]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    Nonempty ((moduleSpecΓFunctor (R := .of K)).obj
      ((higherDirectImage (X ↘ Spec (.of K)) q).obj ℱ) ≃ₗ[K] ℱ.H q) := by
  obtain ⟨e, he⟩ := exists_bijective_semilinearMap_sections_higherDirectImage_H
    (X ↘ Spec (.of K)) ℱ q
  let M := (moduleSpecΓFunctor (R := .of K)).obj ((higherDirectImage (X ↘ Spec (.of K)) q).obj ℱ)
  refine ⟨LinearEquiv.ofBijective (M := M)
    { toFun := e, map_add' := e.map_add, map_smul' := fun c x ↦ ?_ } he⟩
  let y : Γ((higherDirectImage (X ↘ Spec (.of K)) q).obj ℱ, ⊤) := x
  have h : (c • x : M) = (Scheme.ΓSpecIso (.of K)).inv c • y := smul_top_eq (R := .of K) _ c y
  exact (congrArg e h).trans ((e.map_smulₛₗ _ y).trans
    (smul_H_eq_globalSectionsRingHom_smul K ℱ q c (e y)).symm)

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

open MonoidalCategory in
/-- **The projection formula** for an invertible module. For `f : X ⟶ T`, an `𝒪_X`-module `ℱ`
and an invertible `𝒪_T`-module `𝒩`, `R^q f_* (ℱ ⊗ f^* 𝒩) ≅ R^q f_* ℱ ⊗ 𝒩` for every `q`: twisting
by an invertible module pulled back from the base commutes with the higher direct images.

The blueprint states the projection formula `Rf_* E ⊗^𝕃 K ≅ Rf_* (E ⊗^𝕃 Lf^* K)` in the derived
category `D_QCoh` for `f` quasi-compact and quasi-separated, and deduces this case `K = 𝒩[0]`.
There is no derived category of `X.Modules` here, so only this case is stated, through the
higher direct images; it holds for every `f` and `ℱ`, as both sides are computed locally on
`T`, where `𝒩 ≅ 𝒪_T`.

(blueprint: `lem-pc-projection-formula`) -/
theorem nonempty_higherDirectImage_tensorObj_pullback_iso (𝒩 : T.Modules) [𝒩.IsInvertible]
    (q : ℕ) :
    Nonempty ((higherDirectImage f q).obj (ℱ ⊗ (Modules.pullback f).obj 𝒩) ≅
      (higherDirectImage f q).obj ℱ ⊗ 𝒩) :=
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

/-- `IsFiniteLocallyFreeInDegree M i r` says that the family `M = (M q)_{q : ℕ}` of `𝒪_X`-modules,
thought of as the cohomology sheaves `H^q(E)` of an object `E` of the derived category of
`𝒪_X`-modules, is that of a **finite locally free module of rank `r` placed in degree `i`**:
`M q = 0` for `q ≠ i`, and `M i` is finite locally free of rank `r`.

For an object `E` represented by a complex this is the same as `E ≅ ℰ[-i]` with `ℰ` finite
locally free of rank `r`: a complex whose cohomology is concentrated in degree `i` is
quasi-isomorphic to its `i`-th cohomology placed in degree `i`. There is no derived category of
`X.Modules` with derived pushforward available, so the condition is stated on the cohomology
sheaves. The case `i = 0`, `r = 1` is an *invertible module placed in degree `0`*
(`isFiniteLocallyFreeInDegree_zero_one_iff`).

(blueprint: `def-pc-invertible-in-degree-zero`) -/
structure IsFiniteLocallyFreeInDegree (M : ℕ → X.Modules) (i r : ℕ) : Prop where
  isZero (q : ℕ) (hq : q ≠ i) : IsZero (M q)
  isFiniteLocallyFreeOfRank : (M i).IsFiniteLocallyFreeOfRank r

/-- A family of modules is that of an invertible module placed in degree `0` if and only if it
vanishes in nonzero degrees and is invertible in degree `0`.

(blueprint: `def-pc-invertible-in-degree-zero`) -/
theorem isFiniteLocallyFreeInDegree_zero_one_iff (M : ℕ → X.Modules) :
    IsFiniteLocallyFreeInDegree M 0 1 ↔
      (∀ q ≠ 0, IsZero (M q)) ∧ SheafOfModules.IsInvertible (R := X.ringCatSheaf) (M 0) :=
  ⟨fun h ↦ ⟨h.isZero, (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one (M 0)).2
      h.isFiniteLocallyFreeOfRank⟩,
    fun h ↦ ⟨h.1, (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one (M 0)).1 h.2⟩⟩

/-- **The perfect locus of a bounded complex of finite free modules.** Let `P` be a bounded complex
of finite free `𝒪_Y`-modules, representing a perfect object `E` of the derived category of `Y`, and
fix `i r : ℕ`. There is an open subscheme `U` of `Y` such that a morphism `g : Y' ⟶ Y` factors
through `U` if and only if `L g^* E = g^* P` is a finite locally free module of rank `r` placed in
degree `i` (`AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeInDegree`).

The pullback `g^* P` computes `L g^* E` because the terms of `P` are free. The proof splits
contractible summands off `P` over the local rings of `Y`, until every differential has entries in
the maximal ideal; the remaining complex is then `𝒪^r[-i]` near every point whose derived fibre has
cohomology `κ(y)^r` concentrated in degree `i`, and `U` is the set of such points. The converse
direction uses that extension of fields is faithfully flat.

(blueprint: `lem-pc-perfect-locus`) -/
theorem IsFiniteFreeComplex.exists_opens_range_subset_iff {Y : Scheme.{u}}
    {P : CochainComplex Y.Modules ℤ} {d : ℕ} (hP : IsFiniteFreeComplex P d) (i r : ℕ) :
    ∃ U : Y.Opens, ∀ {Y' : Scheme.{u}} (g : Y' ⟶ Y), Set.range g.base ⊆ U ↔
      IsFiniteLocallyFreeInDegree
        (fun q : ℕ ↦ (((Modules.pullback g).mapHomologicalComplex _).obj P).homology q) i r :=
  sorry

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

/-- **Finiteness of the cohomology of a proper morphism over a Noetherian affine base.** With
`f : X ⟶ T` proper, `T` affine with Noetherian ring of global sections `Γ(T, ⊤)` and `ℱ` a coherent
`𝒪_X`-module, the global sections `Γ(T, R^q f_* ℱ) = H^q(X, ℱ)` of the higher direct image form a
finite `Γ(T, ⊤)`-module for every `q` [Stacks, Tag 02O6], [EGA III₁, 3.2.1].

This is the affine clause of the blueprint lemma `lem-pc-coherent-hi`; for a general proper `f`
the blueprint discharges it by the cited classical input (Chow's lemma and the projective case,
Stacks 02O5/02O6). It is the only input to
`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage` beyond the formal
properties of the higher direct images.

(blueprint: `lem-pc-coherent-hi`) -/
theorem finite_sections_higherDirectImage [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    Module.Finite Γ(T, ⊤) Γ((higherDirectImage f q).obj ℱ, ⊤) :=
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
    ((higherDirectImage f q).obj ℱ).IsFinitePresentation := by
  have hP (V : T.Opens) (hV : IsAffineOpen V) :
      ∃ P : (((higherDirectImage f q).obj ℱ).restrict hV.fromSpec).Presentation, P.IsFinite := by
    have := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    have : IsNoetherianRing Γ(Spec Γ(T, V), ⊤) :=
      isNoetherianRing_of_ringEquiv _ (Scheme.ΓSpecIso Γ(T, V)).commRingCatIsoToRingEquiv.symm
    have := isGrothendieckAbelian (Limits.pullback f hV.fromSpec)
    obtain ⟨e⟩ := nonempty_higherDirectImage_iso_restrict f ℱ hV.fromSpec _ _
      (IsPullback.of_hasPullback f hV.fromSpec) q
    have : ((Modules.pullback (pullback.fst f hV.fromSpec)).obj ℱ).IsFinitePresentation :=
      (SheafOfModules.isFinitePresentation (Limits.pullback f hV.fromSpec).ringCatSheaf).prop_of_iso
        ((restrictFunctorIsoPullback _).app ℱ) (isFinitePresentation_restrictFunctor _ ℱ)
    have : ((Modules.pullback (pullback.fst f hV.fromSpec)).obj ℱ).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent (Limits.pullback f hV.fromSpec).ringCatSheaf).prop_of_iso
        ((restrictFunctorIsoPullback _).app ℱ) (isQuasicoherent_restrictFunctor _ ℱ)
    have := finite_sections_higherDirectImage (pullback.snd f hV.fromSpec)
      ((Modules.pullback (pullback.fst f hV.fromSpec)).obj ℱ) q
    let φ : Γ((higherDirectImage (pullback.snd f hV.fromSpec) q).obj
        ((Modules.pullback (pullback.fst f hV.fromSpec)).obj ℱ), ⊤) →ₗ[Γ(Spec Γ(T, V), ⊤)]
        Γ(((higherDirectImage f q).obj ℱ).restrict hV.fromSpec, ⊤) :=
      { toFun := e.hom.app ⊤, map_add' := map_add _, map_smul' := Hom.app_smul e.hom }
    have : Module.Finite Γ(Spec Γ(T, V), ⊤)
        Γ(((higherDirectImage f q).obj ℱ).restrict hV.fromSpec, ⊤) :=
      Module.Finite.of_surjective φ (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).2
    have := finite_sections_top_of_finite
      (((higherDirectImage f q).obj ℱ).restrict hV.fromSpec)
    have := isQuasicoherent_higherDirectImage f ℱ q
    exact exists_presentation_isFinite _
  have (V : T.affineOpens) : IsOpenImmersion (IsAffineOpen.fromSpec (U := V.1) V.2) :=
    IsAffineOpen.isOpenImmersion_fromSpec V.2
  choose P _ using fun V : T.affineOpens ↦ hP V.1 V.2
  refine isFinitePresentation_of_iSup_opensRange_eq_top _ _ ?_ P
  exact (iSup_congr fun V ↦ IsAffineOpen.opensRange_fromSpec V.2).trans
    (iSup_affineOpens_eq_top T)

omit [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
  [HasInjectiveResolutions X.Modules] [ℱ.IsFinitePresentation] in
/-- A point `s` of an open `U` of `T` lifts to a morphism `Spec κ(s) ⟶ U`. -/
lemma exists_comp_ι_eq_fromSpecResidueField {U : T.Opens} {s : T} (hs : s ∈ U) :
    ∃ g : Spec (T.residueField s) ⟶ U.toScheme, g ≫ U.ι = T.fromSpecResidueField s := by
  have hrange : Set.range (T.fromSpecResidueField s).base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι, Scheme.range_fromSpecResidueField]
    simpa using hs
  exact ⟨IsOpenImmersion.lift U.ι (T.fromSpecResidueField s) hrange,
    IsOpenImmersion.lift_fac _ _ _⟩

omit [LocallyOfFinitePresentation f] [HasInjectiveResolutions X.Modules] in
/-- At a point `s` of an open `U` of the base over which `R f_* ℱ` is computed by a complex `P`
compatibly with base change, the fibre dimension `h^q(s)` is the dimension of the cohomology of
the fibre `P ⊗ κ(s)` of `P`. -/
theorem hFiber_eq_finrank_homology {U : T.Opens} {P : CochainComplex U.toScheme.Modules ℤ}
    (hbc : ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ)))
    {s : T} (g : Spec (T.residueField s) ⟶ U.toScheme) (hg : g ≫ U.ι = T.fromSpecResidueField s)
    (q : ℕ) :
    ℱ.hFiber f q s =
      Module.finrank (T.residueField s) ((moduleSpecΓFunctor (R := T.residueField s)).obj
        ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q)) := by
  have := isGrothendieckAbelian (f.fiber s)
  have sq : IsPullback (f.fiberι s) (f.fiberToSpecResidueField s) f (g ≫ U.ι) := by
    rw [hg]
    exact IsPullback.of_hasPullback _ _
  obtain ⟨e⟩ := hbc g _ _ sq q
  rw [hFiber_eq_finrank_sections_higherDirectImage f ℱ s q,
    ← (appLinearEquivOfIso e ⊤).finrank_eq]
  have h := finrank_eq_of_coe_eq
    ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q) ⊤ ⊤ rfl
  rw [finrank_top, finrank_top] at h
  exact h.symm

/-- **Semicontinuity of the fibre dimension.** With `f : X ⟶ T` proper of finite presentation
and `ℱ` an `𝒪_X`-module of finite presentation which is flat over `T`, the fibre dimension
`t ↦ dim_{κ(t)} H^q(X_t, ℱ_t)` is upper semicontinuous on `T`.

Locally on `T` the fibre dimension is `dim_{κ(t)} H^q(P ⊗ κ(t))` for the bounded complex `P` of
finite free modules of
`AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage`: the pullback of
`P` to `Spec κ(t)` computes the higher direct images of the fibre `ℱ_t` to the point, whose global
sections are `H^q(X_t, ℱ_t)`
(`AlgebraicGeometry.Scheme.Modules.hFiber_eq_finrank_sections_higherDirectImage`). The dimension
of the cohomology of a complex of finite free modules is upper semicontinuous in the point, by the
lower semicontinuity of the ranks of its differentials
(`AlgebraicGeometry.Scheme.Modules.exists_finrank_homology_pullback_le`).

(blueprint: `sk-thm-picard-semicon`, `thm-pc-semicontinuity-base-change`) -/
theorem upperSemicontinuous_hFiber (hℱ : ℱ.IsFlatOver f) (q : ℕ) :
    UpperSemicontinuous (ℱ.hFiber f q) := by
  intro t m hm
  obtain ⟨U, P, d, htU, hP, hbc⟩ := exists_isFiniteFreeComplex_higherDirectImage f ℱ hℱ t
  -- at a point `s ∈ U`, the fibre dimension is the dimension of `H^q(P ⊗ κ(s))`
  have key (s : T) (hs : s ∈ U) : ∃ g : Spec (T.residueField s) ⟶ U.toScheme,
      g ≫ U.ι = T.fromSpecResidueField s ∧ ℱ.hFiber f q s =
        Module.finrank (T.residueField s) ((moduleSpecΓFunctor (R := T.residueField s)).obj
          ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q)) :=
    have ⟨g, hg⟩ := exists_comp_ι_eq_fromSpecResidueField hs
    ⟨g, hg, hFiber_eq_finrank_homology f ℱ hbc g hg q⟩
  obtain ⟨g, hg, hgt⟩ := key t htU
  obtain ⟨V, hV, hle⟩ := exists_finrank_homology_pullback_le hP.exists_iso_free q
    (Field.toIsField _) g
  have hmem (s : T) (g' : Spec (T.residueField s) ⟶ U.toScheme)
      (hg' : g' ≫ U.ι = T.fromSpecResidueField s) (v : U.toScheme) (hv : U.ι.base v = s) :
      Set.range g'.base ⊆ {v} := by
    rintro _ ⟨x, rfl⟩
    refine U.ι.isOpenEmbedding.injective ?_
    rw [← Scheme.Hom.comp_apply, hg', hv]
    exact (Scheme.range_fromSpecResidueField s).subset ⟨x, rfl⟩
  have : Nonempty (Spec (T.residueField t)) := inferInstance
  obtain ⟨x⟩ := this
  refine Filter.mem_of_superset ((U.ι ''ᵁ V).isOpen.mem_nhds ⟨g.base x, hV ⟨x, rfl⟩, ?_⟩) ?_
  · have := (Scheme.range_fromSpecResidueField t).subset ⟨x, rfl⟩
    rw [← hg] at this
    exact this
  · rintro _ ⟨v, hv, rfl⟩
    have hvU : U.ι.base v ∈ U := by
      rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]
      exact ⟨v, rfl⟩
    obtain ⟨g', hg', hgs⟩ := key _ hvU
    change ℱ.hFiber f q (U.ι.base v) < m
    rw [hgs]
    refine (hle (Field.toIsField _) g' ((hmem _ g' hg' v rfl).trans ?_)).trans_lt (hgt ▸ hm)
    simpa using hv

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

/-- **The fibre cohomology vanishes in large degrees, locally on the base.** In the situation of
`AlgebraicGeometry.Scheme.Modules.upperSemicontinuous_hFiber`, every point `t` of `T` has an open
neighbourhood `U` and a bound `d` with `H^q(X_{t'}, ℱ_{t'}) = 0` for all `t' ∈ U` and all `q > d`.

Take for `U` and `d` the neighbourhood and the length of the bounded complex `P` of finite free
modules of `AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage`. For
`t' ∈ U` its pullback to `Spec κ(t')` computes the higher direct images of `ℱ_{t'}` along
`X_{t'} ⟶ Spec κ(t')`, whose global sections are `H^q(X_{t'}, ℱ_{t'})`; it vanishes in degrees
`q > d`.

(blueprint: `lem-pc-flat-rf-open`) -/
theorem exists_forall_hFiber_eq_zero (hℱ : ℱ.IsFlatOver f) (t : T) :
    ∃ (U : T.Opens) (d : ℕ), t ∈ U ∧ ∀ t' ∈ U, ∀ q, d < q → ℱ.hFiber f q t' = 0 := by
  obtain ⟨U, P, d, htU, hP, hbc⟩ := exists_isFiniteFreeComplex_higherDirectImage f ℱ hℱ t
  refine ⟨U, d, htU, fun t' ht' q hq ↦ ?_⟩
  have hrange : Set.range (T.fromSpecResidueField t').base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι, Scheme.range_fromSpecResidueField]
    simpa using ht'
  let g := IsOpenImmersion.lift U.ι (T.fromSpecResidueField t') hrange
  have hg : g ≫ U.ι = T.fromSpecResidueField t' := IsOpenImmersion.lift_fac _ _ _
  have := isGrothendieckAbelian (f.fiber t')
  have sq : IsPullback (f.fiberι t') (f.fiberToSpecResidueField t') f (g ≫ U.ι) := by
    rw [hg]
    exact IsPullback.of_hasPullback _ _
  obtain ⟨e⟩ := hbc g _ _ sq q
  -- the pulled back complex vanishes in degree `q > d`, hence so does its cohomology
  have hX : IsZero (((Modules.pullback g).mapHomologicalComplex _).obj P |>.X q) :=
    (Modules.pullback g).map_isZero (by have := hP.isStrictlyLE; exact P.isZero_of_isStrictlyLE d q)
  have hR : IsZero ((higherDirectImage (f.fiberToSpecResidueField t') q).obj
      ((Modules.pullback (f.fiberι t')).obj ℱ)) :=
    (ShortComplex.isZero_homology_of_isZero_X₂ _ hX).of_iso e.symm
  have : IsSeparated (f.fiberToSpecResidueField t') := by
    unfold Scheme.Hom.fiberToSpecResidueField
    infer_instance
  have : QuasiCompact (f.fiberToSpecResidueField t') := by
    unfold Scheme.Hom.fiberToSpecResidueField
    infer_instance
  obtain ⟨φ⟩ := nonempty_sections_higherDirectImage_iso_H (f.fiberToSpecResidueField t')
    ((Modules.pullback (f.fiberι t')).obj ℱ) q
  have : Subsingleton (((Modules.pullback (f.fiberι t')).obj ℱ).H q) :=
    have : Subsingleton Γ((higherDirectImage (f.fiberToSpecResidueField t') q).obj
        ((Modules.pullback (f.fiberι t')).obj ℱ), ⊤) :=
      ModuleCat.subsingleton_of_isZero
        ((SheafOfModules.evaluation _ (Opposite.op ⊤)).map_isZero hR)
    φ.symm.injective.subsingleton
  let := f.fiberOverSpecResidueField t'
  exact Module.finrank_zero_of_subsingleton

/-- **Openness of the bounded perfect locus.** With `f : X ⟶ T` proper of finite presentation and
`ℱ` an `𝒪_X`-module of finite presentation which is flat over `T`, the locus `U_{i,≤r}` of points
`t` of the perfect locus `U_i` at which `H^i(X_t, ℱ_t)` has dimension at most `r` is open in `T`.

Near a point `t`, the fibre cohomology vanishes in degrees `q > d`
(`AlgebraicGeometry.Scheme.Modules.exists_forall_hFiber_eq_zero`), so there `U_{i,≤r}` is cut out
by the finitely many conditions `h^q < 1` for `q ≤ d`, `q ≠ i`, and `h^i < r + 1`, each of which is
open by upper semicontinuity (`AlgebraicGeometry.Scheme.Modules.upperSemicontinuous_hFiber`).

(blueprint: `sk-thm-picard-perfect`) -/
theorem isOpen_setOf_hFiber_le (hℱ : ℱ.IsFlatOver f) (i r : ℕ) :
    IsOpen {t ∈ ℱ.perfectLocus f i | ℱ.hFiber f i t ≤ r} := by
  have hopen (q n : ℕ) : IsOpen {t | ℱ.hFiber f q t < n} :=
    (upperSemicontinuous_hFiber f ℱ hℱ q).isOpen_preimage n
  rw [isOpen_iff_forall_mem_open]
  rintro t ⟨ht, hti⟩
  obtain ⟨U, d, htU, hU⟩ := exists_forall_hFiber_eq_zero f ℱ hℱ t
  refine ⟨U ∩ (⋂ q ∈ Set.Iic d, {t' | q ≠ i → ℱ.hFiber f q t' < 1}) ∩
    {t' | ℱ.hFiber f i t' < r + 1}, ?_, ?_, ?_⟩
  · rintro t' ⟨⟨ht'U, hq⟩, hi⟩
    refine ⟨fun q hqi ↦ ?_, Nat.lt_succ_iff.mp hi⟩
    rcases le_or_gt q d with hqd | hqd
    · exact Nat.lt_one_iff.mp (Set.mem_iInter₂.mp hq q hqd hqi)
    · exact hU t' ht'U q hqd
  · refine (U.isOpen.inter ((Set.finite_Iic d).isOpen_biInter fun q _ ↦ ?_)).inter (hopen i _)
    by_cases hqi : q = i
    · simp [hqi]
    · simpa [hqi] using hopen q 1
  · exact ⟨⟨htU, Set.mem_iInter₂.mpr fun q _ hqi ↦ by simp [ht q hqi]⟩, Nat.lt_succ_of_le hti⟩

/-- **Openness of the perfect locus.** The perfect locus `U_i` is open in `T`, being the union
over `r` of the open loci `U_{i,≤r}` of
`AlgebraicGeometry.Scheme.Modules.isOpen_setOf_hFiber_le`. -/
theorem isOpen_perfectLocus (hℱ : ℱ.IsFlatOver f) (i : ℕ) : IsOpen (ℱ.perfectLocus f i) := by
  convert isOpen_iUnion fun r ↦ isOpen_setOf_hFiber_le f ℱ hℱ i r
  ext t
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  exact ⟨fun ht ↦ ⟨_, ht, le_rfl⟩, fun ⟨_, ht, _⟩ ↦ ht⟩

omit [LocallyOfFinitePresentation f] [HasInjectiveResolutions X.Modules] in
/-- **The fibre dimension is invariant under base change.** Let `f' : X' ⟶ T'` and `g' : X' ⟶ X`
be the base change of `f` along `g : T' ⟶ T`, in the cartesian square `sq`
```
X' --g'--> X
|          |
f'         f
v          v
T' --g---> T
```
and let `ℱ'` be the pullback of `ℱ` to `X'`. Then `h^q_{ℱ'}(t') = h^q_ℱ(g t')` for every point
`t'` of `T'`: the fibre `X'_{t'}` is the base change of `X_{g t'}` along the field extension
`κ(g t') ⟶ κ(t')`, and cohomology commutes with flat base change.

(blueprint: `sk-thm-picard-perfect`) -/
theorem hFiber_pullback_of_isPullback {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X)
    (f' : X' ⟶ T') (sq : IsPullback g' f' f g) (q : ℕ) (t' : T') :
    ((Modules.pullback g').obj ℱ).hFiber f' q t' = ℱ.hFiber f q (g.base t') := by
  let K := T.residueField (g.base t')
  let L := T'.residueField t'
  let : Algebra K L := (g.residueFieldMap t').hom.toAlgebra
  have hsq := isPullback_fiberToSpecResidueField_of_isPullback sq t'
  let := f.fiberOverSpecResidueField (g.base t')
  let := f'.fiberOverSpecResidueField t'
  have : QuasiCompact (f.fiber (g.base t') ↘ Spec (.of K)) := by
    change QuasiCompact (f.fiberToSpecResidueField _)
    unfold Scheme.Hom.fiberToSpecResidueField
    infer_instance
  have : QuasiSeparated (f.fiber (g.base t') ↘ Spec (.of K)) := by
    change QuasiSeparated (f.fiberToSpecResidueField _)
    unfold Scheme.Hom.fiberToSpecResidueField
    infer_instance
  have h := Modules.finrankH_pullback (k := K) L ((Modules.pullback (f.fiberι (g.base t'))).obj ℱ) q
  let φ := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have hsq' : IsPullback (pullback.map f' (T'.fromSpecResidueField t') f
      (T.fromSpecResidueField (g.base t')) g' (Spec.map (g.residueFieldMap t')) g
      (by simp [sq.w]) (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g t').symm)
      (f'.fiberToSpecResidueField t') (f.fiber (g.base t') ↘ Spec (.of K)) φ := hsq
  let e : f'.fiber t' ≅ Limits.pullback (f.fiber (g.base t') ↘ Spec (.of K)) φ :=
    hsq'.isoPullback
  have : e.hom.IsOver (Spec (.of L)) := by
    rw [Scheme.Hom.isOver_iff]
    exact hsq'.isoPullback_hom_snd
  have hcomp : f'.fiberι t' ≫ g' =
      e.hom ≫ pullback.fst _ _ ≫ f.fiberι (g.base t') := by
    rw [← Category.assoc, hsq'.isoPullback_hom_fst]
    simp [Scheme.Hom.fiberι]
  change ((Modules.pullback (f'.fiberι t')).obj ((Modules.pullback g').obj ℱ)).finrankH L q =
    ((Modules.pullback (f.fiberι (g.base t'))).obj ℱ).finrankH K q
  rw [← h, ← finrankH_pullback_of_isIso (k := L) e.hom]
  exact finrankH_congr _ ((pullbackComp _ _).app ℱ ≪≫ (pullbackCongr hcomp).app ℱ ≪≫
    ((pullbackComp _ _).app ℱ).symm ≪≫ (Modules.pullback e.hom).mapIso
      ((pullbackComp _ _).app ℱ).symm) q

omit [LocallyOfFinitePresentation f] [HasInjectiveResolutions X.Modules] in
/-- **The fibre Euler characteristic is invariant under base change**, in the situation of
`AlgebraicGeometry.Scheme.Modules.hFiber_pullback_of_isPullback`. -/
theorem eulerCharFiber_pullback_of_isPullback {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X)
    (f' : X' ⟶ T') (sq : IsPullback g' f' f g) (t' : T') :
    ((Modules.pullback g').obj ℱ).eulerCharFiber f' t' = ℱ.eulerCharFiber f (g.base t') := by
  simp only [eulerCharFiber, hFiber_pullback_of_isPullback f ℱ g g' f' sq]

/-- **The fibre Euler characteristic is locally constant.** With `f : X ⟶ T` proper of finite
presentation and `ℱ` an `𝒪_X`-module of finite presentation which is flat over `T`, the Euler
characteristic `t ↦ Σ_q (-1)^q dim_{κ(t)} H^q(X_t, ℱ_t)` of the fibres is locally constant on
`T`.

Near a point of `T` it is the alternating sum of the ranks of the bounded complex `P` of finite
free modules of `AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage`,
since the Euler characteristic of a bounded complex of finite-dimensional vector spaces is that
of its cohomology.

(blueprint: `sk-thm-picard-perfect`) -/
theorem isLocallyConstant_eulerCharFiber (hℱ : ℱ.IsFlatOver f) :
    IsLocallyConstant (ℱ.eulerCharFiber f) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro t
  obtain ⟨U, P, d, htU, hP, hbc⟩ := exists_isFiniteFreeComplex_higherDirectImage f ℱ hℱ t
  choose r e using hP.exists_iso_free
  let e' n := (e n).some
  suffices h : ∀ s ∈ U, ℱ.eulerCharFiber f s =
      ∑ q ∈ Finset.range (d + 1), (-1) ^ q * (r q : ℤ) by
    filter_upwards [U.isOpen.mem_nhds htU] with s hs
    rw [h s hs, h t htU]
  intro s hs
  -- the fibre dimension in each degree, through the fibre `P ⊗ κ(s)`
  obtain ⟨g, hg⟩ := exists_comp_ι_eq_fromSpecResidueField hs
  have hh := hFiber_eq_finrank_homology f ℱ hbc g hg
  have hκ : IsField (T.residueField s) := Field.toIsField _
  have hf := finrank_homology_pullback_add_rank_add_rank e' hκ g
  let a : ℤ → ℕ := fun n ↦
    ((freeMatrix ((e' n).inv ≫ P.d n (n + 1) ≫ (e' (n + 1)).hom)).map g.appTop).rank
  have ha (n m : ℤ) (h : n + 1 = m) : a n =
      ((freeMatrix ((e' n).inv ≫ P.d n m ≫ (e' m).hom)).map g.appTop).rank := by
    subst h
    rfl
  have hq (q : ℕ) : (ℱ.hFiber f q s : ℤ) = r q - a q - a (q - 1) := by
    have := hf q
    rw [← ha (q - 1) q (by omega)] at this
    change _ + a q + _ = _ at this
    rw [hh q]
    omega
  have hzero (n : ℤ) (hn : IsZero (P.X n) ∨ IsZero (P.X (n + 1))) : a n = 0 := by
    have : P.d n (n + 1) = 0 := hn.elim (fun h ↦ h.eq_of_src _ _) (fun h ↦ h.eq_of_tgt _ _)
    simp [a, this, freeMatrix_zero]
  have hP₀ := hP.isStrictlyGE
  have hP₁ := hP.isStrictlyLE
  have ha₀ : a (-1) = 0 := hzero _ (.inl (P.isZero_of_isStrictlyGE 0 (-1) (by omega)))
  have ha₁ : a d = 0 := hzero _ (.inr (P.isZero_of_isStrictlyLE d (d + 1) (by omega)))
  have hvan (q : ℕ) (hq : d < q) : ℱ.hFiber f q s = 0 := by
    rw [hh q]
    have hX : IsZero (((Modules.pullback g).mapHomologicalComplex _).obj P |>.X q) :=
      (Modules.pullback g).map_isZero (P.isZero_of_isStrictlyLE d q (by omega))
    have hH : IsZero ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q) :=
      ShortComplex.isZero_homology_of_isZero_X₂ _ hX
    have := ModuleCat.subsingleton_of_isZero
      ((moduleSpecΓFunctor (R := T.residueField s)).map_isZero hH)
    exact Module.finrank_zero_of_subsingleton
  rw [eulerCharFiber, finsum_eq_sum_of_support_subset (s := Finset.range (d + 1))]
  · have := Finset.sum_range_neg_one_pow_mul_add_sub_one (fun n ↦ (a n : ℤ)) d
    simp only [ha₀, ha₁, Nat.cast_zero, mul_zero, zero_add] at this
    rw [← sub_zero (∑ q ∈ Finset.range (d + 1), (-1) ^ q * (r q : ℤ)), ← this,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [hq]
    ring
  · intro q hq
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hq
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hq.2 (by rw [hvan q (by omega)]; simp)

/-- **The fibre dimension is locally constant on the perfect locus.** On the perfect locus `U_i`
the fibre dimension `t ↦ dim_{κ(t)} H^i(X_t, ℱ_t)` is locally constant: there it equals
`(-1)^i` times the fibre Euler characteristic, which is locally constant by
`AlgebraicGeometry.Scheme.Modules.isLocallyConstant_eulerCharFiber`.

(blueprint: `sk-thm-picard-perfect`) -/
theorem isLocallyConstant_hFiber_restrict (hℱ : ℱ.IsFlatOver f) (i : ℕ) :
    IsLocallyConstant ((ℱ.perfectLocus f i).domRestrict (ℱ.hFiber f i)) := by
  have h : (ℱ.perfectLocus f i).domRestrict (ℱ.hFiber f i) =
      (fun n : ℤ ↦ ((-1) ^ i * n).toNat) ∘ ℱ.eulerCharFiber f ∘ Subtype.val := by
    ext ⟨t, ht⟩
    rw [Set.domRestrict_apply, Function.comp_apply, Function.comp_apply, eulerCharFiber,
      finsum_eq_single _ i fun q hq ↦ by simp [ht q hq], ← mul_assoc, ← mul_pow, neg_one_mul,
      neg_neg, one_pow, one_mul, Int.toNat_natCast]
  rw [h]
  exact ((isLocallyConstant_eulerCharFiber f ℱ hℱ).comp_continuous continuous_subtype_val).comp _

/-- **Openness of the rank-`r` perfect locus.** The locus `U_{i,r}` is open in `T`: it is the
preimage of `{r}` under the fibre dimension, which is locally constant on the open set `U_i` by
`AlgebraicGeometry.Scheme.Modules.isLocallyConstant_hFiber_restrict`.

(blueprint: `sk-thm-picard-perfect`) -/
theorem isOpen_perfectLocusOfRank (hℱ : ℱ.IsFlatOver f) (i r : ℕ) :
    IsOpen (ℱ.perfectLocusOfRank f i r) := by
  convert (isOpen_perfectLocus f ℱ hℱ i).isOpenMap_subtype_val _
    ((isLocallyConstant_hFiber_restrict f ℱ hℱ i).isOpen_fiber r)
  ext t
  simp only [mem_perfectLocusOfRank, Set.mem_image, Subtype.exists, exists_and_right,
    exists_eq_right, Set.domRestrict_apply]
  exact ⟨fun ⟨ht, hr⟩ ↦ ⟨ht, hr⟩, fun ⟨ht, hr⟩ ↦ ⟨ht, hr⟩⟩

/-- **Openness of `U_{i,r}`.** The locus of points `t` of `T` at which the fibre cohomology
`H^q(X_t, ℱ_t)` vanishes for all `q ≠ i` and has dimension `r` in degree `i` is open in `T`. This
is `AlgebraicGeometry.Scheme.Modules.isOpen_perfectLocusOfRank`.

(blueprint: `sk-thm-picard-perfect`) -/
theorem isOpen_setOf_hFiber_eq (hℱ : ℱ.IsFlatOver f) (i r : ℕ) :
    IsOpen {t : T | (∀ q ≠ i, ℱ.hFiber f q t = 0) ∧ ℱ.hFiber f i t = r} :=
  isOpen_perfectLocusOfRank f ℱ hℱ i r

omit [LocallyOfFinitePresentation f] [HasInjectiveResolutions X.Modules] in
/-- At a point `s` of an open `U` of the base over which `R f_* ℱ` is computed by a bounded
complex `P` of finite free modules compatibly with base change, the fibre `P ⊗ κ(s)` is a finite
locally free module of rank `r` placed in degree `i` if and only if `s` lies in the rank-`r`
perfect locus `U_{i,r}`. -/
theorem isFiniteLocallyFreeInDegree_homology_pullback_iff {U : T.Opens}
    {P : CochainComplex U.toScheme.Modules ℤ} {d : ℕ} (hP : IsFiniteFreeComplex P d)
    (hbc : ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ)))
    {s : T} (g : Spec (T.residueField s) ⟶ U.toScheme) (hg : g ≫ U.ι = T.fromSpecResidueField s)
    (i r : ℕ) :
    IsFiniteLocallyFreeInDegree
        (fun q : ℕ ↦ (((Modules.pullback g).mapHomologicalComplex _).obj P).homology q) i r ↔
      s ∈ ℱ.perfectLocusOfRank f i r := by
  have hκ : IsField (T.residueField s) := Field.toIsField _
  have (q : ℕ) := finite_moduleSpecΓFunctor_obj_homology_pullback hP.exists_iso_free hκ g q
  simp only [mem_perfectLocusOfRank, mem_perfectLocus, hFiber_eq_finrank_homology f ℱ hbc g hg]
  refine ⟨fun ⟨hz, hl⟩ ↦ ⟨fun q hq ↦ (isZero_iff_finrank_moduleSpecΓFunctor_obj_eq_zero hκ _).1
      (hz q hq), (isFiniteLocallyFreeOfRank_iff_finrank_moduleSpecΓFunctor_obj hκ _ r).1 hl⟩,
    fun ⟨hz, hl⟩ ↦ ⟨fun q hq ↦ (isZero_iff_finrank_moduleSpecΓFunctor_obj_eq_zero hκ _).2
      (hz q hq), (isFiniteLocallyFreeOfRank_iff_finrank_moduleSpecΓFunctor_obj hκ _ r).2 hl⟩⟩

omit [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
  [HasInjectiveResolutions X.Modules] [ℱ.IsFinitePresentation] in
/-- In the situation of `isFiniteLocallyFreeInDegree_homology_pullback_iff`, let `f' : X' ⟶ T'`
be the base change of `f` along `g : T' ⟶ T`, and `V` an open of `T'` which `g` maps into `U`.
Then the restriction of `R^q f'_* ℱ'` to `V` is the cohomology of the pullback of `P` to `V`. -/
theorem nonempty_restrict_higherDirectImage_iso_homology {U : T.Opens}
    {P : CochainComplex U.toScheme.Modules ℤ}
    (hbc : ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ)))
    {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
    [HasInjectiveResolutions X'.Modules] (sq : IsPullback g' f' f g) (V : T'.Opens)
    (gV : V.toScheme ⟶ U.toScheme) (hgV : gV ≫ U.ι = V.ι ≫ g) (q : ℕ) :
    Nonempty (((higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ)).restrict V.ι ≅
      (((Modules.pullback gV).mapHomologicalComplex _).obj P).homology q) := by
  have := isGrothendieckAbelian (f' ⁻¹ᵁ V).toScheme
  have sq' : IsPullback (f' ⁻¹ᵁ V).ι (f' ∣_ V) f' V.ι := (isPullback_morphismRestrict f' V).flip
  obtain ⟨e₁⟩ := nonempty_higherDirectImage_iso_restrict f' ((Modules.pullback g').obj ℱ) V.ι _ _
    sq' q
  have sq'' : IsPullback ((f' ⁻¹ᵁ V).ι ≫ g') (f' ∣_ V) f (gV ≫ U.ι) := by
    rw [hgV]
    exact sq'.paste_horiz sq
  obtain ⟨e₂⟩ := hbc gV _ _ sq'' q
  exact ⟨e₁.symm ≪≫ (higherDirectImage (f' ∣_ V) q).mapIso
    ((Modules.pullbackComp _ _).app ℱ) ≪≫ e₂.symm⟩

/-- **`R f'_* ℱ'` is locally finite locally free in one degree over `U_{i,r}`.** Let `f' : X' ⟶ T'`
be the base change of `f` along `g : T' ⟶ T`, and `t'` a point of `T'` mapped into the rank-`r`
perfect locus `U_{i,r}`. Then `t'` has an open neighbourhood `V` over which `R f'_* ℱ'` is a finite
locally free module of rank `r` placed in degree `i`. -/
theorem exists_mem_isFiniteLocallyFreeInDegree_restrict (hℱ : ℱ.IsFlatOver f) {i r : ℕ}
    {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
    [HasInjectiveResolutions X'.Modules] (sq : IsPullback g' f' f g) (t' : T')
    (ht' : g.base t' ∈ ℱ.perfectLocusOfRank f i r) :
    ∃ V : T'.Opens, t' ∈ V ∧ IsFiniteLocallyFreeInDegree
      (fun q ↦ ((higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ)).restrict V.ι) i r := by
  obtain ⟨U, P, d, hsU, hP, hbc⟩ := exists_isFiniteFreeComplex_higherDirectImage f ℱ hℱ (g.base t')
  obtain ⟨UP, hUP⟩ := hP.exists_opens_range_subset_iff i r
  obtain ⟨gs, hgs⟩ := exists_comp_ι_eq_fromSpecResidueField hsU
  have hs : Set.range gs.base ⊆ UP :=
    (hUP gs).2 ((isFiniteLocallyFreeInDegree_homology_pullback_iff f ℱ hP hbc gs hgs i r).2 ht')
  obtain ⟨x⟩ : Nonempty (Spec (T.residueField (g.base t'))) := inferInstance
  have hx : U.ι.base (gs.base x) = g.base t' := by
    rw [← Scheme.Hom.comp_apply, hgs]
    exact (Scheme.range_fromSpecResidueField (g.base t')).subset ⟨x, rfl⟩
  let V := g ⁻¹ᵁ (U.ι ''ᵁ UP)
  have hV : t' ∈ V := ⟨gs.base x, hs ⟨x, rfl⟩, hx⟩
  have hgV : Set.range (V.ι ≫ g).base ⊆ Set.range U.ι.base := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨u, -, hu⟩ := w.2
    exact ⟨u, by simpa using hu⟩
  let gV := IsOpenImmersion.lift U.ι (V.ι ≫ g) hgV
  have hgV' : gV ≫ U.ι = V.ι ≫ g := IsOpenImmersion.lift_fac _ _ _
  have hrange : Set.range gV.base ⊆ UP := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨u, hu, hu'⟩ := w.2
    have : U.ι.base (gV.base w) = U.ι.base u := by
      rw [← Scheme.Hom.comp_apply, hgV', Scheme.Hom.comp_apply]
      exact hu'.symm
    rwa [U.ι.isOpenEmbedding.injective this]
  have h := (hUP gV).1 hrange
  have e q := (nonempty_restrict_higherDirectImage_iso_homology f ℱ hbc g g' f' sq V gV hgV' q).some
  exact ⟨V, hV, fun q hq ↦ (h.isZero q hq).of_iso (e q),
    have := h.isFiniteLocallyFreeOfRank
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (e i).symm⟩

/-- **Vanishing off degree `i` after base change to the perfect locus.** Let `g : T' ⟶ T` have
image in the perfect locus `U_i`, and let `f' : X' ⟶ T'` and `g' : X' ⟶ X` be the base change of
`f` along `g`, in the cartesian square `sq`
```
X' --g'--> X
|          |
f'         f
v          v
T' --g---> T
```
with `ℱ'` the pullback of `ℱ` to `X'`. Then the higher direct images `R^q f'_* ℱ'` vanish for
`q ≠ i`.

Together with
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_higherDirectImage_of_isPullback`
this is the concrete form of "`R f'_* ℱ'` is perfect of amplitude `[i, i]`", there being no
derived category of `X.Modules` available.

(blueprint: `sk-thm-picard-perfect`) -/
theorem isZero_higherDirectImage_of_isPullback (hℱ : ℱ.IsFlatOver f) {i : ℕ}
    {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
    [HasInjectiveResolutions X'.Modules] (sq : IsPullback g' f' f g)
    (hg : Set.range g.base ⊆ ℱ.perfectLocus f i) {q : ℕ} (hq : q ≠ i) :
    IsZero ((higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ)) := by
  choose V hV h using fun t' ↦ exists_mem_isFiniteLocallyFreeInDegree_restrict f ℱ hℱ g g' f' sq
    t' (r := ℱ.hFiber f i (g.base t')) ⟨hg ⟨t', rfl⟩, rfl⟩
  exact isZero_of_iSup_eq_top _ V (eq_top_iff.2 fun t' _ ↦
    TopologicalSpace.Opens.mem_iSup.2 ⟨t', hV t'⟩) fun t' ↦ (h t').isZero q hq

/-- **The higher direct images vanish off degree `i` over the perfect locus.** Over an open
subscheme `U` of `T` contained in the rank-`r` perfect locus `U_{i,r}`, the higher direct images
`R^q f_* ℱ|_U` vanish for `q ≠ i`. This is the case of the inclusion of `U` in
`AlgebraicGeometry.Scheme.Modules.isZero_higherDirectImage_of_isPullback`.

(blueprint: `sk-thm-picard-perfect`) -/
theorem isZero_higherDirectImage_restrict (hℱ : ℱ.IsFlatOver f) (i r : ℕ) (U : T.Opens)
    (hU : ↑U ⊆ {t : T | (∀ q, q ≠ i → ℱ.hFiber f q t = 0) ∧ ℱ.hFiber f i t = r})
    (q : ℕ) (hq : q ≠ i) :
    IsZero (((higherDirectImage f q).obj ℱ).restrict U.ι) := by
  have := isGrothendieckAbelian (f ⁻¹ᵁ U).toScheme
  have sq : IsPullback (f ⁻¹ᵁ U).ι (f ∣_ U) f U.ι := (isPullback_morphismRestrict f U).flip
  obtain ⟨e⟩ := nonempty_higherDirectImage_iso_restrict f ℱ U.ι _ _ sq q
  refine (isZero_higherDirectImage_of_isPullback f ℱ hℱ U.ι _ _ sq ?_ hq).of_iso e.symm
  rw [Scheme.Opens.range_ι]
  exact fun t ht ↦ (hU ht).1

/-- **Cohomology and base change on the perfect locus.** In the situation of
`AlgebraicGeometry.Scheme.Modules.isZero_higherDirectImage_of_isPullback`, the `i`-th higher
direct image commutes with the base change: `R^i f'_* ℱ' ≅ g^* R^i f_* ℱ`.

Locally on `U_i`, `R f_* ℱ` is a finite locally free module placed in degree `i`, and its
formation commutes with base change.

The isomorphism is only asserted to exist: it is not stated to be the canonical base-change map,
which is not available (see
`AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage`).

(blueprint: `sk-thm-picard-perfect`) -/
theorem nonempty_higherDirectImage_iso_pullback_of_isPullback (hℱ : ℱ.IsFlatOver f) {i : ℕ}
    {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
    [HasInjectiveResolutions X'.Modules] (sq : IsPullback g' f' f g)
    (hg : Set.range g.base ⊆ ℱ.perfectLocus f i) :
    Nonempty ((higherDirectImage f' i).obj ((Modules.pullback g').obj ℱ) ≅
      (Modules.pullback g).obj ((higherDirectImage f i).obj ℱ)) :=
  sorry

/-- **Local freeness in degree `i` after base change to the perfect locus.** In the situation of
`AlgebraicGeometry.Scheme.Modules.isZero_higherDirectImage_of_isPullback`, if the image of `g`
lies in the rank-`r` perfect locus `U_{i,r}`, then the higher direct image `R^i f'_* ℱ'` is
finite locally free of rank `r`.

This also follows from
`AlgebraicGeometry.Scheme.Modules.nonempty_higherDirectImage_iso_pullback_of_isPullback`, the
case of the inclusion of `U_{i,r}`, and the stability of finite local freeness of rank `r`
under pullback, which is not available.

(blueprint: `sk-thm-picard-perfect`) -/
theorem isFiniteLocallyFreeOfRank_higherDirectImage_of_isPullback (hℱ : ℱ.IsFlatOver f)
    {i r : ℕ} {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
    [HasInjectiveResolutions X'.Modules] (sq : IsPullback g' f' f g)
    (hg : Set.range g.base ⊆ ℱ.perfectLocusOfRank f i r) :
    ((higherDirectImage f' i).obj ((Modules.pullback g').obj ℱ)).IsFiniteLocallyFreeOfRank r := by
  choose V hV h using fun t' ↦ exists_mem_isFiniteLocallyFreeInDegree_restrict f ℱ hℱ g g' f' sq
    t' (hg ⟨t', rfl⟩)
  exact isFiniteLocallyFreeOfRank_of_iSup_eq_top _ V (eq_top_iff.2 fun t' _ ↦
    TopologicalSpace.Opens.mem_iSup.2 ⟨t', hV t'⟩) fun t' ↦ (h t').isFiniteLocallyFreeOfRank

/-- **The `i`-th higher direct image is finite locally free over the perfect locus.** Over an
open subscheme `U` of `T` contained in the rank-`r` perfect locus `U_{i,r}`, the higher direct
image `R^i f_* ℱ|_U` is finite locally free of rank `r`. This is the case of the inclusion of
`U` in
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_higherDirectImage_of_isPullback`.

(blueprint: `sk-thm-picard-perfect`) -/
theorem isFiniteLocallyFreeOfRank_higherDirectImage_restrict (hℱ : ℱ.IsFlatOver f) (i r : ℕ)
    (U : T.Opens)
    (hU : ↑U ⊆ {t : T | (∀ q, q ≠ i → ℱ.hFiber f q t = 0) ∧ ℱ.hFiber f i t = r}) :
    (((higherDirectImage f i).obj ℱ).restrict U.ι).IsFiniteLocallyFreeOfRank r := by
  have := isGrothendieckAbelian (f ⁻¹ᵁ U).toScheme
  have sq : IsPullback (f ⁻¹ᵁ U).ι (f ∣_ U) f U.ι := (isPullback_morphismRestrict f U).flip
  obtain ⟨e⟩ := nonempty_higherDirectImage_iso_restrict f ℱ U.ι _ _ sq i
  have := isFiniteLocallyFreeOfRank_higherDirectImage_of_isPullback f ℱ hℱ U.ι _ _ sq
    (by rw [Scheme.Opens.range_ι]; exact hU)
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e

/-- **Base change detects the rank-`r` perfect locus.** Let `f' : X' ⟶ T'` and `g' : X' ⟶ X` be
the base change of `f` along `g : T' ⟶ T`, in the cartesian square `sq`
```
X' --g'--> X
|          |
f'         f
v          v
T' --g---> T
```
with `ℱ'` the pullback of `ℱ` to `X'`. If `R f'_* ℱ'` is a finite locally free module of rank `r`
placed in degree `i`, then the image of `g` lies in the rank-`r` perfect locus `U_{i,r}`.

Locally on `T'`, `R f'_* ℱ'` is computed by the pullback `g^* P` of the bounded complex of finite
free modules of `AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage`.
A bounded complex of finite free modules whose cohomology is finite locally free and
concentrated in degree `i` is locally homotopy equivalent to that cohomology placed in degree
`i`, so its fibre at a point `t'` of `T'` has cohomology of dimension `r` in degree `i` only.
This gives `h^q_{ℱ'}(t') = 0` for `q ≠ i` and `h^i_{ℱ'}(t') = r`, and these are the fibre
dimensions of `ℱ` at `g t'` by
`AlgebraicGeometry.Scheme.Modules.hFiber_pullback_of_isPullback`.

(blueprint: `sk-thm-picard-perfect`) -/
theorem range_subset_perfectLocusOfRank_of_isPullback (hℱ : ℱ.IsFlatOver f) {i r : ℕ}
    {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
    [HasInjectiveResolutions X'.Modules] (sq : IsPullback g' f' f g)
    (h₀ : ∀ q ≠ i, IsZero ((higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ)))
    (h₁ : ((higherDirectImage f' i).obj ((Modules.pullback g').obj ℱ)).IsFiniteLocallyFreeOfRank
      r) :
    Set.range g.base ⊆ ℱ.perfectLocusOfRank f i r := by
  rintro _ ⟨t', rfl⟩
  obtain ⟨U, P, d, hsU, hP, hbc⟩ := exists_isFiniteFreeComplex_higherDirectImage f ℱ hℱ (g.base t')
  obtain ⟨UP, hUP⟩ := hP.exists_opens_range_subset_iff i r
  obtain ⟨gs, hgs⟩ := exists_comp_ι_eq_fromSpecResidueField hsU
  rw [← isFiniteLocallyFreeInDegree_homology_pullback_iff f ℱ hP hbc gs hgs i r]
  refine (hUP gs).1 ?_
  -- the base change of `P` to `V = g⁻¹ U` computes `R f'_* ℱ'` there
  let V := g ⁻¹ᵁ U
  have hgV : Set.range (V.ι ≫ g).base ⊆ Set.range U.ι.base := by
    rintro _ ⟨w, rfl⟩
    exact ⟨⟨_, w.2⟩, rfl⟩
  let gV := IsOpenImmersion.lift U.ι (V.ι ≫ g) hgV
  have hgV' : gV ≫ U.ι = V.ι ≫ g := IsOpenImmersion.lift_fac _ _ _
  have e q := (nonempty_restrict_higherDirectImage_iso_homology f ℱ hbc g g' f' sq V gV hgV' q).some
  have hV : Set.range gV.base ⊆ UP := (hUP gV).2
    ⟨fun q hq ↦ ((restrictFunctor V.ι).map_isZero (h₀ q hq)).of_iso (e q).symm,
      SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (e i)⟩
  rintro _ ⟨x, rfl⟩
  have : gs.base x = gV.base ⟨t', hsU⟩ := by
    refine U.ι.isOpenEmbedding.injective ?_
    rw [← Scheme.Hom.comp_apply, hgs, ← Scheme.Hom.comp_apply, hgV']
    exact (Scheme.range_fromSpecResidueField (g.base t')).subset ⟨x, rfl⟩
  rw [this]
  exact hV ⟨_, rfl⟩

/-- **Functorial characterisation of the rank-`r` perfect locus.** In the situation of
`AlgebraicGeometry.Scheme.Modules.range_subset_perfectLocusOfRank_of_isPullback`, the image of
`g` lies in `U_{i,r}` if and only if `R f'_* ℱ'` is a finite locally free module of rank `r`
placed in degree `i`: the higher direct images `R^q f'_* ℱ'` vanish for `q ≠ i` and
`R^i f'_* ℱ'` is finite locally free of rank `r`.

(blueprint: `sk-thm-picard-perfect`) -/
theorem range_subset_perfectLocusOfRank_iff (hℱ : ℱ.IsFlatOver f) (i r : ℕ)
    {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
    [HasInjectiveResolutions X'.Modules] (sq : IsPullback g' f' f g) :
    Set.range g.base ⊆ ℱ.perfectLocusOfRank f i r ↔
      (∀ q ≠ i, IsZero ((higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ))) ∧
        ((higherDirectImage f' i).obj ((Modules.pullback g').obj ℱ)).IsFiniteLocallyFreeOfRank r :=
  ⟨fun hg ↦ ⟨fun _ hq ↦ isZero_higherDirectImage_of_isPullback f ℱ hℱ g g' f' sq
      (hg.trans (perfectLocusOfRank_subset ℱ f i r)) hq,
    isFiniteLocallyFreeOfRank_higherDirectImage_of_isPullback f ℱ hℱ g g' f' sq hg⟩,
   fun h ↦ range_subset_perfectLocusOfRank_of_isPullback f ℱ hℱ g g' f' sq h.1 h.2⟩

/-- **Base change detects `U_{i,r}`.** In the situation of
`AlgebraicGeometry.Scheme.Modules.range_subset_perfectLocusOfRank_iff`, the image of `g` lies in
the locus of points at which the fibre cohomology vanishes outside degree `i` and has dimension
`r` in degree `i` if and only if `R^q f'_* ℱ'` vanishes for `q ≠ i` and `R^i f'_* ℱ'` is finite
locally free of rank `r`.

(blueprint: `sk-thm-picard-perfect`) -/
theorem range_subset_setOf_hFiber_eq_iff (hℱ : ℱ.IsFlatOver f) (i r : ℕ)
    {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
    [HasInjectiveResolutions X'.Modules] (sq : IsPullback g' f' f g) :
    Set.range g.base ⊆ {t : T | (∀ q ≠ i, ℱ.hFiber f q t = 0) ∧ ℱ.hFiber f i t = r} ↔
      (∀ q ≠ i, IsZero ((higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ))) ∧
        ((higherDirectImage f' i).obj ((Modules.pullback g').obj ℱ)).IsFiniteLocallyFreeOfRank r :=
  range_subset_perfectLocusOfRank_iff f ℱ hℱ i r g g' f' sq

/-- **The open locus where `R f_* ℱ` is finite locally free in one degree.** With `f : X ⟶ T`
proper of finite presentation, `ℱ` an `𝒪_X`-module of finite presentation which is flat over `T`,
and `i r : ℕ`, there is an open subscheme `U` of `T`, namely `U_{i,r}`, such that a morphism
`g : T' ⟶ T` factors through `U` if and only if `R f'_* ℱ'` is a finite locally free module of
rank `r` placed in degree `i` [Stacks, Tag 0B9S].

Here `f' : X' ⟶ T'` and `g' : X' ⟶ X` are the base change of `f` along `g`, and `ℱ'` is the
pullback of `ℱ` to `X'`. The set `U_{i,r}` is open by
`AlgebraicGeometry.Scheme.Modules.isOpen_perfectLocusOfRank`, and the factorisation criterion is
`AlgebraicGeometry.Scheme.Modules.range_subset_perfectLocusOfRank_iff`.

(blueprint: `lem-pc-flat-rf-open`) -/
theorem exists_opens_range_subset_iff_isFiniteLocallyFreeInDegree (hℱ : ℱ.IsFlatOver f)
    (i r : ℕ) :
    ∃ U : T.Opens, (U : Set T) = ℱ.perfectLocusOfRank f i r ∧
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f g →
        (Set.range g.base ⊆ U ↔ IsFiniteLocallyFreeInDegree
          (fun q ↦ (higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ)) i r) :=
  ⟨⟨_, isOpen_perfectLocusOfRank f ℱ hℱ i r⟩, rfl, fun g g' f' _ sq ↦
    (range_subset_perfectLocusOfRank_iff f ℱ hℱ i r g g' f' sq).trans
      ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩⟩

end Coherence

section AffineMorphism

/-- **The higher direct images along an affine morphism vanish.** Let `f : X ⟶ T` be affine
and `ℱ` a quasi-coherent `𝒪_X`-module. Then `R^q f_* ℱ = 0` for `q > 0`: the higher direct
images commute with restriction to an affine open `V` of `T`, over which their sections are
`H^q(f⁻¹ V, ℱ)`, and these vanish since `f⁻¹ V` is affine
(`AlgebraicGeometry.Scheme.Modules.subsingleton_H_succ_of_isAffine`).

(blueprint: `lem-pc-affine-morphism-hi`) -/
theorem isZero_higherDirectImage_of_isAffineHom (f : X ⟶ T) [IsAffineHom f]
    [HasInjectiveResolutions X.Modules] (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] {q : ℕ} (hq : 0 < q) :
    IsZero ((higherDirectImage f q).obj ℱ) := by
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  refine isZero_of_forall_affineOpens _ fun V ↦ ?_
  have := isGrothendieckAbelian (f ⁻¹ᵁ V.1).toScheme
  have : IsAffine V.1.toScheme := V.2
  have : IsAffine (f ⁻¹ᵁ V.1).toScheme := V.2.preimage f
  obtain ⟨e⟩ := nonempty_higherDirectImage_iso_restrict f ℱ V.1.ι (f ⁻¹ᵁ V.1).ι (f ∣_ V.1)
    (isPullback_morphismRestrict f V.1).flip (q + 1)
  obtain ⟨e'⟩ := nonempty_sections_higherDirectImage_iso_H (f ∣_ V.1)
    ((Modules.pullback (f ⁻¹ᵁ V.1).ι).obj ℱ) (q + 1)
  have := subsingleton_H_succ_of_isAffine ((Modules.pullback (f ⁻¹ᵁ V.1).ι).obj ℱ) q
  have : Subsingleton Γ((higherDirectImage (f ∣_ V.1) (q + 1)).obj
      ((Modules.pullback (f ⁻¹ᵁ V.1).ι).obj ℱ), ⊤) := e'.toEquiv.subsingleton
  have : Subsingleton Γ(((higherDirectImage f (q + 1)).obj ℱ).restrict V.1.ι, ⊤) :=
    (asIso (e.hom.app ⊤)).addCommGroupIsoToAddEquiv.toEquiv.symm.subsingleton
  have : Subsingleton Γ((higherDirectImage f (q + 1)).obj ℱ, V.1.ι ''ᵁ ⊤) :=
    (((higherDirectImage f (q + 1)).obj ℱ).restrictAppIso V.1.ι ⊤).addCommGroupIsoToAddEquiv
      |>.toEquiv.symm.subsingleton
  rwa [Scheme.Opens.ι_image_top] at this

/-- **The pushforward along an affine morphism is quasi-coherent.** For `f : X ⟶ T` affine and
`ℱ` quasi-coherent, `f_* ℱ = R⁰ f_* ℱ` is quasi-coherent
(`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_higherDirectImage`).

(blueprint: `lem-pc-affine-morphism-hi`) -/
theorem isQuasicoherent_pushforward_of_isAffineHom (f : X ⟶ T) [IsAffineHom f] (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] :
    ((pushforward f).obj ℱ).IsQuasicoherent := by
  have := isGrothendieckAbelian X
  have : PreservesFiniteLimits (pushforward f) :=
    have := (pullbackPushforwardAdjunction f).rightAdjoint_preservesLimits.{0, 0}
    inferInstance
  exact (SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso
    ((Functor.rightDerivedZeroIsoSelf (pushforward f)).app ℱ)
    (isQuasicoherent_higherDirectImage f ℱ 0)

end AffineMorphism

section Finiteness

variable {k : Type u} [Field k] [X.Over (Spec (.of k))]

/-- **Finiteness of coherent cohomology.** On a scheme `X` proper over a field `k`, the
cohomology groups `H^q(X, ℱ)` of a coherent `𝒪_X`-module `ℱ` are finite-dimensional over `k`.
Coherence is spelled as quasi-coherence together with finite presentation.

This is the case `T = Spec k` of the finiteness of the higher direct images along a proper
morphism to a Noetherian affine scheme
(`AlgebraicGeometry.Scheme.Modules.finite_sections_higherDirectImage`), transported along the
identification `Γ(Spec k, R^q f_* ℱ) ≅ H^q(X, ℱ)`
(`AlgebraicGeometry.Scheme.Modules.exists_bijective_semilinearMap_sections_higherDirectImage_H`).
-/
@[stacks 02O5]
theorem finiteDimensional_H_of_isProper [IsProper (X ↘ Spec (.of k))] (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    FiniteDimensional k (ℱ.H q) := by
  classical
  have := isGrothendieckAbelian X
  have : IsNoetherianRing Γ(Spec (.of k), ⊤) :=
    isNoetherianRing_of_ringEquiv _ (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm
  obtain ⟨e, he⟩ := exists_bijective_semilinearMap_sections_higherDirectImage_H
    (X ↘ Spec (.of k)) ℱ q
  obtain ⟨s, hs⟩ := (finite_sections_higherDirectImage (X ↘ Spec (.of k)) ℱ q).fg_top
  have key (x) (hx : x ∈ Submodule.span Γ(Spec (.of k), ⊤) (s : Set _)) :
      e x ∈ Submodule.span k (e '' s) := by
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | smul a x _ hx =>
      obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2 a
      have hc : c • e x = e ((Scheme.ΓSpecIso (.of k)).inv c • x) := by
        rw [smul_H_eq_globalSectionsRingHom_smul, e.map_smulₛₗ]
        rfl
      rw [← hc]
      exact Submodule.smul_mem _ c hx
  refine ⟨⟨s.image e, eq_top_iff.2 fun y _ ↦ ?_⟩⟩
  obtain ⟨x, rfl⟩ := he.2 y
  rw [Finset.coe_image]
  exact key x (hs ▸ Submodule.mem_top)

end Finiteness

end AlgebraicGeometry.Scheme.Modules
