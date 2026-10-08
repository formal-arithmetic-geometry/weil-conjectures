/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
public import WeilConjectures.AlgebraicGeometry.DualNumbers
public import WeilConjectures.AlgebraicGeometry.EffectiveDescent
public import WeilConjectures.AlgebraicGeometry.Picard.Degree
public import WeilConjectures.AlgebraicGeometry.Picard.Scheme
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.Algebra.DualNumber
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# The Jacobian of a smooth projective curve

Let `X` be a smooth proper geometrically integral curve of genus `g` over a field `k`.  This file
states the four steps that turn the representability of the Picard functor
(`AlgebraicGeometry.isRepresentable_picardFunctor`) into the Jacobian variety:

* the Picard scheme decomposes as a disjoint union `∐_{d ∈ ℤ} Pic^d` of open and closed
  subschemes indexed by the fibrewise degree;
* the tangent space of `Pic^0` at the unit is `H^1(X, 𝒪_X)`, of dimension `g`;
* `Pic^0` is an abelian variety of dimension `g`, the Jacobian `J(X)`;
* over a general base field the Jacobian descends by Galois descent.

## Implementation notes

The fibrewise degree of a class `ℒ ∈ Pic (X_T)` is measured by pulling `ℒ` back to the fibre
`X_K` over a field-valued point `Spec K → T` and taking
`AlgebraicGeometry.Scheme.Modules.degree`, the cohomological degree `χ(ℒ) - χ(𝒪)` of
`WeilConjectures/AlgebraicGeometry/Curve/RiemannRoch.lean`.

Membership in `AlgebraicGeometry.picardSubfunctorDegree` is quantified over field-valued points
of the base, so over a base with none — the empty scheme, say — every class lies in every
degree-`d` subfunctor. That is harmless for the sheafification, but it means the disjointness
clause of `exists_decomposition_picardFunctor` is a statement about the representing schemes,
not about the subfunctors.

The decomposition is spelled out as a family of open and closed immersions with disjoint ranges
covering `P`, rather than as `Nonempty (P ≅ ∐ Pd)`: the pinned Mathlib has no coproducts of
schemes over a base indexed by `ℤ` (only `MorphismProperty.Over ⊤ S` has coproducts), so the
`∐` is not available.

Several clauses of the blueprint statements cannot be expressed and are dropped:

* there is no group law on `AlgebraicGeometry.Scheme.Pic`, since there is no tensor product of
  sheaves of modules. So "`P^0` is an open and closed **subgroup scheme**" is stated only as
  "`P^0` is an open and closed subscheme, and carries a commutative group scheme structure";
  `Pic^0(C)` is only a type, not a group; and the `ℓⁿ`-torsion clause
  `J₀[ℓⁿ](k̄₀) ≅ Pic^0(C)[ℓⁿ]` of `sk-prop-jacobian-descent` is omitted — it follows from the
  equivariant bijection below by restricting to `ℓⁿ`-torsion once the group law exists.
* there is no twisting sheaf `𝒪_X(D)`, so "tensoring with `𝒪_X(dP)` is an isomorphism
  `P^0 ≅ P^d`" is stated as the bare existence of an isomorphism of `k`-schemes.
* Mathlib has no tangent space of a scheme, so `AlgebraicGeometry.tangentSpaceAt` is defined
  here through the functor of points. It is given a `k`-vector space structure only at the
  unit of a group scheme, where it is the kernel `AlgebraicGeometry.tangentSubgroup` of
  `P(k[ε]) → P(k)` and the addition is the group law. The standard construction instead puts a
  `k`-vector space structure on the tangent space at any `k`-point of any `k`-scheme, and then
  identifies its addition with the group law at the unit; that comparison is not formalised.
  Two facts are left `sorry`: the commutativity of `tangentSubgroup P` and the axiom
  `(c + d) • v = c • v + d • v`. The instance `Module k (tangentSpaceAt P η[P])`, and with it
  the statement of `nonempty_tangentSpaceAt_linearEquiv_H_one`, depends on them.
* Mathlib has no `AbelianVariety` class, so "abelian variety of dimension `g`" is spelled out
  as `CategoryTheory.CommGrpObj` together with `AlgebraicGeometry.IsProper`,
  `AlgebraicGeometry.SmoothOfRelativeDimension g` and
  `AlgebraicGeometry.GeometricallyIntegral` for the structure morphism.
* in `exists_jacobian_descent` the Galois group is taken to be `k̄₀ ≃ₐ[k₀] k̄₀` rather than
  `Gal(k_s/k₀)`. Restriction `k̄₀ ≃ₐ[k₀] k̄₀ → k_s ≃ₐ[k₀] k_s` is surjective with the same
  orbits, so this is the same action; `k_s` is kept as a hypothesis so that the intended group
  is visible. "The representing isomorphism descends canonically, compatibly with base change"
  is rendered as the representability statement for `J₀ ×_{k₀} k̄₀` together with the
  equivariance; the descent itself happens in
  `AlgebraicGeometry.exists_commGrpObj_representableBy_picardFunctorDegree`, which shows that
  `Pic^0_{C₀/k₀}` is represented over `k₀`.

## Galois descent

The descent from a separable closure `k_s` to `k` follows the blueprint: the Jacobian `J_s` of
`C_{k_s}` represents the restriction of `Pic^0_{C/k}` to `k_s`-schemes and therefore carries a
canonical descent datum (`CategoryTheory.Functor.RepresentableBy.overDescentDatum`, in the
transport form `CategoryTheory.Over.DescentDatum`); the datum is defined at a finite separable
level `K`, where it is effective because the representing scheme is projective, and the group
law and the geometric properties descend with it. The deep inputs — spreading out, effective
descent, fpqc descent of properties, the base change of the degree-zero Picard functor and its
value at an algebraically closed point — are stated separately.

## Main definitions

- `AlgebraicGeometry.picardFibreDegree`: the degree of a relative Picard class on the fibre over
  a field-valued point of the base.
- `AlgebraicGeometry.picardSubfunctorDegree`: the degree-`d` subfunctor of the Picard presheaf.
- `AlgebraicGeometry.picardFunctorDegree`: the degree-`d` part `Pic^d_{X/k}` of the relative
  Picard functor.
- `AlgebraicGeometry.dualNumbersScale`: the `k`-endomorphism `ε ↦ cε` of `(Spec k)[ε]`, the
  dual-number thickening `AlgebraicGeometry.Scheme.dualNumbersOver (Spec k)` of `Spec k` whose
  `k`-point `ε ↦ 0` is `AlgebraicGeometry.Scheme.dualNumbersιOver`.
- `AlgebraicGeometry.tangentSpaceAt`: the tangent space of a `k`-scheme at a `k`-rational point,
  defined through the functor of points.
- `AlgebraicGeometry.tangentSubgroup`: the tangent space of a group scheme at the unit, as the
  kernel of `P(k[ε]) → P(k)`; it gives `tangentSpaceAt P η[P]` its `k`-vector space structure.
- `AlgebraicGeometry.specAlgEquivOver`: a `k`-algebra automorphism of `K` as an automorphism of
  the `k`-scheme `Spec K`.

## Main statements

- `AlgebraicGeometry.picardFibreDegree_eq_of_connectedSpace`,
  `AlgebraicGeometry.exists_decomposition_picardFunctor`,
  `AlgebraicGeometry.nonempty_commGrpObj_of_representableBy` and
  `AlgebraicGeometry.nonempty_iso_of_representableBy`: the degree decomposition of the Picard
  scheme (blueprint `sk-prop-picard-degree-decomposition`).
- `AlgebraicGeometry.nonempty_tangentSpaceAt_linearEquiv_H_one`: the tangent space of the Jacobian
  (blueprint `sk-prop-picard-jacobian-tangent`).
- `AlgebraicGeometry.isProper_of_representableBy_picardFunctorDegree` and
  `AlgebraicGeometry.smoothOfRelativeDimension_of_representableBy_picardFunctorDegree`: the
  theorem of the base, every `Pic^d_{X/k}` is proper and smooth of dimension `g` (blueprint
  `thm-sc-theorem-of-the-base`).
- `AlgebraicGeometry.exists_jacobian`: the Jacobian is an abelian variety (blueprint
  `sk-prop-jacobian`, `thm-sc-jacobian-representability`).
- `AlgebraicGeometry.exists_jacobian_pullback`: the Jacobian over a separable closure (blueprint
  `thm-pd-geometric-pic0`).
- `AlgebraicGeometry.nonempty_picardFunctorDegree_iso_of_isPullback`: `Pic^0` commutes with base
  change (blueprint `cor-pd-pic0-base-change`).
- `AlgebraicGeometry.exists_intermediateField_descentDatum`: the descent datum is defined at a
  finite separable level (blueprint `cor-pd-finite-level`).
- `AlgebraicGeometry.nonempty_representableBy_picardFunctorDegree_of_isPullback`: `Pic^0_{C/k}`
  is represented by the descended scheme (Step 7 of `thm-pd-jacobian-general-field`).
- `AlgebraicGeometry.exists_commGrpObj_representableBy_picardFunctorDegree`: `Pic^0_{C/k}` is
  represented by an abelian variety over any field `k` (blueprint `thm-pd-jacobian-general-field`).
- `AlgebraicGeometry.exists_jacobian_descent`: the Jacobian over a general base field (blueprint
  `sk-prop-jacobian-descent`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

namespace AlgebraicGeometry

open Scheme

section DegreeSubfunctor

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The degree of a relative Picard class on a fibre.  Let `f : X ⟶ Spec k` be a `k`-scheme, let
`T` be a `k`-scheme and let `L ∈ Pic (X_T)` be a section of the Picard presheaf over `T`.  A
field-valued point `t : Spec K ⟶ T` of `T` cuts out the fibre `X_K = X ×_{Spec k} Spec K`, and
`picardFibreDegree f L t` is the degree `deg ℒ_t = χ(ℒ_t) - χ(𝒪_{X_K})` of the pullback of `L`
to that fibre, in the sense of `AlgebraicGeometry.Scheme.Modules.degree`.

The `K`-scheme structure on `X_K` is the second projection; it is supplied explicitly, since it
is not an instance on a bare pullback.

(blueprint: `sk-prop-picard-degree-decomposition`) -/
noncomputable def picardFibreDegree (f : X ⟶ Spec (.of k)) {T : Over (Spec (.of k))}
    (L : (picardPresheaf f).obj (.op T)) {K : Type u} [Field K] [Algebra k K]
    (t : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ T) : ℤ :=
  letI : (Limits.pullback f
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))).hom).Over (Spec (.of K)) :=
    ⟨Limits.pullback.snd f (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))).hom⟩
  Modules.degree K ((fromSkeleton _).obj (Pic.map (baseChangeMap f t) L).val)

/-- The degree-`d` subfunctor of the Picard presheaf of `f : X ⟶ Spec k`: the classes
`ℒ ∈ Pic (X_T)` all of whose fibres have degree `d`, i.e. `deg ℒ_t = d` for every field-valued
point `t` of `T`.  It is a subfunctor because the fibres of the pullback of `ℒ` along `T' ⟶ T`
are among the fibres of `ℒ`.

Over a base with no field-valued points every class satisfies the condition vacuously; see the
implementation notes of this module.

(blueprint: `sk-prop-picard-degree-decomposition`) -/
noncomputable def picardSubfunctorDegree (f : X ⟶ Spec (.of k)) (d : ℤ) :
    Subfunctor (picardPresheaf f) where
  obj T := {L | ∀ (K : Type u) [Field K] [Algebra k K]
    (t : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ T.unop),
      picardFibreDegree f L t = d}
  map := by
    rintro ⟨U⟩ ⟨V⟩ ⟨i⟩ L hL
    intro K _ _ t
    have h := hL K (t ≫ i)
    have e : Pic.map (baseChangeMap f (t ≫ i)) L =
        Pic.map (baseChangeMap f t) (Pic.map (baseChangeMap f i) L) := by
      rw [baseChangeMap_comp, Pic.map_comp]
    simp only [picardFibreDegree, e] at h
    exact h

/-- The degree-`d` part `Pic^d_{X/k}` of the relative Picard functor: the fppf sheafification of
the degree-`d` subfunctor `AlgebraicGeometry.picardSubfunctorDegree` of the Picard presheaf, in
the same way that `AlgebraicGeometry.picardFunctor` is the fppf sheafification of the whole
Picard presheaf.

(blueprint: `sk-prop-picard-degree-decomposition`) -/
noncomputable def picardFunctorDegree (f : X ⟶ Spec (.of k)) (d : ℤ) :
    Sheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type (u + 1))).obj
    (picardSubfunctorDegree f d).toFunctor

/-- **The degree on a fibre over a field-valued point is the fibrewise degree** at the image
point: the degree of `ℒ` on the fibre `X_K` over `t : Spec K ⟶ T` is the fibrewise degree
`deg ℒ_t` of `AlgebraicGeometry.picardPresheafDegree` at the image of the point of `Spec K`.

(blueprint: `lem-pd-degree-locally-constant`, part 3) -/
theorem picardFibreDegree_eq_picardPresheafDegree (f : X ⟶ Spec (.of k)) [IsProper f]
    [LocallyOfFinitePresentation f] {T : Over (Spec (.of k))}
    (L : (picardPresheaf f).obj (.op T)) {K : Type u} [Field K] [Algebra k K]
    (t : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ T) (s : Spec (.of K)) :
    picardFibreDegree f L t = picardPresheafDegree f L (t.left s) := by
  rw [← picardPresheafDegree_map f t L s]
  have := Pic.isInvertible ((picardPresheaf f).map t.op L)
  have : ((fromSkeleton _).obj (Pic.val ((picardPresheaf f).map t.op L))).IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  have : SheafOfModules.IsFinitePresentation.{u, u, u} (SheafOfModules.unit (pullback f
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))).hom).ringCatSheaf) :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  simp only [picardFibreDegree, picardPresheafDegree, Modules.degree]
  rw [Modules.eulerCharFiber_eq_eulerChar, Modules.eulerCharFiber_eq_eulerChar]
  rfl

/-- A class lies in the degree-`d` subfunctor exactly when its fibrewise degree is `d` at every
point. -/
theorem mem_picardSubfunctorDegree_iff (f : X ⟶ Spec (.of k)) [IsProper f]
    [LocallyOfFinitePresentation f] (d : ℤ) {T : Over (Spec (.of k))}
    (L : (picardPresheaf f).obj (.op T)) :
    L ∈ (picardSubfunctorDegree f d).obj (.op T) ↔ ∀ t, picardPresheafDegree f L t = d := by
  refine ⟨fun h t ↦ ?_, fun h K _ _ t ↦ ?_⟩
  · let φ := T.left.fromSpecResidueField t ≫ T.hom
    let : Algebra k (T.left.residueField t) := (Spec.preimage φ).hom.toAlgebra
    let τ : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (T.left.residueField t)))) ⟶ T :=
      Over.homMk (T.left.fromSpecResidueField t) (Spec.map_preimage φ).symm
    obtain ⟨s⟩ : Nonempty (Spec (T.left.residueField t)) := inferInstance
    have := h _ τ
    rwa [picardFibreDegree_eq_picardPresheafDegree f L τ s,
      show τ.left s = t from Scheme.fromSpecResidueField_apply _ _] at this
  · obtain ⟨s⟩ : Nonempty (Spec (.of K)) := inferInstance
    rw [picardFibreDegree_eq_picardPresheafDegree f L t s]
    exact h _

/-- **The degree-`d` subfunctor is compatible with base change along a field extension.** Let
`f' : X' ⟶ Spec K` be the base change of `f : X ⟶ Spec k` along `Spec K ⟶ Spec k`. Through the
identification `AlgebraicGeometry.picardPresheafIsoOfIsPullback` of the Picard presheaves, a class
has all its fibrewise degrees equal to `d` exactly when its transport does, so the restriction of
the degree-`d` subfunctor of `f` to schemes over `K` is the degree-`d` subfunctor of `f'`. -/
noncomputable def picardSubfunctorDegreeIsoOfIsPullback {K : Type u} [Field K] [Algebra k K]
    {X' : Scheme.{u}} {f : X ⟶ Spec (.of k)} {f' : X' ⟶ Spec (.of K)} {g' : X' ⟶ X}
    [IsProper f] [LocallyOfFinitePresentation f]
    (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (d : ℤ) :
    (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).op ⋙
      (picardSubfunctorDegree f d).toFunctor ≅ (picardSubfunctorDegree f' d).toFunctor :=
  have : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) h ‹_›
  have : LocallyOfFinitePresentation f' :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) h ‹_›
  NatIso.ofComponents
    (fun T ↦ (Equiv.subtypeEquiv ((picardPresheafIsoOfIsPullback h).app T).toEquiv
      fun L ↦ by
        refine (mem_picardSubfunctorDegree_iff f d (T := (Over.map _).obj T.unop) L).trans
          (Iff.trans ?_ (mem_picardSubfunctorDegree_iff f' d (T := T.unop) _).symm)
        refine forall_congr' fun t ↦ ?_
        exact Iff.of_eq (congrArg (· = d)
          (picardPresheafDegree_picardPresheafIsoOfIsPullback f (T := T.unop) h L t).symm)).toIso)
    fun φ ↦ by
      ext L
      apply Subtype.ext
      exact NatTrans.naturality_apply (picardPresheafIsoOfIsPullback h).hom φ L.1

end DegreeSubfunctor

section Decomposition

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsSepClosed k]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [GeometricallyIntegral (X ↘ Spec (.of k))]

set_option linter.unusedSectionVars false in
/-- **The fibrewise degree is locally constant.** For a connected `k`-scheme `T` and a class
`ℒ ∈ Pic (X_T)`, all the fibrewise degrees `deg ℒ_t` agree.

(blueprint: `sk-prop-picard-degree-decomposition`) -/
theorem picardFibreDegree_eq_of_connectedSpace (T : Over (Spec (.of k)))
    [ConnectedSpace T.left] (L : (picardPresheaf (X ↘ Spec (.of k))).obj (.op T))
    {K : Type u} [Field K] [Algebra k K]
    (t : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ T)
    {K' : Type u} [Field K'] [Algebra k K']
    (t' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K'))) ⟶ T) :
    picardFibreDegree (X ↘ Spec (.of k)) L t = picardFibreDegree (X ↘ Spec (.of k)) L t' := by
  obtain ⟨s⟩ : Nonempty (Spec (.of K)) := inferInstance
  obtain ⟨s'⟩ : Nonempty (Spec (.of K')) := inferInstance
  rw [picardFibreDegree_eq_picardPresheafDegree _ L t s,
    picardFibreDegree_eq_picardPresheafDegree _ L t' s']
  exact (isLocallyConstant_picardPresheafDegree _ L).apply_eq_of_preconnectedSpace _ _

set_option linter.unusedSectionVars false in
/-- **The degree decomposition of the Picard scheme.** Let `X` be a smooth projective curve over
a separably closed field `k` and let `P` represent the Picard functor `Pic_{X/k}`.  Then `P` is
the disjoint union `∐_{d ∈ ℤ} P^d` of a family of open and closed subschemes indexed by `ℤ`,
and `P^d` represents the degree-`d` part `Pic^d_{X/k}`.

(blueprint: `sk-prop-picard-degree-decomposition`) -/
theorem exists_decomposition_picardFunctor (P : Over (Spec (.of k)))
    (hP : (picardFunctor (X ↘ Spec (.of k))).obj.RepresentableBy P) :
    ∃ (Pd : ℤ → Over (Spec (.of k))) (j : ∀ d, Pd d ⟶ P),
      (∀ d, IsOpenImmersion (j d).left) ∧
      (∀ d, IsClopen (Set.range (j d).left.base)) ∧
      (∀ d d', d ≠ d' → Disjoint (Set.range (j d).left.base) (Set.range (j d').left.base)) ∧
      (⋃ d, Set.range (j d).left.base) = Set.univ ∧
      ∀ d, Nonempty ((picardFunctorDegree (X ↘ Spec (.of k)) d).obj.RepresentableBy (Pd d)) := by
  set f := X ↘ Spec (.of k)
  let J := Scheme.fppfTopology.over (Spec (.of k))
  -- the degree `δ : P → ℤ` of the universal class
  let δ := picardDegree f (hP.homEquiv (𝟙 P))
  have hδ : IsLocallyConstant δ := isLocallyConstant_picardDegree f _
  have hδh {T : Over (Spec (.of k))} (h : T ⟶ P) (t : T.left) :
      picardDegree f (hP.homEquiv h) t = δ (h.left t) := by
    rw [show hP.homEquiv h = (picardFunctor f).obj.map h.op (hP.homEquiv (𝟙 P)) by
      simpa using hP.homEquiv_comp h (𝟙 P), picardDegree_map]
  -- the components `P^d = δ⁻¹(d)`
  let U (d : ℤ) : P.left.Opens := ⟨δ ⁻¹' {d}, hδ.isOpen_fiber d⟩
  let Pd (d : ℤ) : Over (Spec (.of k)) := Over.mk ((U d).ι ≫ P.hom)
  let j (d : ℤ) : Pd d ⟶ P := Over.homMk (U d).ι
  have hj (d : ℤ) : Set.range (j d).left.base = δ ⁻¹' {d} := (U d).range_ι
  have hjmono (d : ℤ) {T : Over (Spec (.of k))} (a b : T ⟶ Pd d) (hab : a ≫ j d = b ≫ j d) :
      a = b := by
    ext1
    exact (cancel_mono (U d).ι).1 congr($(hab).left)
  have hlift (d : ℤ) {T : Over (Spec (.of k))} (h : T ⟶ P) (hh : ∀ t, δ (h.left t) = d) :
      ∃ l : T ⟶ Pd d, l ≫ j d = h := by
    have H : Set.range h.left.base ⊆ Set.range (U d).ι.base := by
      rw [(U d).range_ι]
      rintro _ ⟨t, rfl⟩
      exact hh t
    refine ⟨Over.homMk (IsOpenImmersion.lift (U d).ι h.left H) ?_, ?_⟩
    · simp [Pd, IsOpenImmersion.lift_fac_assoc]
    · ext1
      exact IsOpenImmersion.lift_fac _ _ _
  refine ⟨Pd, j, fun d ↦ inferInstanceAs (IsOpenImmersion (U d).ι), fun d ↦ ?_, ?_, ?_,
    fun d ↦ ⟨?_⟩⟩
  · rw [hj]
    exact hδ.isClopen_fiber d
  · intro d d' hdd'
    rw [hj, hj]
    exact Disjoint.preimage _ (Set.disjoint_singleton.2 hdd')
  · simp only [hj]
    ext t
    simp
  -- `P^d` represents `Pic^d_{X/k}`
  let S := picardSubfunctorDegree f d
  have hmem {T : Over (Spec (.of k))} (L : (picardPresheaf f).obj (.op T))
      (hL : L ∈ S.obj (.op T)) (t : T.left) :
      δ ((hP.homEquiv.symm ((toPicardFunctor f).app (.op T) L)).left t) = d := by
    rw [← hδh, Equiv.apply_symm_apply, picardDegree_toPicardFunctor]
    exact (mem_picardSubfunctorDegree_iff f d L).1 hL t
  let lift {T : Over (Spec (.of k))} (L : S.toFunctor.obj (.op T)) : T ⟶ Pd d :=
    (hlift d _ (hmem L.1 L.2)).choose
  have lift_j {T : Over (Spec (.of k))} (L : S.toFunctor.obj (.op T)) :
      lift L ≫ j d = hP.homEquiv.symm ((toPicardFunctor f).app (.op T) L.1) :=
    (hlift d _ (hmem L.1 L.2)).choose_spec
  let α : S.toFunctor ⟶ uliftYoneda.{u + 1}.obj (Pd d) :=
    { app T := TypeCat.ofHom fun L ↦ ULift.up (lift L)
      naturality T T' g := by
        ext L
        refine ULift.ext _ _ (hjmono d _ _ ?_)
        change lift (S.toFunctor.map g L) ≫ j d = (g.unop ≫ lift L) ≫ j d
        rw [lift_j, Category.assoc, lift_j, hP.comp_homEquiv_symm]
        exact congrArg hP.homEquiv.symm (NatTrans.naturality_apply (toPicardFunctor f) g L.1) }
  have hinj : Presheaf.IsLocallyInjective J α := by
    refine ⟨fun {T} L L' h ↦ ?_⟩
    have h' : (toPicardFunctor f).app T L.1 = (toPicardFunctor f).app T L'.1 := by
      apply hP.homEquiv.symm.injective
      rw [← lift_j, ← lift_j]
      exact congrArg (· ≫ j d) (congrArg ULift.down h)
    exact J.superset_covering (fun Z g hg ↦ Subtype.ext hg)
      (Presheaf.equalizerSieve_mem J (toPicardFunctor f) L.1 L'.1 h')
  have hsurj : Presheaf.IsLocallySurjective J α := by
    refine ⟨fun {T} l ↦ ?_⟩
    refine J.superset_covering ?_
      (Presheaf.imageSieve_mem J (toPicardFunctor f) (hP.homEquiv (l.down ≫ j d)))
    rintro Z g ⟨L, hL⟩
    have hLS : L ∈ S.obj (.op Z) := by
      refine (mem_picardSubfunctorDegree_iff f d L).2 fun z ↦ ?_
      rw [← picardDegree_toPicardFunctor, hL, picardDegree_map, hδh, ← Set.mem_singleton_iff,
        ← Set.mem_preimage, ← hj d]
      exact ⟨l.down.left (g.left z), rfl⟩
    refine ⟨⟨L, hLS⟩, ULift.ext _ _ (hjmono d _ _ ?_)⟩
    change lift ⟨L, hLS⟩ ≫ j d = (g ≫ l.down) ≫ j d
    rw [lift_j, Category.assoc, ← Equiv.symm_apply_apply hP.homEquiv (l.down ≫ j d),
      hP.comp_homEquiv_symm]
    exact congrArg hP.homEquiv.symm hL
  -- hence `α` induces an isomorphism from `Pic^d_{X/k}` to the sheaf represented by `P^d`
  have : J.Subcanonical := inferInstanceAs (fppfTopology.over (Spec (.of k))).Subcanonical
  let Y := J.uliftYoneda.{u + 1}.obj (Pd d)
  let β : (presheafToSheaf J (Type (u + 1))).obj S.toFunctor ⟶ Y :=
    ⟨sheafifyLift J α Y.property⟩
  have fac : toSheafify J S.toFunctor ≫ β.hom = α := toSheafify_sheafifyLift J α Y.property
  have : Presheaf.IsLocallyInjective J β.hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac J α fac
  have : Presheaf.IsLocallySurjective J β.hom :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J fac
  have : IsIso β := (Sheaf.isLocallyBijective_iff_isIso β).1 ⟨inferInstance, inferInstance⟩
  exact (Functor.RepresentableBy.equivUliftYonedaIso _ (Pd d)).symm
    ((sheafToPresheaf J _).mapIso (asIso β)).symm

/-- **`Pic^0` is a commutative group scheme.** A `k`-scheme representing the degree-zero part
`Pic^0_{X/k}` of the Picard functor carries a commutative group scheme structure.

That the open immersion `P^0 ⟶ P` is a homomorphism is not stated: `P` is only given as a
representing object and carries no group structure here.

(blueprint: `sk-prop-picard-degree-decomposition`) -/
theorem nonempty_commGrpObj_of_representableBy (P₀ : Over (Spec (.of k)))
    (hP₀ : (picardFunctorDegree (X ↘ Spec (.of k)) 0).obj.RepresentableBy P₀) :
    Nonempty (CommGrpObj P₀) :=
  sorry

/-- **All the degree components are isomorphic.** Schemes representing `Pic^0_{X/k}` and
`Pic^d_{X/k}` are isomorphic as `k`-schemes; the isomorphism is tensoring with `𝒪_X(dP)` for a
rational point `P`, which cannot be named for lack of the twisting sheaf.

(blueprint: `sk-prop-picard-degree-decomposition`) -/
theorem nonempty_iso_of_representableBy (d : ℤ) (P₀ Pd : Over (Spec (.of k)))
    (hP₀ : (picardFunctorDegree (X ↘ Spec (.of k)) 0).obj.RepresentableBy P₀)
    (hPd : (picardFunctorDegree (X ↘ Spec (.of k)) d).obj.RepresentableBy Pd) :
    Nonempty (P₀ ≅ Pd) :=
  sorry

/-- **`Pic^g` is proper.** A `k`-scheme representing the degree-`g` part `Pic^g_{X/k}` of the
Picard functor, `g` the genus, is proper over `k`.  The universal divisor of the Hilbert scheme
defines `Hilb^g_{X/k} ⟶ Pic^g_{X/k}`, `D ↦ 𝒪_X(D)`; it is surjective because by Riemann–Roch
an invertible module of degree `g` has `h⁰ ≥ χ = 1`, hence is `𝒪_X(D)` for the zero divisor `D`
of a nonzero section.  So `Pic^g_{X/k}` is the image of the proper `Hilb^g_{X/k}` in a
separated `k`-scheme, hence proper (Stacks `03GN`).

(blueprint: `thm-sc-theorem-of-the-base`, properness of `Pic^g`) -/
theorem isProper_of_representableBy_picardFunctorDegree_genus (P : Over (Spec (.of k)))
    (hP : (picardFunctorDegree (X ↘ Spec (.of k)) (arithmeticGenus k X)).obj.RepresentableBy P) :
    IsProper P.hom :=
  sorry

/-- **`Pic^g` is smooth of dimension `g`.** A `k`-scheme representing the degree-`g` part
`Pic^g_{X/k}` of the Picard functor, `g` the genus, is smooth of relative dimension `g` over `k`.
The subfunctor `F` of the normalized Picard functor is represented by an open subscheme `U` of
the smooth `g`-dimensional `Hilb^g_{X/k}`, and its classes have degree `g`, so `U` is open in
`Pic^g_{X/k}`; by the twist lemma the translates of `U` by `k`-points cover `Pic^g_{X/k}`.

(blueprint: `thm-sc-theorem-of-the-base`, smoothness of `Pic^g`) -/
theorem smoothOfRelativeDimension_of_representableBy_picardFunctorDegree_genus
    (P : Over (Spec (.of k)))
    (hP : (picardFunctorDegree (X ↘ Spec (.of k)) (arithmeticGenus k X)).obj.RepresentableBy P) :
    SmoothOfRelativeDimension (arithmeticGenus k X) P.hom :=
  sorry

/-- Two representing objects of degree components of the Picard functor are isomorphic over
`k`: both are isomorphic to a representing object of `Pic^0_{X/k}`. -/
lemma nonempty_iso_of_representableBy_picardFunctorDegree (d d' : ℤ) (P P' : Over (Spec (.of k)))
    (hP : (picardFunctorDegree (X ↘ Spec (.of k)) d).obj.RepresentableBy P)
    (hP' : (picardFunctorDegree (X ↘ Spec (.of k)) d').obj.RepresentableBy P') :
    Nonempty (P ≅ P') := by
  obtain ⟨A, -, ⟨hA⟩⟩ := isRepresentable_picardFunctor (X ↘ Spec (.of k))
  obtain ⟨Pd, -, -, -, -, -, hPd⟩ := exists_decomposition_picardFunctor A hA
  obtain ⟨h₀⟩ := hPd 0
  obtain ⟨e⟩ := nonempty_iso_of_representableBy d (Pd 0) P h₀ hP
  obtain ⟨e'⟩ := nonempty_iso_of_representableBy d' (Pd 0) P' h₀ hP'
  exact ⟨e.symm ≪≫ e'⟩

/-- A representing object of a degree component `Pic^d_{X/k}` is isomorphic to a representing
object of `Pic^g_{X/k}`, `g` the genus. -/
lemma exists_iso_representableBy_picardFunctorDegree_genus (d : ℤ) (P : Over (Spec (.of k)))
    (hP : (picardFunctorDegree (X ↘ Spec (.of k)) d).obj.RepresentableBy P) :
    ∃ Pg : Over (Spec (.of k)), Nonempty
      ((picardFunctorDegree (X ↘ Spec (.of k)) (arithmeticGenus k X)).obj.RepresentableBy Pg) ∧
      Nonempty (P ≅ Pg) := by
  obtain ⟨A, -, ⟨hA⟩⟩ := isRepresentable_picardFunctor (X ↘ Spec (.of k))
  obtain ⟨Pd, -, -, -, -, -, hPd⟩ := exists_decomposition_picardFunctor A hA
  obtain ⟨hg⟩ := hPd (arithmeticGenus k X)
  exact ⟨_, ⟨hg⟩, nonempty_iso_of_representableBy_picardFunctorDegree d _ P _ hP hg⟩

/-- **The theorem of the base.** Let `X` be a smooth projective curve of genus `g` over a
separably closed field `k`.  Every degree component `Pic^d_{X/k}` of the Picard scheme is proper
over `k`: all of them are isomorphic to `Pic^g_{X/k}`, which is proper by
`AlgebraicGeometry.isProper_of_representableBy_picardFunctorDegree_genus`.

(blueprint: `thm-sc-theorem-of-the-base`) -/
theorem isProper_of_representableBy_picardFunctorDegree (d : ℤ) (P : Over (Spec (.of k)))
    (hP : (picardFunctorDegree (X ↘ Spec (.of k)) d).obj.RepresentableBy P) :
    IsProper P.hom := by
  obtain ⟨Pg, ⟨hg⟩, ⟨e⟩⟩ := exists_iso_representableBy_picardFunctorDegree_genus d P hP
  rw [← Over.w e.hom, MorphismProperty.cancel_left_of_respectsIso (P := @IsProper)]
  exact isProper_of_representableBy_picardFunctorDegree_genus _ hg

/-- **The theorem of the base, smoothness.** Let `X` be a smooth projective curve of genus `g`
over a separably closed field `k`.  Every degree component `Pic^d_{X/k}` of the Picard scheme is
smooth of relative dimension `g` over `k`: all of them are isomorphic to `Pic^g_{X/k}`, which is
smooth of dimension `g` by
`AlgebraicGeometry.smoothOfRelativeDimension_of_representableBy_picardFunctorDegree_genus`.

(blueprint: `thm-sc-theorem-of-the-base`) -/
theorem smoothOfRelativeDimension_of_representableBy_picardFunctorDegree (d : ℤ)
    (P : Over (Spec (.of k)))
    (hP : (picardFunctorDegree (X ↘ Spec (.of k)) d).obj.RepresentableBy P) :
    SmoothOfRelativeDimension (arithmeticGenus k X) P.hom := by
  obtain ⟨Pg, ⟨hg⟩, ⟨e⟩⟩ := exists_iso_representableBy_picardFunctorDegree_genus d P hP
  rw [← Over.w e.hom, MorphismProperty.cancel_left_of_respectsIso
    (P := @SmoothOfRelativeDimension (arithmeticGenus k X))]
  exact smoothOfRelativeDimension_of_representableBy_picardFunctorDegree_genus _ hg

/-- **`Pic^g` is geometrically integral.** A `k`-scheme representing the degree-`g` part
`Pic^g_{X/k}` of the Picard functor, `g` the genus, is geometrically integral over `k`: it is the
image of the geometrically integral `Hilb^g_{X/k}` under `D ↦ 𝒪_X(D)`, so geometrically
irreducible, and it is smooth, hence geometrically reduced.

(blueprint: `sk-prop-jacobian`, connectedness) -/
theorem geometricallyIntegral_of_representableBy_picardFunctorDegree_genus
    (P : Over (Spec (.of k)))
    (hP : (picardFunctorDegree (X ↘ Spec (.of k)) (arithmeticGenus k X)).obj.RepresentableBy P) :
    GeometricallyIntegral P.hom :=
  sorry

/-- **Every degree component is geometrically integral.** A `k`-scheme representing a degree
component `Pic^d_{X/k}` of the Picard functor is geometrically integral over `k`, being isomorphic
to `Pic^g_{X/k}`; in particular the Jacobian `Pic^0_{X/k}` is connected.

(blueprint: `sk-prop-jacobian`, connectedness) -/
theorem geometricallyIntegral_of_representableBy_picardFunctorDegree (d : ℤ)
    (P : Over (Spec (.of k)))
    (hP : (picardFunctorDegree (X ↘ Spec (.of k)) d).obj.RepresentableBy P) :
    GeometricallyIntegral P.hom := by
  obtain ⟨Pg, ⟨hg⟩, ⟨e⟩⟩ := exists_iso_representableBy_picardFunctorDegree_genus d P hP
  rw [← Over.w e.hom, MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyIntegral)]
  exact geometricallyIntegral_of_representableBy_picardFunctorDegree_genus _ hg

end Decomposition

section TangentSpace

variable {k : Type u} [Field k]

/-- The **tangent space** of a `k`-scheme `P` at a `k`-rational point `e`, defined through the
functor of points: it is the fibre over `e` of the restriction map
`P((Spec k)[ε]) → P(k)`, where `(Spec k)[ε] = Spec k[ε]` is the dual-number thickening
`AlgebraicGeometry.Scheme.dualNumbersOver (Spec k)` of `Spec k`, `k[ε] = k[T]/(T²)`, and the map
is induced by the `k`-point `ε ↦ 0` (`AlgebraicGeometry.Scheme.dualNumbersιOver`).

`k`-rational points of `P` are morphisms from the terminal object `𝟙_ (Over (Spec k))` of the
category of `k`-schemes, so that the unit `η[G]` of a group scheme `G` is directly a point in
this sense.  Mathlib has no tangent space of a scheme, so this is a genuine definition rather
than a reuse. At the unit of a group scheme it is a `k`-vector space, its addition being the
group law; see `AlgebraicGeometry.tangentSubgroup`. -/
def tangentSpaceAt (P : Over (Spec (.of k))) (e : 𝟙_ (Over (Spec (.of k))) ⟶ P) : Type u :=
  {v : Scheme.dualNumbersOver (Spec (.of k)) ⟶ P // Scheme.dualNumbersιOver _ ≫ v = e}

variable (k) in
/-- The `k`-endomorphism `ε ↦ cε` of `(Spec k)[ε]` for `c : k`: the scaling
`AlgebraicGeometry.Scheme.dualNumbersScaleOver` by `c` viewed as a global section of `𝒪_{Spec k}`
through `k ≅ Γ(Spec k, 𝒪)`. It defines the scalar action on tangent spaces. -/
noncomputable abbrev dualNumbersScale (c : k) :
    Scheme.dualNumbersOver (Spec (.of k)) ⟶ Scheme.dualNumbersOver (Spec (.of k)) :=
  Scheme.dualNumbersScaleOver (Spec (.of k)) ((Scheme.ΓSpecIso (.of k)).inv.hom c)

@[reassoc (attr := simp)]
lemma dualNumbersιOver_comp_dualNumbersScale (c : k) :
    Scheme.dualNumbersιOver _ ≫ dualNumbersScale k c = Scheme.dualNumbersιOver _ :=
  Scheme.dualNumbersιOver_comp_scaleOver _ _

@[simp]
lemma dualNumbersScale_one : dualNumbersScale k 1 = 𝟙 _ := by
  simp [dualNumbersScale]

@[reassoc]
lemma dualNumbersScale_mul (c d : k) :
    dualNumbersScale k (c * d) = dualNumbersScale k c ≫ dualNumbersScale k d := by
  simp [dualNumbersScale, Scheme.dualNumbersScaleOver_mul]

/-- Scaling by `0` factors through the point `ε ↦ 0`. -/
lemma dualNumbersScale_zero :
    dualNumbersScale k 0 = CartesianMonoidalCategory.toUnit _ ≫ Scheme.dualNumbersιOver _ := by
  simp [dualNumbersScale, Scheme.dualNumbersScaleOver_zero]

section GrpObj

open scoped MonObj

variable (P : Over (Spec (.of k))) [GrpObj P]

/-- The tangent space of a group scheme `P` at the unit, as the kernel of the restriction map
`P(k[ε]) → P(k)` induced by `ε ↦ 0`, a subgroup of the group `P(k[ε])`. -/
def tangentSubgroup : Subgroup (Scheme.dualNumbersOver (Spec (.of k)) ⟶ P) where
  carrier := {v | Scheme.dualNumbersιOver _ ≫ v = η[P]}
  one_mem' := (MonObj.comp_one _).trans (MonObj.one_eq_one (M := P)).symm
  mul_mem' {v w} (hv : _ = _) (hw : _ = _) := by
    rw [Set.mem_ofPred_eq, MonObj.comp_mul, hv, hw, MonObj.one_eq_one, _root_.one_mul]
  inv_mem' {v} (hv : _ = _) := by
    rw [Set.mem_ofPred_eq, GrpObj.comp_inv, hv, MonObj.one_eq_one, _root_.inv_one]

/-- The kernel of `P(k[ε]) → P(k)` is commutative, even when `P` is not. -/
instance : IsMulCommutative (tangentSubgroup P) :=
  sorry

open scoped IsMulCommutative in
/-- The tangent space of a group scheme at the unit is the commutative group
`tangentSubgroup P`, written additively: `v + w` is the group law `⟨v, w⟩ ≫ μ[P]` of
`P(k[ε])`. -/
noncomputable instance : AddCommGroup (tangentSpaceAt P η[P]) :=
  inferInstanceAs (AddCommGroup (Additive (tangentSubgroup P)))

@[simp]
lemma tangentSpaceAt.val_add (v w : tangentSpaceAt P η[P]) : (v + w).1 = v.1 * w.1 :=
  rfl

@[simp]
lemma tangentSpaceAt.val_zero : (0 : tangentSpaceAt P η[P]).1 = 1 :=
  rfl

@[simp]
lemma tangentSpaceAt.val_neg (v : tangentSpaceAt P η[P]) : (-v).1 = v.1⁻¹ :=
  rfl

/-- The scalar action on the tangent space of a group scheme at the unit: `c • v` is `v`
precomposed with the endomorphism `ε ↦ c ε` of `Spec k[ε]`. -/
noncomputable instance : SMul k (tangentSpaceAt P η[P]) where
  smul c v := ⟨dualNumbersScale k c ≫ v.1, by
    rw [dualNumbersιOver_comp_dualNumbersScale_assoc, v.2]⟩

@[simp]
lemma tangentSpaceAt.val_smul (c : k) (v : tangentSpaceAt P η[P]) :
    (c • v).1 = dualNumbersScale k c ≫ v.1 :=
  rfl

/-- The scalar action is additive in the scalar: `(c + d) • v = c • v + d • v`. -/
theorem tangentSpaceAt.add_smul (c d : k) (v : tangentSpaceAt P η[P]) :
    (c + d) • v = c • v + d • v :=
  sorry

/-- The tangent space of a group scheme `P` over `k` at the unit is a `k`-vector space: the
addition is the group law of `P(k[ε])` and `c • v` is `v` precomposed with `ε ↦ c ε`. -/
noncomputable instance : Module k (tangentSpaceAt P η[P]) where
  one_smul v := Subtype.ext (by simp)
  mul_smul c d v := Subtype.ext (by simp [dualNumbersScale_mul])
  smul_zero c := Subtype.ext (MonObj.comp_one _)
  smul_add c v w := Subtype.ext (MonObj.comp_mul _ _ _)
  add_smul := tangentSpaceAt.add_smul P
  zero_smul v := Subtype.ext (by
    rw [tangentSpaceAt.val_smul, dualNumbersScale_zero, Category.assoc, v.2,
      tangentSpaceAt.val_zero, MonObj.one_eq_one, MonObj.comp_one])

end GrpObj

variable {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- **The tangent space of the Jacobian.** Let `X` be a smooth projective curve of genus `g`
over a separably closed field `k` and let `J` be a group scheme over `k` representing the
degree-zero part `Pic^0_{X/k}` of the Picard functor. Then the tangent space of `J` at the unit
`η[J]` is isomorphic as a `k`-vector space to `H^1(X, 𝒪_X)`, which has dimension `g` by the
definition of `AlgebraicGeometry.Scheme.arithmeticGenus`.

(blueprint: `sk-prop-picard-jacobian-tangent`) -/
theorem nonempty_tangentSpaceAt_linearEquiv_H_one [IsSepClosed k]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    [GeometricallyIntegral (X ↘ Spec (.of k))] (J : Over (Spec (.of k))) [GrpObj J]
    (hJ : Nonempty ((picardFunctorDegree (X ↘ Spec (.of k)) 0).obj.RepresentableBy J)) :
    Nonempty (tangentSpaceAt J η[J] ≃ₗ[k] (Modules.unit X).H 1) :=
  sorry

end TangentSpace

section Jacobian

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

variable (k X) in
/-- The degree-zero part `Pic^0(X) = {ℒ ∈ Pic X : deg ℒ = 0}` of the Picard group of a
`k`-scheme `X`, with `AlgebraicGeometry.Scheme.Modules.degree` the cohomological degree
`deg ℒ = χ(ℒ) - χ(𝒪_X)`.  It is only a type, not a group: there is no tensor product of sheaves
of modules, hence no group law on `AlgebraicGeometry.Scheme.Pic`.

(blueprint: `sk-prop-jacobian`) -/
def picardZero : Type (u + 1) :=
  {L : X.Pic // Modules.degree k ((fromSkeleton X.Modules).obj L.val) = 0}

/-- **The `k`-points of `Pic^0_{X/k}`.** For a smooth projective curve `X` over a separably
closed field `k`, the value of the degree-zero part `Pic^0_{X/k}` of the Picard functor on
`Spec k` is `Pic^0(X)`.  By the split exact sequence with `T = Spec k` and `Pic (Spec k) = 0`,
`Pic_{X/k}(k) = Pic X`, and its degree-zero part is `Pic^0(X)`, the fibrewise degree being
invariant under extension of the base field.

(blueprint: `thm-sc-jacobian-representability`, the `k`-points of `Pic^0_{X/k}`) -/
theorem nonempty_picardZero_equiv_picardFunctorDegree_zero [IsSepClosed k]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    [GeometricallyIntegral (X ↘ Spec (.of k))] :
    Nonempty (picardZero k X ≃
      (picardFunctorDegree (X ↘ Spec (.of k)) 0).obj.obj (.op (𝟙_ (Over (Spec (.of k)))))) :=
  sorry

/-- **The Jacobian is an abelian variety.** Let `X` be a smooth projective curve of genus `g`
over a separably closed field `k`.  Then there is a `k`-scheme `J` carrying a commutative group
scheme structure which is proper, smooth of relative dimension `g` and geometrically integral
over `k`, which represents the degree-zero part `Pic^0_{X/k}` of the Picard functor, and whose
set of `k`-rational points is in bijection with `Pic^0(X)`.

The tangent space clause `T_e J ≅ H^1(X, 𝒪_X)` is
`AlgebraicGeometry.nonempty_tangentSpaceAt_linearEquiv_H_one` and is not repeated here; the
base-change clause `J(X_{k'}) = J(X) ×_k k'` for `k ⊆ k'` algebraically closed is omitted, the
corresponding compatibility over a general base field being part of
`AlgebraicGeometry.exists_jacobian_descent`.

(blueprint: `sk-prop-jacobian`) -/
theorem exists_jacobian [IsSepClosed k]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    [GeometricallyIntegral (X ↘ Spec (.of k))] :
    ∃ (J : Over (Spec (.of k))) (_ : CommGrpObj J),
      IsProper J.hom ∧ SmoothOfRelativeDimension (arithmeticGenus k X) J.hom ∧
        GeometricallyIntegral J.hom ∧
        Nonempty ((picardFunctorDegree (X ↘ Spec (.of k)) 0).obj.RepresentableBy J) ∧
        Nonempty (picardZero k X ≃ (𝟙_ (Over (Spec (.of k))) ⟶ J)) := by
  obtain ⟨A, -, ⟨hA⟩⟩ := isRepresentable_picardFunctor (X ↘ Spec (.of k))
  obtain ⟨Pd, -, -, -, -, -, hPd⟩ := exists_decomposition_picardFunctor A hA
  obtain ⟨h₀⟩ := hPd 0
  obtain ⟨e⟩ := nonempty_picardZero_equiv_picardFunctorDegree_zero (k := k) (X := X)
  exact ⟨Pd 0, (nonempty_commGrpObj_of_representableBy _ h₀).some,
    isProper_of_representableBy_picardFunctorDegree 0 _ h₀,
    smoothOfRelativeDimension_of_representableBy_picardFunctorDegree 0 _ h₀,
    geometricallyIntegral_of_representableBy_picardFunctorDegree 0 _ h₀, ⟨h₀⟩,
    ⟨e.trans h₀.homEquiv.symm⟩⟩

end Jacobian

section Descent

/-- A `k`-algebra automorphism `σ` of `K`, viewed as an automorphism of the `k`-scheme
`Spec K`.  Base changing along it is the geometric form of the Galois action. -/
noncomputable def specAlgEquivOver {k K : Type u} [CommRing k] [CommRing K] [Algebra k K]
    (σ : K ≃ₐ[k] K) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext x
    exact σ.commutes x)

variable {k : Type u} [Field k]

/-- **The degree-zero Picard functor over a separable closure.** Let `C` be a smooth projective
geometrically integral curve of genus `g` over `k` and let `k_s` be a separable closure of `k`.
Then `Pic^0_{C_{k_s}/k_s}` is represented by an abelian variety `J_s` of dimension `g` over
`k_s`, whose `k_s`-points are `Pic^0(C_{k_s})`.

(blueprint: `thm-pd-geometric-pic0`) -/
theorem exists_jacobian_pullback (ks : Type u) [Field ks] [Algebra k ks] [IsSepClosure k ks]
    (C : Scheme.{u}) [C.Over (Spec (.of k))] [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))]
    [IsProper (C ↘ Spec (.of k))] [GeometricallyIntegral (C ↘ Spec (.of k))] (g : ℕ)
    (hg : arithmeticGenus k C = g) :
    ∃ (J : Over (Spec (.of ks))) (_ : CommGrpObj J),
      IsProper J.hom ∧ SmoothOfRelativeDimension g J.hom ∧ GeometricallyIntegral J.hom ∧
        Nonempty ((picardFunctorDegree
          (pullback (C ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k ks))) ↘
            Spec (.of ks)) 0).obj.RepresentableBy J) ∧
        Nonempty (picardZero ks
            (pullback (C ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k ks)))) ≃
          (𝟙_ (Over (Spec (.of ks))) ⟶ J)) := by
  -- The base change of `C` to `k_s` is a smooth projective geometrically integral curve of
  -- genus `g` over the separably closed field `k_s` (blueprint `lem-pd-geometric-curve`).
  have : IsSepClosed ks := IsSepClosure.sep_closed k
  have : SmoothOfRelativeDimension 1 (pullback (C ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k ks))) ↘ Spec (.of ks)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (pullback.snd _ _))
  have : IsProper (pullback (C ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k ks))) ↘ Spec (.of ks)) :=
    inferInstanceAs (IsProper (pullback.snd _ _))
  have : GeometricallyIntegral (pullback (C ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k ks))) ↘ Spec (.of ks)) :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd _ _))
  rw [← hg, ← arithmeticGenus_pullback ks]
  exact exists_jacobian (k := ks)

/-- **The degree-zero part is compatible with base change.** Let `C` be a smooth projective
geometrically integral curve over `k`, let `K/k` be a field extension and let `C_K` be the base
change of `C`, presented by a cartesian square. Then the restriction of `Pic^0_{C/k}` to schemes
over `K` is `Pic^0_{C_K/K}`.

This follows from the compatibility of the Picard functor with base change
(`AlgebraicGeometry.nonempty_picardFunctor_iso_of_isPullback`), the fibrewise degree of a class
being computed on the same fibres in both cases.

The blueprint asserts that the restriction *is* `Pic^0_{C_K/K}`, through the canonical
identification. The statement here only asserts that some isomorphism exists, which is weaker;
this suffices for the current applications.

(blueprint: `cor-pd-pic0-base-change`) -/
theorem nonempty_picardFunctorDegree_iso_of_isPullback {K : Type u} [Field K] [Algebra k K]
    {C C' : Scheme.{u}} [C.Over (Spec (.of k))] [C'.Over (Spec (.of K))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))] [IsProper (C ↘ Spec (.of k))]
    [GeometricallyIntegral (C ↘ Spec (.of k))] (q : C' ⟶ C)
    (h : IsPullback q (C' ↘ Spec (.of K)) (C ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (d : ℤ) :
    Nonempty ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).op ⋙
      (picardFunctorDegree (C ↘ Spec (.of k)) d).obj ≅
        (picardFunctorDegree (C' ↘ Spec (.of K)) d).obj) :=
  ⟨((sheafToPresheaf _ _).mapIso ((presheafToSheaf _ _).mapIso
    (picardSubfunctorDegreeIsoOfIsPullback h d).symm ≪≫
      Functor.sheafifyCompIso _ _ (Over.map _) _)).symm⟩

omit [Field k] in
lemma specMap_algebraMap_comp_specMap_algebraMap (k K L : Type u) [CommRing k] [CommRing K]
    [CommRing L] [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L] :
    Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) =
      Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- **The descent datum is defined at a finite separable level.** Let `C` be a smooth projective
geometrically integral curve over `k`, let `k_s` be a separable closure of `k` and let `J_s`
represent the restriction of `Pic^0_{C/k}` to schemes over `k_s`, so that `J_s` carries the
canonical descent datum `φ` relative to `Spec k_s ⟶ Spec k`
(`CategoryTheory.Functor.RepresentableBy.overDescentDatum`). Then there are a finite separable
subextension `K` of `k_s/k`, a `K`-scheme `J_K` with `J_K ×_K k_s ≅ J_s`, and a descent datum
`φ_K` on `J_K` relative to `Spec K ⟶ Spec k` whose base change to `k_s` is `φ`. Moreover every
finite set of points of `J_K` lies in an affine open, `J_K` being projective over `K`.

The proof spreads `J_s`, the isomorphism `φ` and a closed immersion `J_s ⟶ ℙ^N` out to a finite
level (Stacks 01ZM: `AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation`,
`AlgebraicGeometry.Scheme.exists_pullback_hom_of_isLimit` and
`AlgebraicGeometry.Scheme.exists_pullback_fst_comp_eq_of_isLimit`), the cocycle condition
holding at a finite level because it holds over `k_s`.

(blueprint: `cor-pd-finite-level`) -/
theorem exists_intermediateField_descentDatum {ks : Type u} [Field ks] [Algebra k ks]
    [IsSepClosure k ks] (C : Scheme.{u}) [C.Over (Spec (.of k))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))] [IsProper (C ↘ Spec (.of k))]
    [GeometricallyIntegral (C ↘ Spec (.of k))] (Js : Over (Spec (.of ks)))
    (rs : ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k ks)))).op ⋙
      (picardFunctorDegree (C ↘ Spec (.of k)) 0).obj).RepresentableBy Js) :
    ∃ (K : IntermediateField k ks), FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
      ∃ (JK : Over (Spec (.of K))) (q : Js.left ⟶ JK.left)
        (hq : IsPullback q Js.hom JK.hom (Spec.map (CommRingCat.ofHom (algebraMap K ks))))
        (D : Over.DescentDatum (Spec.map (CommRingCat.ofHom (algebraMap k K))) JK),
        D.IsBaseChange (specMap_algebraMap_comp_specMap_algebraMap k K ks) hq.w
            rs.overDescentDatum ∧
          ∀ s : Set JK.left, s.Finite → ∃ U : JK.left.Opens, IsAffineOpen U ∧ s ⊆ U :=
  sorry

/-- **The group law is compatible with the descent datum at a finite level.** Let `k ⊆ K ⊆ k_s`
be field extensions, let `J_s` represent the restriction of `Pic^0_{C/k}` to schemes over `k_s`
and let `J_K` be a `K`-scheme with `J_K ×_K k_s ≅ J_s`, carrying a descent datum `φ_K` relative to
`Spec K ⟶ Spec k` whose base change to `k_s` is the canonical descent datum of `J_s`. Then `J_K`
carries a commutative group scheme structure whose multiplication and unit are compatible with
`φ_K`.

The group law of `Pic^0_{C/k}` makes `J_s` a commutative group scheme over `k_s` compatible with
its canonical descent datum, since transport does not change the element of `Pic^0_{C/k}(T)` that
a point stands for. Restricted to `Spec k_s ⟶ Spec K`, that datum is the one induced by `J_K`, so
the group law descends to `J_K` (`CategoryTheory.Over.DescentDatum.exists_commGrpObj_of_isPullback`
along `Spec k_s ⟶ Spec K`), and it is compatible with `φ_K` because it is so after the faithfully
flat base change to `k_s`. This is Step 5 of the proof of
`AlgebraicGeometry.exists_jacobian_descent`; it is stated separately because
`AlgebraicGeometry.Scheme.Pic` carries no group law here. -/
theorem exists_commGrpObj_of_isBaseChange {K ks : Type u} [Field K] [Field ks] [Algebra k K]
    [Algebra K ks] [Algebra k ks] [IsScalarTower k K ks] (C : Scheme.{u}) [C.Over (Spec (.of k))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))] [IsProper (C ↘ Spec (.of k))]
    [GeometricallyIntegral (C ↘ Spec (.of k))] (Js : Over (Spec (.of ks)))
    (rs : ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k ks)))).op ⋙
      (picardFunctorDegree (C ↘ Spec (.of k)) 0).obj).RepresentableBy Js)
    (JK : Over (Spec (.of K))) (q : Js.left ⟶ JK.left)
    (hq : IsPullback q Js.hom JK.hom (Spec.map (CommRingCat.ofHom (algebraMap K ks))))
    (D : Over.DescentDatum (Spec.map (CommRingCat.ofHom (algebraMap k K))) JK)
    (hD : D.IsBaseChange (specMap_algebraMap_comp_specMap_algebraMap k K ks) hq.w
      rs.overDescentDatum) :
    ∃ _ : CommGrpObj JK,
      (∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ Spec (.of K))
        (h : f₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) =
          f₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))) (a b : Over.mk f₁ ⟶ JK),
        D.transport f₁ f₂ h (CartesianMonoidalCategory.lift a b ≫ μ[JK]) =
          CartesianMonoidalCategory.lift (D.transport f₁ f₂ h a) (D.transport f₁ f₂ h b) ≫
            μ[JK]) ∧
      ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ Spec (.of K))
        (h : f₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) =
          f₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))),
        D.transport f₁ f₂ h (CartesianMonoidalCategory.toUnit _ ≫ η[JK]) =
          CartesianMonoidalCategory.toUnit _ ≫ η[JK] :=
  sorry

/-- **`Pic^0_{C/k}` is represented by the descended scheme.** Let `K/k` be a field extension, let
`J_K` represent the restriction of `Pic^0_{C/k}` to schemes over `K`, and let `J` be a `k`-scheme
with `J ×_k K ≅ J_K` through which the canonical descent datum of `J_K` relative to
`Spec K ⟶ Spec k` is the trivial one: the projection `q : J_K ⟶ J` is invariant under transport.
Then `J` represents `Pic^0_{C/k}`.

This is Step 7 of the proof of `AlgebraicGeometry.exists_jacobian_descent`, applied with
`K = k_s`. The morphism `Spec K ⟶ Spec k` is faithfully flat and quasi-compact but in general not
locally of finite presentation, so this does not follow from the fppf sheaf property of
`Pic^0_{C/k}` alone. Since `Pic^0_{C/k}` and `J` are locally of finite presentation, the
identification of `Pic^0_{C/k}` with `h_J` over `K` is defined over a finitely generated
subalgebra `A ⊆ K` (Stacks 01ZC), along which fppf descent of sections applies; equivalently, by
fpqc descent of morphisms (Stacks 02W0) it agrees with the representing object of `Pic^0_{C/k}`.

(blueprint: `thm-pd-jacobian-general-field`, Step 7) -/
theorem nonempty_representableBy_picardFunctorDegree_of_isPullback {K : Type u} [Field K]
    [Algebra k K] (C : Scheme.{u}) [C.Over (Spec (.of k))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))] [IsProper (C ↘ Spec (.of k))]
    [GeometricallyIntegral (C ↘ Spec (.of k))] (JK : Over (Spec (.of K)))
    (r : ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).op ⋙
      (picardFunctorDegree (C ↘ Spec (.of k)) 0).obj).RepresentableBy JK)
    (J : Over (Spec (.of k))) (q : JK.left ⟶ J.left)
    (hq : IsPullback q JK.hom J.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hinv : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ Spec (.of K))
      (h : f₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) =
        f₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))) (a : Over.mk f₁ ⟶ JK),
      (r.overTransport f₁ f₂ h a).left ≫ q = a.left ≫ q) :
    Nonempty ((picardFunctorDegree (C ↘ Spec (.of k)) 0).obj.RepresentableBy J) :=
  sorry

/-- Over an algebraically closed field `K`, every fppf covering sieve of `Spec K`, viewed as a
scheme over `S`, contains the identity: it contains a nonempty `K`-scheme locally of finite type,
which has a `K`-point by the Nullstellensatz. -/
lemma id_mem_of_mem_fppfTopology_over_of_isAlgClosed {S : Scheme.{u}} {K : Type u} [Field K]
    [IsAlgClosed K] (φ : Spec (.of K) ⟶ S) {R : Sieve (Over.mk φ)}
    (hR : R ∈ fppfTopology.over S (Over.mk φ)) : R (𝟙 _) := by
  obtain ⟨s⟩ : Nonempty (Spec (.of K)) := inferInstance
  obtain ⟨Z, g, hg, -, hg₂, z, -⟩ := exists_flat_mem_of_mem_fppfTopology_over hR s
  have : JacobsonSpace (Over.mk φ).left := inferInstanceAs (JacobsonSpace (Spec (.of K)))
  have : JacobsonSpace Z.left := LocallyOfFiniteType.jacobsonSpace g.left
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints ⟨z, Set.mem_univ z⟩
    (isClosed_univ (X := Z.left)).isLocallyClosed
  have hσ : Over.homMk (pointOfClosedPoint g.left x hx)
      (by rw [← Over.w g, pointOfClosedPoint_comp_assoc]) ≫ g = 𝟙 (Over.mk φ) := by
    ext1
    exact pointOfClosedPoint_comp g.left x hx
  rw [← hσ]
  exact R.downward_closed hg _

/-- The degree of an invertible module on a proper scheme over a field `K` is the difference of
the fibre Euler characteristics of the module and of the structure sheaf at the point of
`Spec K`. -/
lemma degree_eq_eulerCharFiber_sub {K : Type u} [Field K] {C : Scheme.{u}} [C.Over (Spec (.of K))]
    [IsProper (C ↘ Spec (.of K))] (L : C.Pic) (s : Spec (.of K)) :
    Modules.degree K ((fromSkeleton _).obj L.val) =
      Modules.eulerCharFiber ((fromSkeleton _).obj L.val) (C ↘ Spec (.of K)) s -
        Modules.eulerCharFiber (SheafOfModules.unit C.ringCatSheaf) (C ↘ Spec (.of K)) s := by
  have := Pic.isInvertible L
  have : ((fromSkeleton _).obj L.val).IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  have : (SheafOfModules.unit C.ringCatSheaf).IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  rw [Modules.degree, Modules.eulerCharFiber_eq_eulerChar, Modules.eulerCharFiber_eq_eulerChar]

/-- **The geometric points of `Pic^0_{C₀/k₀}`.** Let `C₀` be a smooth projective geometrically
integral curve over `k₀`, let `K` be an algebraically closed extension of `k₀` and let `C` be the
base change of `C₀` to `K`. Then the value of `Pic^0_{C₀/k₀}` on `Spec K` is `Pic^0(C)`, and the
identification is equivariant: for a `k₀`-automorphism `σ` of `K`, the automorphism `γ` of `C`
over `C₀` lying over `Spec σ` acts on `Pic^0(C)` by pullback, and this corresponds to the action of
`Spec σ` on `Pic^0_{C₀/k₀}(Spec K)`.

Since `C` has a `K`-point, `Pic(C) ⟶ Pic_{C/K}(K)` is bijective
(`AlgebraicGeometry.bijective_pic_split` with `Pic(Spec K) = 0`), every fppf covering of `Spec K`
having a section; the fibrewise degree of a class over the point `Spec K` is its degree on `C`.
Both maps are natural in `Spec K`, which gives the equivariance. These are Steps 9 and 10 of the
proof of `AlgebraicGeometry.exists_jacobian_descent`. -/
theorem exists_picardZero_equiv_picardFunctorDegree {k₀ K : Type u} [Field k₀] [Field K]
    [Algebra k₀ K] [IsAlgClosed K] (C₀ : Scheme.{u}) [C₀.Over (Spec (.of k₀))]
    [SmoothOfRelativeDimension 1 (C₀ ↘ Spec (.of k₀))] [IsProper (C₀ ↘ Spec (.of k₀))]
    [GeometricallyIntegral (C₀ ↘ Spec (.of k₀))] (C : Scheme.{u}) [C.Over (Spec (.of K))]
    (p : C ⟶ C₀)
    (hC : IsPullback p (C ↘ Spec (.of K)) (C₀ ↘ Spec (.of k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) :
    ∃ Φ : picardZero K C ≃ (picardFunctorDegree (C₀ ↘ Spec (.of k₀)) 0).obj.obj
        (.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))),
      ∀ σ : K ≃ₐ[k₀] K, ∃ γ : C ⟶ C, γ ≫ p = p ∧
        γ ≫ (C ↘ Spec (.of K)) = (C ↘ Spec (.of K)) ≫
          Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ∧
        ∃ act : picardZero K C → picardZero K C,
          (∀ L, (act L).1 = Pic.map γ L.1) ∧
            ∀ L, Φ (act L) =
            (picardFunctorDegree (C₀ ↘ Spec (.of k₀)) 0).obj.map (specAlgEquivOver σ).op (Φ L) := by
  have : IsProper (C ↘ Spec (.of K)) := MorphismProperty.of_isPullback (P := @IsProper) hC ‹_›
  have : LocallyOfFinitePresentation (C ↘ Spec (.of K)) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hC inferInstance
  obtain ⟨s⟩ : Nonempty (Spec (.of K)) := inferInstance
  let T₀ := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))
  let ψ := hC.isoPullback
  -- Step 10: a class on `C` has degree `0` iff its transport to `C₀ ×_{k₀} K` lies in the
  -- degree-zero subfunctor.
  have hdeg (L : C.Pic) (t : T₀.left) :
      picardPresheafDegree (C₀ ↘ Spec (.of k₀)) (T := T₀) (Pic.map ψ.inv L) t =
        Modules.degree K ((fromSkeleton _).obj L.val) := by
    rw [degree_eq_eulerCharFiber_sub L t]
    exact eulerCharFiber_sub_eulerCharFiber_unit_map_of_isPullback
      (IsPullback.of_horiz_isIso ⟨by simp [ψ]⟩ :
        IsPullback ψ.inv (pullback.snd _ _) (C ↘ Spec (.of K)) (𝟙 _)) L t
  let e₀ : picardZero K C ≃
      (picardSubfunctorDegree (C₀ ↘ Spec (.of k₀)) 0).toFunctor.obj (.op T₀) :=
    Equiv.subtypeEquiv
      ⟨Pic.map ψ.inv, Pic.map ψ.hom,
        fun L ↦ by rw [← Pic.map_comp, Iso.hom_inv_id, Pic.map_id],
        fun L ↦ by rw [← Pic.map_comp, Iso.inv_hom_id, Pic.map_id]⟩
      fun L ↦ by
        rw [mem_picardSubfunctorDegree_iff]
        exact ⟨fun h t ↦ (hdeg L t).trans h, fun h ↦ (hdeg L s).symm.trans (h s)⟩
  -- Step 9: every fppf covering of `Spec K` has a section, so the sections of the
  -- sheafification over `Spec K` are those of the subfunctor.
  let e₁ := Equiv.ofBijective _ (Presheaf.bijective_app_of_forall_mem
    (fppfTopology.over (Spec (.of k₀)))
    (toSheafify (fppfTopology.over (Spec (.of k₀)))
      (picardSubfunctorDegree (C₀ ↘ Spec (.of k₀)) 0).toFunctor) (X := T₀)
    fun _ hR ↦ id_mem_of_mem_fppfTopology_over_of_isAlgClosed _ hR)
  refine ⟨e₀.trans e₁, fun σ ↦ ?_⟩
  -- the automorphism `γ` of `C` over `C₀` lying over `Spec σ`
  have hσg : Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k₀ K)) =
        Spec.map (CommRingCat.ofHom (algebraMap k₀ K)) :=
    Over.w (specAlgEquivOver σ)
  let γ : C ⟶ C := hC.lift p ((C ↘ Spec (.of K)) ≫
    Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom)) (by rw [Category.assoc, hσg, hC.w])
  have hγp : γ ≫ p = p := hC.lift_fst _ _ _
  have hγs : γ ≫ (C ↘ Spec (.of K)) =
      (C ↘ Spec (.of K)) ≫ Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) :=
    hC.lift_snd _ _ _
  have hγ : IsPullback γ (C ↘ Spec (.of K)) (C ↘ Spec (.of K))
      (Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom)) :=
    IsPullback.of_right (by rwa [hγp, hσg]) hγs hC
  have hdegγ (L : C.Pic) : Modules.degree K ((fromSkeleton _).obj (Pic.map γ L).val) =
      Modules.degree K ((fromSkeleton _).obj L.val) := by
    rw [degree_eq_eulerCharFiber_sub _ s, degree_eq_eulerCharFiber_sub L
      ((Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom)) s)]
    exact eulerCharFiber_sub_eulerCharFiber_unit_map_of_isPullback hγ L s
  have hbc : baseChangeMap (C₀ ↘ Spec (.of k₀)) (specAlgEquivOver σ) ≫ ψ.inv = ψ.inv ≫ γ := by
    refine hC.hom_ext ?_ ?_
    · simp [ψ, hγp, baseChangeMap]
    · simp [ψ, hγs, baseChangeMap, specAlgEquivOver]
  refine ⟨γ, hγp, hγs, fun L ↦ ⟨Pic.map γ L.1, (hdegγ L.1).trans L.2⟩, fun L ↦ rfl, fun L ↦ ?_⟩
  refine Eq.trans ?_ (NatTrans.naturality_apply (toSheafify (fppfTopology.over (Spec (.of k₀)))
    (picardSubfunctorDegree (C₀ ↘ Spec (.of k₀)) 0).toFunctor) (specAlgEquivOver σ).op (e₀ L))
  have key : Pic.map ψ.inv (Pic.map γ L.1) =
      Pic.map (baseChangeMap _ (specAlgEquivOver σ)) (Pic.map ψ.inv L.1) := by
    rw [← Pic.map_comp, ← hbc, Pic.map_comp]
  exact congrArg e₁ (Subtype.ext key)

omit [Field k] in
lemma isFinite_specMap_algebraMap (k K : Type u) [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
  IsFinite.SpecMap_iff _ |>.mpr (RingHom.finite_algebraMap.mpr inferInstance)

omit [Field k] in
lemma flat_specMap_algebraMap (k K : Type u) [Field k] [CommRing K] [Algebra k K] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
  Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)

omit [Field k] in
lemma locallyOfFinitePresentation_specMap_algebraMap (k K : Type u) [Field k] [Field K]
    [Algebra k K] [FiniteDimensional k K] :
    LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  exact RingHom.FinitePresentation.of_finiteType.mp
    (RingHom.finite_algebraMap.mpr inferInstance).finiteType

omit [Field k] in
lemma surjective_specMap_algebraMap (k K : Type u) [Field k] [Field K] [Algebra k K] :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
  ⟨fun _ ↦ ⟨default, Subsingleton.elim _ _⟩⟩

/-- **The Jacobian over an arbitrary ground field, as a representing object.** Let `C` be a smooth
projective geometrically integral curve of genus `g` over a field `k`. Then `Pic^0_{C/k}` is
represented by an abelian variety of dimension `g` over `k`. No rational point of `C` is assumed.

This is Steps 1–7 of the proof of `AlgebraicGeometry.exists_jacobian_descent`: the Jacobian of
`C_{k_s}` carries the canonical descent datum, which is defined at a finite separable level `K`,
is effective there, and descends the group law and the geometric properties to `k`.

(blueprint: `thm-pd-jacobian-general-field`) -/
theorem exists_commGrpObj_representableBy_picardFunctorDegree (ks : Type u) [Field ks]
    [Algebra k ks] [IsSepClosure k ks] (C : Scheme.{u}) [C.Over (Spec (.of k))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))] [IsProper (C ↘ Spec (.of k))]
    [GeometricallyIntegral (C ↘ Spec (.of k))] (g : ℕ) (hg : arithmeticGenus k C = g) :
    ∃ (J : Over (Spec (.of k))) (_ : CommGrpObj J),
      IsProper J.hom ∧ SmoothOfRelativeDimension g J.hom ∧ GeometricallyIntegral J.hom ∧
        Nonempty ((picardFunctorDegree (C ↘ Spec (.of k)) 0).obj.RepresentableBy J) := by
  -- Step 1: the Jacobian `J_s` of `C_{k_s}` represents the restriction of `Pic^0_{C/k}`.
  obtain ⟨Js, _, hJsP, hJsS, hJsG, ⟨rJs⟩, -⟩ := exists_jacobian_pullback ks C g hg
  obtain ⟨e⟩ := nonempty_picardFunctorDegree_iso_of_isPullback (K := ks) (C := C)
    (C' := pullback (C ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k ks))))
    (pullback.fst _ _) (IsPullback.of_hasPullback _ _) 0
  -- Steps 2 and 3: its canonical descent datum is defined at a finite separable level `K`.
  obtain ⟨K, _, _, JK, q', hq', D, hD, hJK⟩ :=
    exists_intermediateField_descentDatum C Js (rJs.ofIso e.symm)
  have := isFinite_specMap_algebraMap k K
  have := flat_specMap_algebraMap k K
  have := locallyOfFinitePresentation_specMap_algebraMap k K
  have := surjective_specMap_algebraMap k K
  -- Step 4: the descent datum `φ_K` is effective, with descended scheme `J`.
  obtain ⟨J, q, hq, hinv⟩ := D.isEffective_of_isFinite hJK
  -- Step 5: the group law descends.
  obtain ⟨_, hμ, hη⟩ := exists_commGrpObj_of_isBaseChange C Js (rJs.ofIso e.symm) JK q' hq' D hD
  obtain ⟨_, -⟩ := D.exists_commGrpObj_of_isPullback q hq hinv hμ hη
  -- Step 7: `J` represents `Pic^0_{C/k}`, since `J ×_k k_s ≅ J_s` compatibly with the canonical
  -- descent datum of `J_s`.
  have hs := specMap_algebraMap_comp_specMap_algebraMap k K ks
  have hJ : IsPullback (q' ≫ q) Js.hom J.hom (Spec.map (CommRingCat.ofHom (algebraMap k ks))) :=
    hs ▸ hq'.paste_horiz hq
  obtain ⟨r⟩ := nonempty_representableBy_picardFunctorDegree_of_isPullback C Js
    (rJs.ofIso e.symm) J (q' ≫ q) hJ fun f₁ f₂ h a ↦ by
      rw [← Category.assoc, ← Functor.RepresentableBy.overDescentDatum_transport, ← hD f₁ f₂ h a,
        hinv]
      simp
  -- Step 6: the geometric properties descend along `k ⊆ k_s`.
  obtain ⟨hP, hS, hG⟩ := isProper_smoothOfRelativeDimension_geometricallyIntegral_of_isPullback
    J.hom Js.hom (q' ≫ q) hJ g
  exact ⟨J, inferInstance, hP, hS, hG, ⟨r⟩⟩

/-- **The Jacobian over a general base field, by Galois descent.** Let `k₀` be any field, `k_s` a
separable closure of `k₀`, `k̄₀` an algebraic closure of `k₀` containing `k_s`, and let `C₀` be a
proper smooth geometrically connected curve of genus `g` over `k₀`.  Let `C` be the base change
`C₀ ×_{k₀} k̄₀`, presented by a cartesian square.  Then the Jacobian of `C` descends to `k₀`:
there is a `k₀`-scheme `J₀` carrying a commutative group scheme structure, proper, smooth of
relative dimension `g` and geometrically integral over `k₀`, whose base change `J₀ ×_{k₀} k̄₀`
represents `Pic^0_{C/k̄₀}`, and whose `k̄₀`-points are in bijection with `Pic^0(C)`.  The
bijection is equivariant: every `k₀`-algebra automorphism `σ` of `k̄₀` induces the automorphism
`γ` of `C` over `C₀` lying over `Spec σ`, base change along `γ` preserves `Pic^0(C)`, and the
bijection intertwines that action with the action on `k̄₀`-points by precomposition with
`AlgebraicGeometry.specAlgEquivOver σ`.

No rational point of `C₀` is assumed.

(blueprint: `sk-prop-jacobian-descent`) -/
theorem exists_jacobian_descent (k₀ ks K : Type u) [Field k₀] [Field ks] [Field K]
    [Algebra k₀ ks] [Algebra k₀ K] [Algebra ks K] [IsScalarTower k₀ ks K]
    [IsSepClosure k₀ ks] [IsAlgClosure k₀ K] (C₀ : Scheme.{u}) [C₀.Over (Spec (.of k₀))]
    [SmoothOfRelativeDimension 1 (C₀ ↘ Spec (.of k₀))] [IsProper (C₀ ↘ Spec (.of k₀))]
    [GeometricallyConnected (C₀ ↘ Spec (.of k₀))] (g : ℕ) (hg : arithmeticGenus k₀ C₀ = g)
    (C : Scheme.{u}) [C.Over (Spec (.of K))] (p : C ⟶ C₀)
    (hC : IsPullback p (C ↘ Spec (.of K)) (C₀ ↘ Spec (.of k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) :
    ∃ (J₀ : Over (Spec (.of k₀))) (_ : CommGrpObj J₀),
      IsProper J₀.hom ∧ SmoothOfRelativeDimension g J₀.hom ∧ GeometricallyIntegral J₀.hom ∧
        Nonempty ((picardFunctorDegree (C ↘ Spec (.of K)) 0).obj.RepresentableBy
          (Over.mk (Limits.pullback.snd J₀.hom
            (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))))) ∧
        ∃ e : picardZero K C ≃
            (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) ⟶ J₀),
          ∀ σ : K ≃ₐ[k₀] K, ∃ γ : C ⟶ C, γ ≫ p = p ∧
            γ ≫ (C ↘ Spec (.of K)) = (C ↘ Spec (.of K)) ≫
              Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ∧
            ∃ act : picardZero K C → picardZero K C,
              (∀ L, (act L).1 = Pic.map γ L.1) ∧
                ∀ L, e (act L) = specAlgEquivOver σ ≫ e L := by
  -- A smooth geometrically connected curve is geometrically integral.
  have : Smooth (C₀ ↘ Spec (.of k₀)) := SmoothOfRelativeDimension.smooth 1 _
  have := GeometricallyIrreducible.of_smooth_of_geometricallyConnected (C₀ ↘ Spec (.of k₀))
  have : GeometricallyIntegral (C₀ ↘ Spec (.of k₀)) :=
    .of_geometricallyReduced_of_geometricallyIrreducible _
  -- Steps 1–7: the Jacobian `J₀` over `k₀`.
  obtain ⟨J₀, _, hP, hS, hG, ⟨r⟩⟩ :=
    exists_commGrpObj_representableBy_picardFunctorDegree ks C₀ g hg
  -- Step 8: its base change to `K` represents `Pic^0_{C/K}`.
  obtain ⟨e⟩ := nonempty_picardFunctorDegree_iso_of_isPullback p hC 0
  -- Steps 9–11: the geometric points, equivariantly.
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed k₀
  obtain ⟨Φ, hΦ⟩ := exists_picardZero_equiv_picardFunctorDegree C₀ C p hC
  refine ⟨J₀, inferInstance, hP, hS, hG, ⟨(r.ofAdjunction (Over.mapPullbackAdj _)).ofIso e⟩,
    Φ.trans r.homEquiv.symm, fun σ ↦ ?_⟩
  obtain ⟨γ, hγp, hγ, act, hact, hΦσ⟩ := hΦ σ
  refine ⟨γ, hγp, hγ, act, hact, fun L ↦ r.homEquiv.injective ?_⟩
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply, r.homEquiv_comp, hΦσ]

end Descent

end AlgebraicGeometry
