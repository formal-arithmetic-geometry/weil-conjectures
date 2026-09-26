/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
public import WeilConjectures.AlgebraicGeometry.Picard.Representability

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

## Design notes

There is no tensor product of sheaves of modules, no twisting sheaf `𝒪_X(D)` and no group law on
`AlgebraicGeometry.Scheme.Pic` in this project, and there is no tangent space of a scheme and no
`AbelianVariety` class anywhere.  Each statement below therefore renders the blueprint clause in
the closest expressible form, and each docstring records exactly what had to be dropped.

The fibrewise degree of a class `ℒ ∈ Pic (X_T)` is measured by pulling `ℒ` back to the fibre
`X_K` over a field-valued point `Spec K → T` and taking
`AlgebraicGeometry.Scheme.Modules.degree`, the cohomological degree `χ(ℒ) - χ(𝒪)` of
`WeilConjectures/AlgebraicGeometry/Curve/RiemannRoch.lean`.

## Main definitions

- `AlgebraicGeometry.picardFibreDegree`: the degree of a relative Picard class on the fibre over
  a field-valued point of the base.
- `AlgebraicGeometry.picardSubfunctorDegree`: the degree-`d` subfunctor of the Picard presheaf.
- `AlgebraicGeometry.picardFunctorDegree`: the degree-`d` part `Pic^d_{X/k}` of the relative
  Picard functor.
- `AlgebraicGeometry.dualNumbersOver`: `Spec k[ε]` as a `k`-scheme, `k[ε] = k[T]/(T²)`.
- `AlgebraicGeometry.dualNumbersZero`: the `k`-point `ε ↦ 0` of `Spec k[ε]`.
- `AlgebraicGeometry.tangentSpaceAt`: the tangent space of a `k`-scheme at a `k`-rational point,
  defined through the functor of points.
- `AlgebraicGeometry.specAlgEquivOver`: a `k`-algebra automorphism of `K` as an automorphism of
  the `k`-scheme `Spec K`.

## Main statements

- `AlgebraicGeometry.exists_decomposition_picardFunctor`: the degree decomposition of the Picard
  scheme (blueprint `sk-prop-picard-degree-decomposition`).
- `AlgebraicGeometry.nonempty_tangentSpaceAt_equiv_H_one`: the tangent space of the Jacobian
  (blueprint `sk-prop-picard-jacobian-tangent`).
- `AlgebraicGeometry.exists_jacobian`: the Jacobian is an abelian variety (blueprint
  `sk-prop-jacobian`).
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

/-- Blueprint `sk-prop-picard-degree-decomposition`: Degree decomposition of the Picard scheme

The degree of a relative Picard class on a fibre.  Let `f : X ⟶ Spec k` be a `k`-scheme, let `T`
be a `k`-scheme and let `L ∈ Pic (X_T)` be a section of the Picard presheaf over `T`.  A
field-valued point `t : Spec K ⟶ T` of `T` cuts out the fibre `X_K = X ×_{Spec k} Spec K`, and
`picardFibreDegree f L t` is the degree `deg ℒ_t = χ(ℒ_t) - χ(𝒪_{X_K})` of the pullback of `L`
to that fibre, in the sense of `AlgebraicGeometry.Scheme.Modules.degree`.

The `K`-scheme structure on `X_K` is the second projection; it is supplied explicitly rather than
by instance search, since it is not an instance on a bare pullback. -/
noncomputable def picardFibreDegree (f : X ⟶ Spec (.of k)) {T : Over (Spec (.of k))}
    (L : (picardPresheaf f).obj (.op T)) {K : Type u} [Field K] [Algebra k K]
    (t : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ T) : ℤ :=
  @Modules.degree K _ _
    ⟨Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))⟩
    ((fromSkeleton _).obj (Pic.map (baseChangeMap f t) L).val)

/-- Blueprint `sk-prop-picard-degree-decomposition`: Degree decomposition of the Picard scheme

The degree-`d` subfunctor of the Picard presheaf of `f : X ⟶ Spec k`: the classes
`ℒ ∈ Pic (X_T)` all of whose fibres have degree `d`, i.e. `deg ℒ_t = d` for every field-valued
point `t` of `T`.  It is a subfunctor because the fibres of the pullback of `ℒ` along `T' ⟶ T`
are among the fibres of `ℒ`. -/
noncomputable def picardSubfunctorDegree (f : X ⟶ Spec (.of k)) (d : ℤ) :
    Subfunctor (picardPresheaf f) where
  obj T := {L | ∀ (K : Type u) (_ : Field K) (_ : Algebra k K)
    (t : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ T.unop),
      picardFibreDegree f L t = d}
  map := by
    rintro ⟨U⟩ ⟨V⟩ ⟨i⟩ L hL
    intro K _ _ t
    have h := hL K ‹_› ‹_› (t ≫ i)
    have e : Pic.map (baseChangeMap f (t ≫ i)) L =
        Pic.map (baseChangeMap f t) (Pic.map (baseChangeMap f i) L) := by
      rw [baseChangeMap_comp, Pic.map_comp]
    simp only [picardFibreDegree, e] at h
    exact h

/-- Blueprint `sk-prop-picard-degree-decomposition`: Degree decomposition of the Picard scheme

The degree-`d` part `Pic^d_{X/k}` of the relative Picard functor: the fppf sheafification of the
degree-`d` subfunctor `AlgebraicGeometry.picardSubfunctorDegree` of the Picard presheaf, in the
same way that `AlgebraicGeometry.picardFunctor` is the fppf sheafification of the whole Picard
presheaf. -/
noncomputable def picardFunctorDegree (f : X ⟶ Spec (.of k)) (d : ℤ) :
    Sheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type (u + 1))).obj
    (picardSubfunctorDegree f d).toFunctor

end DegreeSubfunctor

section Decomposition

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- Blueprint `sk-prop-picard-degree-decomposition`: Degree decomposition of the Picard scheme

Let `X` be a smooth projective curve over a separably closed field `k` and let `P` represent the
Picard functor `Pic_{X/k}`.  Then:

* the fibrewise degree is locally constant, which is spelled out as: for a *connected* `k`-scheme
  `T` and a class `ℒ ∈ Pic (X_T)`, all the fibrewise degrees `deg ℒ_t` agree;
* `P` is the disjoint union `∐_{d ∈ ℤ} P^d` of a family of open and closed subschemes `P^d`
  indexed by `ℤ`, and `P^d` represents `Pic^d_{X/k}`, the degree-`d` part
  `AlgebraicGeometry.picardFunctorDegree` of the Picard functor;
* `P^0` is a commutative group scheme over `k`;
* `P^0 ≅ P^d` as `k`-schemes, for every `d`.

Two clauses of the blueprint statement are weakened, for lack of the relevant notions:

* "`P^0` is an open and closed **subgroup scheme**" is stated only as "`P^0` is an open and closed
  subscheme, and carries a commutative group scheme structure"; that the open immersion
  `P^0 ⟶ P` is a homomorphism cannot be stated, because `P` itself is only given here as a
  representing object and carries no group structure in this statement.
* "tensoring with `𝒪_X(dP)` is an isomorphism `P^0 ≅ P^d`" is stated as the bare existence of an
  isomorphism `P^0 ≅ P^d` of `k`-schemes: there is no twisting sheaf `𝒪_X(D)` and no tensor
  product of sheaves of modules available, so the twisting map cannot be named. -/
theorem exists_decomposition_picardFunctor [IsSepClosed k]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    [GeometricallyIntegral (X ↘ Spec (.of k))] (P : Over (Spec (.of k)))
    (hP : (picardFunctor (X ↘ Spec (.of k))).obj.RepresentableBy P) :
    (∀ (T : Over (Spec (.of k))) (_ : ConnectedSpace T.left)
        (L : (picardPresheaf (X ↘ Spec (.of k))).obj (.op T))
        (K : Type u) (_ : Field K) (_ : Algebra k K)
        (t : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ T)
        (K' : Type u) (_ : Field K') (_ : Algebra k K')
        (t' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K'))) ⟶ T),
        picardFibreDegree (X ↘ Spec (.of k)) L t =
          picardFibreDegree (X ↘ Spec (.of k)) L t') ∧
      ∃ (Pd : ℤ → Over (Spec (.of k))) (j : ∀ d, Pd d ⟶ P),
        (∀ d, IsOpenImmersion (j d).left) ∧
        (∀ d, IsClopen (Set.range (j d).left.base)) ∧
        (∀ d d', d ≠ d' → Disjoint (Set.range (j d).left.base) (Set.range (j d').left.base)) ∧
        (⋃ d, Set.range (j d).left.base) = Set.univ ∧
        (∀ d, Nonempty ((picardFunctorDegree (X ↘ Spec (.of k)) d).obj.RepresentableBy (Pd d))) ∧
        Nonempty (CommGrpObj (Pd 0)) ∧ ∀ d, Nonempty (Pd 0 ≅ Pd d) := by
  sorry

end Decomposition

section TangentSpace

variable (k : Type u) [Field k]

/-- The dual numbers `k[ε] = k[T]/(T²)` over `k`, as a `k`-scheme `Spec k[ε] ⟶ Spec k`. -/
noncomputable abbrev dualNumbersOver : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))

/-- The `k`-rational point `ε ↦ 0` of `Spec k[ε]`, i.e. the closed immersion
`Spec k ⟶ Spec k[ε]` induced by the `k`-algebra projection `k[ε] → k`. -/
noncomputable def dualNumbersZero : 𝟙_ (Over (Spec (.of k))) ⟶ dualNumbersOver k :=
  Over.homMk (Spec.map (CommRingCat.ofHom
      (TrivSqZeroExt.fstHom k k k : DualNumber k →ₐ[k] k).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 (Spec (CommRingCat.of k))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    convert Spec.map_id (CommRingCat.of k) using 2
    ext x
    rfl)

variable {k}

/-- The **tangent space** of a `k`-scheme `P` at a `k`-rational point `e`, defined through the
functor of points: it is the fibre over `e` of the restriction map
`P(k[ε]) → P(k)`, where `k[ε] = k[T]/(T²)` are the dual numbers and the map is induced by
`ε ↦ 0`.

`k`-rational points of `P` are morphisms from the terminal object `𝟙_ (Over (Spec k))` of the
category of `k`-schemes, so that the unit `η[G]` of a group scheme `G` is directly a point in
this sense.  Mathlib has no tangent space of a scheme, so this is a genuine definition rather
than a reuse; it carries no `k`-vector space structure here. -/
def tangentSpaceAt (P : Over (Spec (.of k))) (e : 𝟙_ (Over (Spec (.of k))) ⟶ P) : Type u :=
  {v : dualNumbersOver k ⟶ P // dualNumbersZero k ≫ v = e}

variable {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- Blueprint `sk-prop-picard-jacobian-tangent`: The tangent space of the Jacobian

Let `X` be a smooth projective curve of genus `g` over a separably closed field `k` and let `J`
be a group scheme over `k` representing the degree-zero part `Pic^0_{X/k}` of the Picard functor.
Then the tangent space of `J` at the unit `η[J]` is in bijection with `H^1(X, 𝒪_X)`, and that
`k`-vector space has dimension `g`.

The tangent space is `AlgebraicGeometry.tangentSpaceAt`, the fibre over the unit of
`J(k[ε]) → J(k)`, since Mathlib has no tangent space of a scheme.  For the same reason the
conclusion is a bijection of types rather than an isomorphism of `k`-vector spaces: the
functor-of-points tangent space carries no `k`-module structure without the standard `k[ε]`
scaling argument, which is not available here.  The dimension statement is the second conjunct,
`h^1(X, 𝒪_X) = g`; with `AlgebraicGeometry.Scheme.genus` defined cohomologically this conjunct
is a tautology, and it is recorded only to make the blueprint clause visible. -/
theorem nonempty_tangentSpaceAt_equiv_H_one [IsSepClosed k]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    [GeometricallyIntegral (X ↘ Spec (.of k))] (J : Over (Spec (.of k))) [GrpObj J]
    (hJ : Nonempty ((picardFunctorDegree (X ↘ Spec (.of k)) 0).obj.RepresentableBy J)) :
    Nonempty (tangentSpaceAt J η[J] ≃
        Modules.H (X := X) (SheafOfModules.unit X.ringCatSheaf) 1) ∧
      Modules.h (X := X) k (SheafOfModules.unit X.ringCatSheaf) 1 = genus k X := by
  sorry

end TangentSpace

section Jacobian

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

variable (k X) in
/-- Blueprint `sk-prop-jacobian`: The Jacobian is an abelian variety

The degree-zero part `Pic^0(X) = {ℒ ∈ Pic X : deg ℒ = 0}` of the Picard group of a `k`-scheme
`X`, with `AlgebraicGeometry.Scheme.Modules.degree` the cohomological degree
`deg ℒ = χ(ℒ) - χ(𝒪_X)`.  It is only a type, not a group: there is no tensor product of sheaves
of modules, hence no group law on `AlgebraicGeometry.Scheme.Pic`. -/
def picardZero : Type (u + 1) :=
  {L : X.Pic // Modules.degree k ((fromSkeleton X.Modules).obj L.val) = 0}

/-- Blueprint `sk-prop-jacobian`: The Jacobian is an abelian variety

Let `X` be a smooth projective curve of genus `g` over a separably closed field `k`.  Then there
is a `k`-scheme `J` carrying a commutative group scheme structure (`CategoryTheory.CommGrpObj`)
which is proper, smooth of relative dimension `g` and geometrically integral over `k`, which
represents the degree-zero part `Pic^0_{X/k}` of the Picard functor, and whose set of
`k`-rational points is in bijection with `Pic^0(X) = {ℒ ∈ Pic X : deg ℒ = 0}`.

Mathlib has no `AbelianVariety` class, so "abelian variety of dimension `g`" is spelled out as
the conjunction of `CategoryTheory.CommGrpObj`, `AlgebraicGeometry.IsProper`,
`AlgebraicGeometry.SmoothOfRelativeDimension g` and
`AlgebraicGeometry.GeometricallyIntegral` for the structure morphism `J.hom`; geometric
integrality subsumes the "connected" clause of the blueprint statement.  The tangent space clause
`T_e J ≅ H^1(X, 𝒪_X)` is the content of
`AlgebraicGeometry.nonempty_tangentSpaceAt_equiv_H_one` and is not repeated here.

The base-change clause `J(X_{k'}) = J(X) ×_k k'` for `k ⊆ k'` algebraically closed is **omitted**
from this statement; the corresponding compatibility over a general base field is stated in
`AlgebraicGeometry.exists_jacobian_descent`, which is where it is used.

`k`-rational points are morphisms out of the terminal object `𝟙_ (Over (Spec k))` of the category
of `k`-schemes; the identification with `Pic^0(X)` is a bijection of types, since
`AlgebraicGeometry.Scheme.Pic` carries no group law in this development. -/
theorem exists_jacobian [IsSepClosed k]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    [GeometricallyIntegral (X ↘ Spec (.of k))] :
    ∃ (J : Over (Spec (.of k))) (_ : CommGrpObj J),
      IsProper J.hom ∧ SmoothOfRelativeDimension (genus k X) J.hom ∧
        GeometricallyIntegral J.hom ∧
        Nonempty ((picardFunctorDegree (X ↘ Spec (.of k)) 0).obj.RepresentableBy J) ∧
        Nonempty (picardZero k X ≃ (𝟙_ (Over (Spec (.of k))) ⟶ J)) := by
  sorry

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

/-- Blueprint `sk-prop-jacobian-descent`: The Jacobian over a general base field, by Galois descent

Let `k₀` be any field, `k_s` a separable closure of `k₀`, `k̄₀` an algebraic closure of `k₀`
containing `k_s`, and let `C₀` be a proper smooth geometrically connected curve of genus `g` over
`k₀`.  Let `C` be the base change `C₀ ×_{k₀} k̄₀`, presented by a cartesian square.  Then the
Jacobian of `C` descends to `k₀`: there is a `k₀`-scheme `J₀` carrying a commutative group scheme
structure, proper, smooth of relative dimension `g` and geometrically integral over `k₀`, whose
base change `J₀ ×_{k₀} k̄₀` represents the degree-zero part `Pic^0_{C/k̄₀}` of the Picard functor
of `C`, and whose `k̄₀`-points are in bijection with `Pic^0(C)`.  The bijection is equivariant:
every `k₀`-algebra automorphism `σ` of `k̄₀` induces the automorphism `γ` of `C` over `C₀` lying
over `Spec σ`, base change along `γ` preserves `Pic^0(C)`, and the bijection intertwines that
action with the action on `k̄₀`-points by precomposition with
`AlgebraicGeometry.specAlgEquivOver σ`.

Three clauses of the blueprint statement are weakened:

* the Galois group is taken to be `k̄₀ ≃ₐ[k₀] k̄₀` rather than `Gal(k_s/k₀) = k_s ≃ₐ[k₀] k_s`.
  Restriction `k̄₀ ≃ₐ[k₀] k̄₀ → k_s ≃ₐ[k₀] k_s` is surjective with the same orbits, so this is the
  same action, but the restriction map and its surjectivity are extra field theory that would
  only obscure the statement; `k_s` is kept as a hypothesis so that the intended group is
  visible.
* the `ℓⁿ`-torsion clause `J₀[ℓⁿ](k̄₀) ≅ Pic^0(C)[ℓⁿ]` is **omitted**: there is no group law on
  `AlgebraicGeometry.Scheme.Pic` in this development, so `Pic^0(C)[ℓⁿ]` cannot be formed.  Once
  the tensor product of sheaves of modules exists it follows from the equivariant bijection
  below by restricting to `ℓⁿ`-torsion on both sides.
* "the representing isomorphism descends canonically, compatibly with base change" is rendered as
  the single representability statement for `J₀ ×_{k₀} k̄₀` together with the equivariance; the
  descent datum itself is not spelled out.

No rational point of `C₀` is assumed. -/
theorem exists_jacobian_descent (k₀ ks K : Type u) [Field k₀] [Field ks] [Field K]
    [Algebra k₀ ks] [Algebra k₀ K] [Algebra ks K] [IsScalarTower k₀ ks K]
    [IsSepClosure k₀ ks] [IsAlgClosure k₀ K] (C₀ : Scheme.{u}) [C₀.Over (Spec (.of k₀))]
    [SmoothOfRelativeDimension 1 (C₀ ↘ Spec (.of k₀))] [IsProper (C₀ ↘ Spec (.of k₀))]
    [GeometricallyConnected (C₀ ↘ Spec (.of k₀))] (g : ℕ) (hg : genus k₀ C₀ = g)
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
  sorry

end Descent

end AlgebraicGeometry
