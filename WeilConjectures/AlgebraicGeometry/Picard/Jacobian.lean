/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
public import WeilConjectures.AlgebraicGeometry.Picard.Representability
public import WeilConjectures.Mathlib.Algebra.DualNumber
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

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
  equivariance; the descent datum itself is not spelled out.

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

end DegreeSubfunctor

section Decomposition

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsSepClosed k]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [GeometricallyIntegral (X ↘ Spec (.of k))]

/-- **The fibrewise degree is locally constant.** For a connected `k`-scheme `T` and a class
`ℒ ∈ Pic (X_T)`, all the fibrewise degrees `deg ℒ_t` agree.

(blueprint: `sk-prop-picard-degree-decomposition`) -/
theorem picardFibreDegree_eq_of_connectedSpace (T : Over (Spec (.of k)))
    [ConnectedSpace T.left] (L : (picardPresheaf (X ↘ Spec (.of k))).obj (.op T))
    {K : Type u} [Field K] [Algebra k K]
    (t : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ T)
    {K' : Type u} [Field K'] [Algebra k K']
    (t' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K'))) ⟶ T) :
    picardFibreDegree (X ↘ Spec (.of k)) L t = picardFibreDegree (X ↘ Spec (.of k)) L t' :=
  sorry

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
      ∀ d, Nonempty ((picardFunctorDegree (X ↘ Spec (.of k)) d).obj.RepresentableBy (Pd d)) :=
  sorry

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

end Decomposition

section TangentSpace

variable (k : Type u) [Field k]

/-- The dual numbers `k[ε] = k[T]/(T²)` over `k`, as a `k`-scheme `Spec k[ε] ⟶ Spec k`. -/
noncomputable abbrev dualNumbersOver : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))

/-- The `k`-rational point `ε ↦ 0` of `Spec k[ε]`, i.e. the closed immersion
`Spec k ⟶ Spec k[ε]` induced by the `k`-algebra projection `k[ε] → k`. -/
noncomputable def dualNumbersZero : 𝟙_ (Over (Spec (.of k))) ⟶ dualNumbersOver k :=
  Over.homMk (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k : DualNumber k →+* k))) (by
    simp only [Over.mk_hom, Over.tensorUnit_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]
    exact Spec.map_id _)

@[simp]
lemma dualNumbersZero_left :
    (dualNumbersZero k).left =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k : DualNumber k →+* k)) :=
  rfl

variable {k}

/-- The **tangent space** of a `k`-scheme `P` at a `k`-rational point `e`, defined through the
functor of points: it is the fibre over `e` of the restriction map
`P(k[ε]) → P(k)`, where `k[ε] = k[T]/(T²)` are the dual numbers and the map is induced by
`ε ↦ 0`.

`k`-rational points of `P` are morphisms from the terminal object `𝟙_ (Over (Spec k))` of the
category of `k`-schemes, so that the unit `η[G]` of a group scheme `G` is directly a point in
this sense.  Mathlib has no tangent space of a scheme, so this is a genuine definition rather
than a reuse. At the unit of a group scheme it is a `k`-vector space, its addition being the
group law; see `AlgebraicGeometry.tangentSubgroup`. -/
def tangentSpaceAt (P : Over (Spec (.of k))) (e : 𝟙_ (Over (Spec (.of k))) ⟶ P) : Type u :=
  {v : dualNumbersOver k ⟶ P // dualNumbersZero k ≫ v = e}

variable (k) in
/-- The `k`-endomorphism of `Spec k[ε]` induced by the `k`-algebra map `ε ↦ c ε` of the dual
numbers. It defines the scalar action on tangent spaces. -/
noncomputable def dualNumbersScale (c : k) : dualNumbersOver k ⟶ dualNumbersOver k :=
  Over.homMk (Spec.map (CommRingCat.ofHom (DualNumber.scale c : DualNumber k →+* DualNumber k))) (by
    simp only [Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap])

@[simp]
lemma dualNumbersScale_left (c : k) :
    (dualNumbersScale k c).left =
      Spec.map (CommRingCat.ofHom (DualNumber.scale c : DualNumber k →+* DualNumber k)) :=
  rfl

@[reassoc (attr := simp)]
lemma dualNumbersZero_comp_dualNumbersScale (c : k) :
    dualNumbersZero k ≫ dualNumbersScale k c = dualNumbersZero k := by
  ext : 1
  rw [Over.comp_left, dualNumbersScale_left, dualNumbersZero_left, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← AlgHom.comp_toRingHom, DualNumber.fstHom_comp_scale]

@[simp]
lemma dualNumbersScale_one : dualNumbersScale k 1 = 𝟙 _ := by
  ext : 1
  rw [dualNumbersScale_left, DualNumber.scale_one, Over.id_left]
  exact Spec.map_id _

@[reassoc]
lemma dualNumbersScale_mul (c d : k) :
    dualNumbersScale k (c * d) = dualNumbersScale k c ≫ dualNumbersScale k d := by
  ext : 1
  rw [Over.comp_left, dualNumbersScale_left, dualNumbersScale_left, dualNumbersScale_left,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← AlgHom.comp_toRingHom, DualNumber.scale_mul]

/-- Scaling by `0` factors through the point `ε ↦ 0`, since `ε ↦ 0` factors as
`k[ε] → k → k[ε]`. -/
lemma dualNumbersScale_zero :
    dualNumbersScale k 0 = CartesianMonoidalCategory.toUnit _ ≫ dualNumbersZero k := by
  ext : 1
  rw [Over.comp_left, dualNumbersScale_left, dualNumbersZero_left, Over.toUnit_left]
  simp only [Over.mk_hom]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, DualNumber.scale_zero, AlgHom.comp_toRingHom]
  rfl

section GrpObj

open scoped MonObj

variable (P : Over (Spec (.of k))) [GrpObj P]

/-- The tangent space of a group scheme `P` at the unit, as the kernel of the restriction map
`P(k[ε]) → P(k)` induced by `ε ↦ 0`, a subgroup of the group `P(k[ε])`. -/
def tangentSubgroup : Subgroup (dualNumbersOver k ⟶ P) where
  carrier := {v | dualNumbersZero k ≫ v = η[P]}
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
    rw [dualNumbersZero_comp_dualNumbersScale_assoc, v.2]⟩

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
definition of `AlgebraicGeometry.Scheme.genus`.

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
      IsProper J.hom ∧ SmoothOfRelativeDimension (genus k X) J.hom ∧
        GeometricallyIntegral J.hom ∧
        Nonempty ((picardFunctorDegree (X ↘ Spec (.of k)) 0).obj.RepresentableBy J) ∧
        Nonempty (picardZero k X ≃ (𝟙_ (Over (Spec (.of k))) ⟶ J)) :=
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
                ∀ L, e (act L) = specAlgEquivOver σ ≫ e L :=
  sorry

end Descent

end AlgebraicGeometry
