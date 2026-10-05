/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
public import WeilConjectures.AlgebraicGeometry.DualNumbers
public import WeilConjectures.AlgebraicGeometry.EffectiveDescent
public import WeilConjectures.AlgebraicGeometry.Picard.Representability
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.Algebra.DualNumber
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Basic

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
- `AlgebraicGeometry.isSepClosed_and_curve_pullback`: the base change of the curve to a separable
  closure (blueprint `lem-pd-geometric-curve`).
- `AlgebraicGeometry.exists_jacobian_pullback`: the Jacobian over a separable closure (blueprint
  `thm-pd-geometric-pic0`).
- `AlgebraicGeometry.nonempty_picardFunctorDegree_iso_of_isPullback`: `Pic^0` commutes with base
  change (blueprint `cor-pd-pic0-base-change`).
- `AlgebraicGeometry.exists_intermediateField_representableBy`: the descent datum is defined at a
  finite separable level (blueprint `cor-pd-finite-level`).
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

/-- **The base change of a curve to a separable closure.** Let `C` be a smooth projective
geometrically integral curve of genus `g` over `k` and let `k_s` be a separable closure of `k`.
Then `k_s` is separably closed and the base change `C_{k_s}` is a smooth projective geometrically
integral curve of genus `g` over `k_s`.

(blueprint: `lem-pd-geometric-curve`) -/
theorem isSepClosed_and_curve_pullback (ks : Type u) [Field ks] [Algebra k ks]
    [IsSepClosure k ks] (C : Scheme.{u}) [C.Over (Spec (.of k))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))] [IsProper (C ↘ Spec (.of k))]
    [GeometricallyIntegral (C ↘ Spec (.of k))] :
    IsSepClosed ks ∧
      SmoothOfRelativeDimension 1
        (pullback (C ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k ks))) ↘
          Spec (.of ks)) ∧
      IsProper (pullback (C ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k ks))) ↘
          Spec (.of ks)) ∧
      GeometricallyIntegral
        (pullback (C ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k ks))) ↘
          Spec (.of ks)) ∧
      arithmeticGenus ks
          (pullback (C ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k ks)))) =
        arithmeticGenus k C :=
  ⟨IsSepClosure.sep_closed k,
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance,
    inferInstanceAs (IsProper (pullback.snd _ _)),
    inferInstanceAs (GeometricallyIntegral (pullback.snd _ _)), arithmeticGenus_pullback ks⟩

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
  obtain ⟨_, _, _, _, hgs⟩ := isSepClosed_and_curve_pullback (k := k) ks C
  rw [← hg, ← hgs]
  exact exists_jacobian (k := ks)

/-- **The degree-zero part is compatible with base change.** Let `C` be a smooth projective
geometrically integral curve over `k`, let `K/k` be a field extension and let `C_K` be the base
change of `C`, presented by a cartesian square. Then the restriction of `Pic^0_{C/k}` to schemes
over `K` is `Pic^0_{C_K/K}`.

This follows from the compatibility of the Picard functor with base change
(`AlgebraicGeometry.nonempty_picardFunctor_iso_of_isPullback`), the fibrewise degree of a class
being computed on the same fibres in both cases.

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
  sorry

/-- **The descent datum is defined at a finite separable level.** Let `C` be a smooth projective
geometrically integral curve over `k`, let `k_s` be a separable closure of `k` and let `J_s`
represent the restriction of `Pic^0_{C/k}` to schemes over `k_s`, so that `J_s` carries the
canonical descent datum relative to `Spec k_s ⟶ Spec k`
(`CategoryTheory.Functor.RepresentableBy.overDescentDatum`). Then there are a finite separable
subextension `K` of `k_s/k` and a `K`-scheme `J_K` representing the restriction of `Pic^0_{C/k}`
to schemes over `K` — so that `J_K` carries the canonical descent datum relative to
`Spec K ⟶ Spec k`, which base changes to that of `J_s` — such that `J_K ×_K k_s ≅ J_s`. Moreover
every finite set of points of `J_K` lies in an affine open, `J_K` being projective over `K`.

The blueprint asks for a descent datum on `J_K` whose base change is that of `J_s`; asking that
`J_K` represent the restriction of `Pic^0_{C/k}` produces such a datum canonically. The proof
spreads `J_s`, its datum and a closed immersion `J_s ⟶ ℙ^N` out to a finite level
(Stacks 01ZM: `AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation`,
`AlgebraicGeometry.Scheme.exists_pullback_hom_of_isLimit` and
`AlgebraicGeometry.Scheme.exists_pullback_fst_comp_eq_of_isLimit`).

(blueprint: `cor-pd-finite-level`) -/
theorem exists_intermediateField_representableBy {ks : Type u} [Field ks] [Algebra k ks]
    [IsSepClosure k ks] (C : Scheme.{u}) [C.Over (Spec (.of k))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))] [IsProper (C ↘ Spec (.of k))]
    [GeometricallyIntegral (C ↘ Spec (.of k))] (Js : Over (Spec (.of ks)))
    (rs : ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k ks)))).op ⋙
      (picardFunctorDegree (C ↘ Spec (.of k)) 0).obj).RepresentableBy Js) :
    ∃ (K : IntermediateField k ks), FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
      ∃ (JK : Over (Spec (.of K)))
        (_ : ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).op ⋙
          (picardFunctorDegree (C ↘ Spec (.of k)) 0).obj).RepresentableBy JK)
        (q : Js.left ⟶ JK.left),
        IsPullback q Js.hom JK.hom (Spec.map (CommRingCat.ofHom (algebraMap K ks))) ∧
          ∀ s : Set JK.left, s.Finite → ∃ U : JK.left.Opens, IsAffineOpen U ∧ s ⊆ U :=
  sorry

/-- **The group law is compatible with the canonical descent datum.** Let `K/k` be a field
extension and let `J_K` represent the restriction of `Pic^0_{C/k}` to schemes over `K`. Then `J_K`
carries a commutative group scheme structure whose multiplication and unit are compatible with the
canonical descent datum of `J_K` relative to `Spec K ⟶ Spec k`.

The group structure is the one induced by the group law of `Pic^0_{C/k}`, and it is compatible
with the datum because that group law is defined over `k`: transport does not change the element
of `Pic^0_{C/k}(T)` that a point stands for. This is Step 5 of the proof of
`AlgebraicGeometry.exists_jacobian_descent`; it is stated separately because
`AlgebraicGeometry.Scheme.Pic` carries no group law here. -/
theorem exists_commGrpObj_overTransport {K : Type u} [Field K] [Algebra k K] (C : Scheme.{u})
    [C.Over (Spec (.of k))] [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))]
    [IsProper (C ↘ Spec (.of k))] [GeometricallyIntegral (C ↘ Spec (.of k))]
    (JK : Over (Spec (.of K)))
    (r : ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).op ⋙
      (picardFunctorDegree (C ↘ Spec (.of k)) 0).obj).RepresentableBy JK) :
    ∃ _ : CommGrpObj JK,
      (∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ Spec (.of K))
        (h : f₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) =
          f₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))) (a b : Over.mk f₁ ⟶ JK),
        r.overTransport f₁ f₂ h (CartesianMonoidalCategory.lift a b ≫ μ[JK]) =
          CartesianMonoidalCategory.lift (r.overTransport f₁ f₂ h a)
            (r.overTransport f₁ f₂ h b) ≫ μ[JK]) ∧
      ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ Spec (.of K))
        (h : f₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) =
          f₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))),
        r.overTransport f₁ f₂ h (CartesianMonoidalCategory.toUnit _ ≫ η[JK]) =
          CartesianMonoidalCategory.toUnit _ ≫ η[JK] :=
  sorry

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
              (picardFunctorDegree (C₀ ↘ Spec (.of k₀)) 0).obj.map (specAlgEquivOver σ).op (Φ L) :=
  sorry

omit [Field k] in
/-- `Spec K ⟶ Spec k` is surjective, finite, flat and of finite presentation for a finite field
extension `K/k`. -/
lemma isFinite_flat_surjective_specMap (k K : Type u) [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k K))) ∧
      Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) ∧
      LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap k K))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  have hfin : (CommRingCat.ofHom (algebraMap k K)).hom.Finite :=
    RingHom.finite_algebraMap.mpr inferInstance
  refine ⟨IsFinite.SpecMap_iff _ |>.mpr hfin, Flat.SpecMap_iff.mpr ?_, ?_,
    ⟨fun x ↦ ⟨default, Subsingleton.elim _ _⟩⟩⟩
  · exact RingHom.flat_algebraMap_iff.mpr inferInstance
  · rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    exact RingHom.FinitePresentation.of_finiteType.mp hfin.finiteType

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
  obtain ⟨K, _, _, JK, rK, q', hq', hJK⟩ :=
    exists_intermediateField_representableBy C Js (rJs.ofIso e.symm)
  obtain ⟨_, _, _, _⟩ := isFinite_flat_surjective_specMap k K
  -- Step 4: the canonical descent datum of `J_K` is effective, with descended scheme `J`.
  obtain ⟨J, q, hq, hinv⟩ := rK.overDescentDatum.isEffective_of_isFinite hJK
  -- Step 7: `J` represents `Pic^0_{C/k}`.
  obtain ⟨r⟩ := nonempty_representableBy_of_isPullback _ _ rK q hq hinv
  -- Step 5: the group law descends.
  obtain ⟨_, hμ, hη⟩ := exists_commGrpObj_overTransport C JK rK
  obtain ⟨_, -⟩ := rK.overDescentDatum.exists_commGrpObj_of_isPullback q hq hinv hμ hη
  -- Step 6: the geometric properties descend along `k ⊆ k_s`.
  have hs : Spec.map (CommRingCat.ofHom (algebraMap K ks)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k K)) =
        Spec.map (CommRingCat.ofHom (algebraMap k ks)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  obtain ⟨hP, hS, hG⟩ := isProper_smoothOfRelativeDimension_geometricallyIntegral_of_isPullback
    J.hom Js.hom (q' ≫ q) (hs ▸ hq'.paste_horiz hq) g
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
