/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.Curve.Picard
public import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
public import WeilConjectures.AlgebraicGeometry.DualNumbers
public import WeilConjectures.AlgebraicGeometry.DualNumbersBaseChange
public import WeilConjectures.AlgebraicGeometry.Picard.DualNumbers
public import WeilConjectures.AlgebraicGeometry.EffectiveDescent
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Separated
public import WeilConjectures.AlgebraicGeometry.Picard.Degree
public import WeilConjectures.AlgebraicGeometry.Picard.Scheme
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.Algebra.DualNumber
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
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

The group law of `Pic^0_{X/k}` is the tensor product of invertible modules: the classes of
fibrewise degree zero form a presheaf of groups (`AlgebraicGeometry.picardPresheafDegreeZeroGrp`),
whose fppf sheafification `Pic^0_{X/k}` inherits the group law (`CategoryTheory.sheafifyGrp`). A
scheme `J` representing `Pic^0_{X/k}` therefore carries a commutative group scheme structure
whose group law is the tensor product (`AlgebraicGeometry.exists_commGrpObj_isPicardZeroMul`);
that the representation respects the group laws is the predicate
`AlgebraicGeometry.IsPicardZeroMul`, which all the representability statements below include.
The degree-zero part `Pic^0(X)` of the Picard group is the subgroup
`AlgebraicGeometry.picardZero`, the kernel of the degree `AlgebraicGeometry.Scheme.picDegreeHom`,
and the bijections between `Pic^0(X)` and the rational points of the Jacobian are group
isomorphisms. The `ℓⁿ`-torsion clause `J₀[ℓⁿ](k̄₀) ≅ Pic^0(C)[ℓⁿ]` of
`sk-prop-jacobian-descent` is the restriction of the group isomorphism of
`AlgebraicGeometry.exists_jacobian_descent` to `ℓⁿ`-torsion, and is not stated separately.

That `P^0` is an open and closed **subgroup scheme** of `P` is not stated: `P^0` carries the
group law of `Pic^0_{X/k}`, and `P` that of `Pic_{X/k}`
(`AlgebraicGeometry.isRepresentable_picardFunctor`), but the compatibility of the open immersion
`P^0 ⟶ P` with them is not recorded by `AlgebraicGeometry.exists_decomposition_picardFunctor`.

Several clauses of the blueprint statements cannot be expressed and are dropped:

* there is no twisting sheaf `𝒪_X(D)`, so "tensoring with `𝒪_X(dP)` is an isomorphism
  `P^0 ≅ P^d`" is stated as the bare existence of an isomorphism of `k`-schemes.
* Mathlib has no tangent space of a scheme, so `AlgebraicGeometry.tangentSpaceAt` is defined
  here through the functor of points. It is given a `k`-vector space structure only at the
  unit of a group scheme, where it is the kernel `AlgebraicGeometry.tangentSubgroup` of
  `P(k[ε]) → P(k)` and the addition is the group law. The standard construction instead puts a
  `k`-vector space structure on the tangent space at any `k`-point of any `k`-scheme, and then
  identifies its addition with the group law at the unit; that comparison is not formalised.
  The commutativity of `tangentSubgroup P` and the axiom `(c + d) • v = c • v + d • v` are
  transported from the Lie algebra of `P`: `tangentSubgroup P` is the group
  `AlgebraicGeometry.GrpObj.infPoints P` of infinitesimal points, in bijection with
  `AlgebraicGeometry.GrpObj.Lie P` (`AlgebraicGeometry.GrpObj.lieEquiv`).
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
level `K`, where it is effective because the representing scheme is projective, and the
geometric properties descend with it. The descended scheme represents `Pic^0_{C/k}`, so its group
law is the one induced by `Pic^0_{C/k}` (`AlgebraicGeometry.exists_commGrpObj_isPicardZeroMul`)
and need not be descended. The deep inputs — spreading out, effective
descent, fpqc descent of properties, the base change of the degree-zero Picard functor and its
value at an algebraically closed point — are stated separately.

## Main definitions

- `AlgebraicGeometry.picardFibreDegree`: the degree of a relative Picard class on the fibre over
  a field-valued point of the base.
- `AlgebraicGeometry.picardSubfunctorDegree`: the degree-`d` subfunctor of the Picard presheaf.
- `AlgebraicGeometry.picardFunctorDegree`: the degree-`d` part `Pic^d_{X/k}` of the relative
  Picard functor.
- `AlgebraicGeometry.picardPresheafDegreeZeroGrp`: the classes of fibrewise degree zero, as a
  presheaf of groups.
- `AlgebraicGeometry.IsPicardZeroMul`: a representation of `Pic^0_{X/k}` by a group scheme
  respects the group laws.
- `AlgebraicGeometry.picardZero`: the subgroup `Pic^0(X)` of `Pic(X)`.
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
  `AlgebraicGeometry.exists_commGrpObj_isPicardZeroMul` and
  `AlgebraicGeometry.nonempty_iso_of_representableBy`: the degree decomposition of the Picard
  scheme (blueprint `sk-prop-picard-degree-decomposition`).
- `AlgebraicGeometry.nonempty_tangentSpaceAt_linearEquiv_H_one`: the tangent space of the Jacobian
  (blueprint `sk-prop-picard-jacobian-tangent`).
- `AlgebraicGeometry.isProper_of_representableBy_picardFunctorDegree` and
  `AlgebraicGeometry.smoothOfRelativeDimension_of_representableBy_picardFunctorDegree`: the
  theorem of the base, every `Pic^d_{X/k}` is proper and smooth of dimension `g` (blueprint
  `thm-sc-theorem-of-the-base`).
- `AlgebraicGeometry.exists_surjective_of_representableBy_picardFunctorDegree_genus`: the Abel map
  `Hilb^g ⟶ Pic^g`, `D ↦ 𝒪_X(D)`, is surjective; with `AlgebraicGeometry.exists_abelClass_eq` (a
  class of degree `g` is effective) this gives properness and geometric integrality of `Pic^g`.
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

end DegreeSubfunctor

section GroupLaw

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

section FibreDegree

variable {T : Over (Spec (.of k))} {K : Type u} [Field K] [Algebra k K]
  (t : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ T)

/-- **The fibrewise degree is additive**: on a smooth proper curve, the degree of `ℒ ⊗ ℳ` on the
fibre over a field-valued point is the sum of the degrees of `ℒ` and `ℳ`, the fibre being a smooth
proper curve over that field (`AlgebraicGeometry.Scheme.Modules.degree_tensorObj`). -/
lemma picardFibreDegree_mul [SmoothOfRelativeDimension 1 f] [IsProper f]
    (L M : (pullback f T.hom).Pic) :
    picardFibreDegree f (L * M : (pullback f T.hom).Pic) t =
      picardFibreDegree f L t + picardFibreDegree f M t := by
  let : (pullback f (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))).hom).Over
      (Spec (.of K)) := ⟨pullback.snd _ _⟩
  have : SmoothOfRelativeDimension 1 (pullback f
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))).hom ↘ Spec (.of K)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback _ _) ‹_›
  have : IsProper (pullback f
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))).hom ↘ Spec (.of K)) :=
    IsProper.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  change Modules.degree K _ = Modules.degree K _ + Modules.degree K _
  rw [Pic.map_mul]
  exact (Modules.degree_congr K (Pic.mulIso _ _)).trans (Modules.degree_tensorObj _ _)

/-- The fibrewise degree of the unit class is zero. -/
lemma picardFibreDegree_one : picardFibreDegree f (1 : (pullback f T.hom).Pic) t = 0 := by
  let : (pullback f (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))).hom).Over
      (Spec (.of K)) := ⟨pullback.snd _ _⟩
  change Modules.degree K _ = 0
  rw [Pic.map_one]
  exact (Modules.degree_congr K Pic.oneIso).trans (Modules.degree_unit K)

end FibreDegree

variable [SmoothOfRelativeDimension 1 f] [IsProper f]

/-- The classes `ℒ ∈ Pic (X_T)` of fibrewise degree zero form a subgroup of `Pic (X_T)`, the
fibrewise degree being additive (`AlgebraicGeometry.picardFibreDegree_mul`). Its carrier is
`(AlgebraicGeometry.picardSubfunctorDegree f 0).obj (.op T)`. -/
noncomputable def picardSubgroupDegreeZero (T : Over (Spec (.of k))) :
    Subgroup (pullback f T.hom).Pic where
  carrier := (picardSubfunctorDegree f 0).obj (.op T)
  one_mem' K _ _ t := picardFibreDegree_one f t
  mul_mem' {L M} hL hM K _ _ t := by
    rw [picardFibreDegree_mul f t L M, hL K t, hM K t, add_zero]
  inv_mem' {L} hL K _ _ t := by
    have h := picardFibreDegree_mul f t L⁻¹ L
    rw [inv_mul_cancel, picardFibreDegree_one, hL K t, add_zero] at h
    exact h.symm

/-- **The degree-zero part of the Picard presheaf is a presheaf of groups**: `T` is sent to the
subgroup `AlgebraicGeometry.picardSubgroupDegreeZero f T` of `Pic (X_T)`, and pulling back along
`X_{T'} ⟶ X_T` is a group homomorphism. The underlying presheaf of sets is the degree-zero
subfunctor `AlgebraicGeometry.picardSubfunctorDegree f 0`
(`AlgebraicGeometry.picardPresheafDegreeZeroGrp_comp_forget`), whose fppf sheafification is
`Pic^0_{X/k}`.

(blueprint: `sk-prop-picard-degree-decomposition`) -/
noncomputable def picardPresheafDegreeZeroGrp :
    (Over (Spec (.of k)))ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj T := GrpCat.of (picardSubgroupDegreeZero f T.unop)
  map φ := GrpCat.ofHom
    { toFun L := ⟨Pic.map (baseChangeMap f φ.unop) L.1,
        (picardSubfunctorDegree f 0).map φ L.2⟩
      map_one' := Subtype.ext (Pic.map_one _)
      map_mul' L L' := Subtype.ext (Pic.map_mul _ L.1 L'.1) }
  map_id T := by
    refine GrpCat.hom_ext (MonoidHom.ext fun L ↦ Subtype.ext ?_)
    change Pic.map (baseChangeMap f (𝟙 T).unop) L.1 = L.1
    rw [unop_id, baseChangeMap_id, Pic.map_id]
  map_comp φ ψ := by
    refine GrpCat.hom_ext (MonoidHom.ext fun L ↦ Subtype.ext ?_)
    change Pic.map (baseChangeMap f (φ ≫ ψ).unop) L.1 =
      Pic.map (baseChangeMap f ψ.unop) (Pic.map (baseChangeMap f φ.unop) L.1)
    rw [unop_comp, baseChangeMap_comp, Pic.map_comp]

/-- The underlying presheaf of sets of `picardPresheafDegreeZeroGrp` is the degree-zero
subfunctor of the Picard presheaf. -/
lemma picardPresheafDegreeZeroGrp_comp_forget :
    picardPresheafDegreeZeroGrp f ⋙ forget GrpCat = (picardSubfunctorDegree f 0).toFunctor :=
  rfl

omit [SmoothOfRelativeDimension 1 f] [IsProper f] in
/-- A representation `e` of the degree-zero Picard functor `Pic^0_{X/k}` by a group scheme `J`
*respects the group laws* if, for every `k`-scheme `T`, the map sending a class `ℒ ∈ Pic (X_T)`
of fibrewise degree zero to the point of `J` classifying its image in `Pic^0_{X/k}(T)` turns the
tensor product of invertible modules into the group law of `J`. Equivalently, `e` is an
isomorphism of group-valued functors between `Pic^0_{X/k}`, with the group law induced by that of
`AlgebraicGeometry.picardPresheafDegreeZeroGrp`, and the functor of points of `J`.

The product `ℒ ⊗ ℳ` is required to have fibrewise degree zero; for a smooth proper curve this is
automatic (`AlgebraicGeometry.picardSubgroupDegreeZero`).

(blueprint: `sk-def-av-jacobian`, `rem-pc-group-structure`) -/
def IsPicardZeroMul {J : Over (Spec (.of k))} [GrpObj J]
    (e : (picardFunctorDegree f 0).obj.RepresentableBy J) : Prop :=
  ∀ {T : Over (Spec (.of k))} (L M : (pullback f T.hom).Pic)
    (hL : L ∈ (picardSubfunctorDegree f 0).obj (.op T))
    (hM : M ∈ (picardSubfunctorDegree f 0).obj (.op T))
    (hLM : L * M ∈ (picardSubfunctorDegree f 0).obj (.op T)),
    e.homEquiv.symm ((toSheafify (fppfTopology.over (Spec (.of k)))
        (picardSubfunctorDegree f 0).toFunctor).app (.op T) ⟨L * M, hLM⟩) =
      e.homEquiv.symm ((toSheafify (fppfTopology.over (Spec (.of k)))
          (picardSubfunctorDegree f 0).toFunctor).app (.op T) ⟨L, hL⟩) *
        e.homEquiv.symm ((toSheafify (fppfTopology.over (Spec (.of k)))
          (picardSubfunctorDegree f 0).toFunctor).app (.op T) ⟨M, hM⟩)

/-- **`Pic^0` is a commutative group scheme.** Let `X` be a smooth proper curve over a field `k`.
A `k`-scheme `J` representing the degree-zero part `Pic^0_{X/k}` of the Picard functor carries a
commutative group scheme structure for which the representation respects the group laws: the
group law of `J` is the tensor product of invertible modules, through the group law that the
sheafification `Pic^0_{X/k}` inherits from `AlgebraicGeometry.picardPresheafDegreeZeroGrp`
(`CategoryTheory.sheafifyGrp`).

(blueprint: `sk-prop-picard-degree-decomposition`, `rem-pc-group-structure`) -/
theorem exists_commGrpObj_isPicardZeroMul {J : Over (Spec (.of k))}
    (e : (picardFunctorDegree f 0).obj.RepresentableBy J) :
    ∃ _ : CommGrpObj J, IsPicardZeroMul f e := by
  let G := picardPresheafDegreeZeroGrp f
  let e' : (sheafify (fppfTopology.over (Spec (.of k))) (G ⋙ forget GrpCat)).RepresentableBy J :=
    e
  let := GrpObj.ofRepresentableBySheafify _ G J e'
  have := isCommMonObj_ofRepresentableBySheafify _ G
    (fun _ x y ↦ Subtype.ext (mul_comm x.1 y.1)) e'
  exact ⟨{ }, fun {T} L M hL hM _ ↦
    homEquiv_symm_toSheafify_mul _ G e' (Y := T) ⟨L, hL⟩ ⟨M, hM⟩⟩

omit [SmoothOfRelativeDimension 1 f] [IsProper f] in
/-- **Rational points as a group.** Let `e` represent `Pic^0_{X/k}` by a group scheme `J`,
respecting the group laws. If a bijection `Φ` from a group `G` to `Pic^0_{X/k}(T)` sends every
`g ∈ G` to the image of a class `ρ g ∈ Pic (X_T)` of fibrewise degree zero, for a
multiplicative map `ρ : G → Pic (X_T)`, then `G ≅ J(T)` as groups, through `Φ` followed by the
representation. This turns the bijections `Pic^0(X) ≃ Pic^0_{X/k}(k)` below into group
isomorphisms `Pic^0(X) ≃* J(k)`. -/
theorem exists_mulEquiv_of_isPicardZeroMul {G : Type*} [Group G] {T : Over (Spec (.of k))}
    {J : Over (Spec (.of k))} [GrpObj J] (e : (picardFunctorDegree f 0).obj.RepresentableBy J)
    (he : IsPicardZeroMul f e) (ρ : G → (pullback f T.hom).Pic)
    (hρ : ∀ a b, ρ (a * b) = ρ a * ρ b)
    (Φ : G ≃ (picardFunctorDegree f 0).obj.obj (.op T))
    (hΦ : ∀ g, ∃ h, Φ g = (toSheafify (fppfTopology.over (Spec (.of k)))
      (picardSubfunctorDegree f 0).toFunctor).app (.op T) ⟨ρ g, h⟩) :
    ∃ ψ : G ≃* (T ⟶ J), ∀ g, ψ g = e.homEquiv.symm (Φ g) := by
  refine ⟨{ Φ.trans e.homEquiv.symm with map_mul' a b := ?_ }, fun _ ↦ rfl⟩
  obtain ⟨ha, hΦa⟩ := hΦ a
  obtain ⟨hb, hΦb⟩ := hΦ b
  obtain ⟨hab, hΦab⟩ := hΦ (a * b)
  have hab' : ρ a * ρ b ∈ (picardSubfunctorDegree f 0).obj (.op T) := hρ a b ▸ hab
  change e.homEquiv.symm (Φ (a * b)) = e.homEquiv.symm (Φ a) * e.homEquiv.symm (Φ b)
  rw [hΦab, hΦa, hΦb, ← he _ _ ha hb hab']
  congr 3
  exact hρ a b

end GroupLaw

section DegreeShift

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- **The fibrewise degree of a class pulled back from `X`** is its degree: for `ℒ ∈ Pic X`, a
`k`-scheme `T` and a field-valued point `t : Spec K ⟶ T`, the pullback of `ℒ` to `X_T` has degree
`deg ℒ` on the fibre `X_K`, the degree being invariant under extension of the base field
(`AlgebraicGeometry.Scheme.Modules.degree_pullback`). -/
theorem picardFibreDegree_map_fst [IsProper (X ↘ Spec (.of k))] {T : Over (Spec (.of k))}
    (L : X.Pic) {K : Type u} [Field K] [Algebra k K]
    (t : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ T) :
    picardFibreDegree (X ↘ Spec (.of k)) (Pic.map (pullback.fst (X ↘ Spec (.of k)) T.hom) L) t =
      Modules.degree k ((fromSkeleton X.Modules).obj L.val) := by
  have hb : baseChangeMap (X ↘ Spec (.of k)) t ≫ pullback.fst (X ↘ Spec (.of k)) T.hom =
      pullback.fst (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    pullback.lift_fst _ _ _ |>.trans (Category.comp_id _)
  let : (pullback (X ↘ Spec (.of k))
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))).hom).Over (Spec (.of K)) :=
    ⟨pullback.snd _ _⟩
  change Modules.degree K ((fromSkeleton _).obj
    (Pic.map (baseChangeMap _ t) (Pic.map (pullback.fst _ T.hom) L)).val) = _
  rw [← Pic.map_comp, hb]
  exact (Modules.degree_congr K (fromSkeletonToSkeletonIso _)).trans
    (Modules.degree_pullback k K ((fromSkeleton X.Modules).obj L.val))

variable [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]

/-- Tensoring with the pullback of a class `M ∈ Pic X` of degree `e` sends classes of fibrewise
degree `d` to classes of fibrewise degree `d + e`. -/
lemma mul_map_fst_mem_picardSubfunctorDegree {T : Over (Spec (.of k))} {d e : ℤ} (M : X.Pic)
    (hM : picDegreeHom k X M = .ofAdd e) {L : (pullback (X ↘ Spec (.of k)) T.hom).Pic}
    (hL : L ∈ (picardSubfunctorDegree (X ↘ Spec (.of k)) d).obj (.op T)) :
    L * Pic.map (pullback.fst (X ↘ Spec (.of k)) T.hom) M ∈
      (picardSubfunctorDegree (X ↘ Spec (.of k)) (d + e)).obj (.op T) := fun K _ _ t ↦ by
  rw [picardFibreDegree_mul, hL K t, picardFibreDegree_map_fst]
  rw [picDegreeHom_apply, Hom.picDegree_eq] at hM
  rw [Multiplicative.ofAdd.injective hM]

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))] in
/-- Pulling a class back along `X_{T'} ⟶ X_T` commutes with tensoring by a class pulled back from
`X`. -/
lemma pic_map_baseChangeMap_mul_map_fst {T T' : Over (Spec (.of k))} (φ : T' ⟶ T)
    (L : (pullback (X ↘ Spec (.of k)) T.hom).Pic) (M : X.Pic) :
    Pic.map (baseChangeMap (X ↘ Spec (.of k)) φ)
        (L * Pic.map (pullback.fst (X ↘ Spec (.of k)) T.hom) M) =
      Pic.map (baseChangeMap (X ↘ Spec (.of k)) φ) L *
        Pic.map (pullback.fst (X ↘ Spec (.of k)) T'.hom) M := by
  have hb : baseChangeMap (X ↘ Spec (.of k)) φ ≫ pullback.fst (X ↘ Spec (.of k)) T.hom =
      pullback.fst (X ↘ Spec (.of k)) T'.hom :=
    pullback.lift_fst _ _ _ |>.trans (Category.comp_id _)
  rw [Pic.map_mul, ← Pic.map_comp, hb]

/-- Tensoring with the pullback of a class `M ∈ Pic X` of degree `e`, as a map from the
degree-`d` subfunctor of the Picard presheaf to the degree-`d'` subfunctor, `d' = d + e`. -/
noncomputable def picardSubfunctorDegreeMulMapFst {d d' e : ℤ} (M : X.Pic)
    (hM : picDegreeHom k X M = .ofAdd e) (h : d' = d + e) :
    (picardSubfunctorDegree (X ↘ Spec (.of k)) d).toFunctor ⟶
      (picardSubfunctorDegree (X ↘ Spec (.of k)) d').toFunctor where
  app T := TypeCat.ofHom fun L ↦
    ⟨(show (pullback (X ↘ Spec (.of k)) T.unop.hom).Pic from L.1) *
        Pic.map (pullback.fst (X ↘ Spec (.of k)) T.unop.hom) M, by
      rw [h]
      exact mul_map_fst_mem_picardSubfunctorDegree M hM L.2⟩
  naturality {T T'} φ := by
    ext L
    exact Subtype.ext (pic_map_baseChangeMap_mul_map_fst φ.unop L.1 M).symm

lemma picardSubfunctorDegreeMulMapFst_app_val {d d' e : ℤ} (M : X.Pic)
    (hM : picDegreeHom k X M = .ofAdd e) (h : d' = d + e) (T : (Over (Spec (.of k)))ᵒᵖ)
    (L : (picardSubfunctorDegree (X ↘ Spec (.of k)) d).toFunctor.obj T) :
    ((picardSubfunctorDegreeMulMapFst M hM h).app T L).1 =
      (show (pullback (X ↘ Spec (.of k)) T.unop.hom).Pic from L.1) *
        Pic.map (pullback.fst (X ↘ Spec (.of k)) T.unop.hom) M :=
  rfl

/-- **Translating the degree.** Tensoring with the pullback of a class `M ∈ Pic X` of degree `e`
is an isomorphism from the degree-`d` subfunctor of the Picard presheaf onto the degree-`d'`
subfunctor, `d' = d + e`, with inverse the tensor product with the pullback of `M⁻¹`. -/
noncomputable def picardSubfunctorDegreeIsoOfDegree {d d' e : ℤ} (M : X.Pic)
    (hM : picDegreeHom k X M = .ofAdd e) (h : d' = d + e) :
    (picardSubfunctorDegree (X ↘ Spec (.of k)) d).toFunctor ≅
      (picardSubfunctorDegree (X ↘ Spec (.of k)) d').toFunctor where
  hom := picardSubfunctorDegreeMulMapFst M hM h
  inv := picardSubfunctorDegreeMulMapFst M⁻¹ (by rw [map_inv, hM, ofAdd_neg]) (e := -e)
    (by omega)
  hom_inv_id := by
    ext T L
    refine Subtype.ext ?_
    change _ * _ * _ = _
    rw [show Pic.map _ M⁻¹ = (Pic.map _ M)⁻¹ from map_inv (Pic.mapHom _) M,
      mul_inv_cancel_right]
    rfl
  inv_hom_id := by
    ext T L
    refine Subtype.ext ?_
    change _ * _ * _ = _
    rw [show Pic.map _ M⁻¹ = (Pic.map _ M)⁻¹ from map_inv (Pic.mapHom _) M,
      inv_mul_cancel_right]
    rfl

end DegreeShift

section AbelMap

open scoped AlgebraicGeometry.Scheme.Modules

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The fibrewise degree of a class at a point `t` of the base is the degree of its restriction
to the fibre `X_t` over the residue field `κ(t)`. -/
lemma picardPresheafDegree_eq_degree (f : X ⟶ Spec (.of k)) {T : Over (Spec (.of k))}
    (L : (picardPresheaf f).obj (.op T)) (t : T.left) :
    letI := (pullback.snd f T.hom).fiberOverSpecResidueField t
    picardPresheafDegree f L t = Modules.degree (T.left.residueField t)
      ((Modules.pullback ((pullback.snd f T.hom).fiberι t)).obj
        ((fromSkeleton _).obj (Pic.val (Y := pullback f T.hom) L))) := by
  let := (pullback.snd f T.hom).fiberOverSpecResidueField t
  refine congrArg (_ - ·) ?_
  exact Modules.eulerChar_congr _ (Modules.pullbackObjUnitIso _)

variable (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f]

/-- The class `𝒪_{X_T}(D)` in `Pic (X_T)` of a point `D` of the Hilbert functor `Hilb^d_{X/k}(T)`:
`D` is a relative effective Cartier divisor (`AlgebraicGeometry.IsHilbertSubscheme.isInvertible`),
and `𝒪(D)` is the dual of its ideal sheaf. -/
noncomputable def abelClass {d : ℕ} {T : Over (Spec (.of k))}
    (D : (hilbertPresheaf f d).obj (.op T)) : (pullback f T.hom).Pic :=
  have := D.2.isInvertible.isInvertible_dual_toModules
  Pic.ofIsInvertible D.1.toModulesᵛ

/-- The chosen representative of `𝒪(D)` is the dual of the ideal sheaf of `D`. -/
noncomputable def abelClassIso {d : ℕ} {T : Over (Spec (.of k))}
    (D : (hilbertPresheaf f d).obj (.op T)) :
    (fromSkeleton _).obj (abelClass f D).val ≅ D.1.toModulesᵛ :=
  have := D.2.isInvertible.isInvertible_dual_toModules
  Pic.ofIsInvertibleIso _

/-- The class `𝒪(D)` is compatible with base change: `𝒪(D)_{T'} = 𝒪(D_{T'})`. -/
lemma pic_map_abelClass {d : ℕ} {T T' : Over (Spec (.of k))} (φ : T' ⟶ T)
    (D : (hilbertPresheaf f d).obj (.op T)) :
    Pic.map (baseChangeMap f φ) (abelClass f D) =
      abelClass f ((hilbertPresheaf f d).map φ.op D) := by
  have := D.2.isInvertible.isInvertible_dual_toModules
  have := ((hilbertPresheaf f d).map φ.op D).2.isInvertible.isInvertible_dual_toModules
  obtain ⟨e⟩ := D.2.isInvertible.nonempty_pullback_dual_toModules_iso (baseChangeMap f φ)
    ((hilbertPresheaf f d).map φ.op D).2.isInvertible
  exact Pic.eq_iff_nonempty_iso.2 ⟨fromSkeletonToSkeletonIso _ ≪≫
    (Modules.pullback _).mapIso (abelClassIso f D) ≪≫ e ≪≫
    (abelClassIso f ((hilbertPresheaf f d).map φ.op D)).symm⟩

variable [IsProper f]

/-- **`𝒪(D)` has fibrewise degree `d`** for a point `D` of `Hilb^d_{X/k}(T)`: on the fibre `X_t`,
`𝒪(D)_t = 𝒪(D_t)` has degree `dim_{κ(t)} Γ(D_t, 𝒪) = d` by Riemann–Roch
(`AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.degree_dual_toModules`). -/
lemma abelClass_mem {d : ℕ} {T : Over (Spec (.of k))} (D : (hilbertPresheaf f d).obj (.op T)) :
    abelClass f D ∈ (picardSubfunctorDegree f d).obj (.op T) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  refine (mem_picardSubfunctorDegree_iff f d _).2 fun t ↦ ?_
  let π := pullback.snd f T.hom
  let κ := T.left.residueField t
  let := π.fiberOverSpecResidueField t
  have := smoothOfRelativeDimension_isStableUnderBaseChange 1
  have : SmoothOfRelativeDimension 1 π :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ ‹_›
  have : IsProper π := MorphismProperty.pullback_snd (P := @IsProper) _ _ ‹_›
  have : SmoothOfRelativeDimension 1 (π.fiber t ↘ Spec κ) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ ‹_›
  have : IsProper (π.fiber t ↘ Spec κ) :=
    MorphismProperty.pullback_snd (P := @IsProper) _ _ ‹_›
  obtain ⟨hfin, hflat, -, hrank⟩ := D.2
  have hI := D.2.isInvertible
  have := hI.isInvertible_dual_toModules
  -- the fibre `D_t` is an effective Cartier divisor on `X_t`
  have hDt : (D.1.comap (π.fiberι t)).IsInvertible :=
    (IdealSheafData.IsRelativeEffectiveCartier.isRelativeEffectiveCartier_comap_of_isPullback
      ⟨hI, hflat⟩
      (IsPullback.of_hasPullback π (T.left.fromSpecResidueField t))).1
  obtain ⟨e⟩ := hI.nonempty_pullback_dual_toModules_iso (π.fiberι t) hDt
  rw [picardPresheafDegree_eq_degree, Modules.degree_congr κ
    ((Modules.pullback _).mapIso (abelClassIso f D) ≪≫ e), hDt.degree_dual_toModules]
  exact_mod_cast ((Scheme.IdealSheafData.finrank_subschemeι_comp_eq_finrankΓ π D.1 t).symm.trans
    (hrank t))

/-- **The Abel map** `Hilb^d_{X/k} ⟶ Pic^d_{X/k}` at the level of presheaves: a relative effective
Cartier divisor `D ⊆ X_T` of degree `d` is sent to the class of `𝒪_{X_T}(D)`, which has fibrewise
degree `d` (`AlgebraicGeometry.abelClass_mem`). The Hilbert functor is `Type u`-valued, so it is
composed with `CategoryTheory.uliftFunctor`. -/
noncomputable def abelMapPresheaf (d : ℕ) :
    hilbertPresheaf f d ⋙ uliftFunctor.{u + 1, u} ⟶ (picardSubfunctorDegree f d).toFunctor where
  app T := TypeCat.ofHom fun D ↦ ⟨abelClass f D.down, abelClass_mem f D.down⟩
  naturality {T T'} φ := by
    ext D
    exact Subtype.ext (pic_map_abelClass f φ.unop D.down).symm

lemma abelMapPresheaf_app_val (d : ℕ) (T : (Over (Spec (.of k)))ᵒᵖ)
    (D : (hilbertPresheaf f d ⋙ uliftFunctor.{u + 1, u}).obj T) :
    ((abelMapPresheaf f d).app T D).1 = abelClass f D.down :=
  rfl

end AbelMap

section GeometricPoints

open scoped AlgebraicGeometry.Scheme.Modules

variable {k : Type u} [Field k]

/-- **Sections of an fppf sheafification over an algebraically closed field.** Let `K` be an
algebraically closed field over `k`. Every section over `Spec K` of the fppf sheafification of a
presheaf `P` on `k`-schemes comes from a section of `P`: an fppf covering of `Spec K` has a member
with a closed point, which is a `K`-rational point (Hilbert's Nullstellensatz), i.e. a section of
the covering. -/
lemma exists_toSheafify_app_eq_of_isAlgClosed {K : Type u} [Field K] [Algebra k K]
    [IsAlgClosed K] (P : (Over (Spec (.of k)))ᵒᵖ ⥤ Type (u + 1))
    (s : (sheafify (fppfTopology.over (Spec (.of k))) P).obj
      (.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))))) :
    ∃ a, (toSheafify (fppfTopology.over (Spec (.of k))) P).app _ a = s := by
  let J := fppfTopology.over (Spec (.of k))
  let T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  obtain ⟨t₀⟩ : Nonempty T.left := inferInstanceAs (Nonempty (Spec (.of K)))
  obtain ⟨Z, g, ⟨a, ha⟩, -, hg, z, -⟩ := exists_flat_mem_of_mem_fppfTopology_over
    (Presheaf.imageSieve_mem J (toSheafify J P) s) t₀
  have : JacobsonSpace Z.left := LocallyOfFiniteType.jacobsonSpace g.left
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (Z := Set.univ) ⟨z, trivial⟩
    isClosed_univ.isLocallyClosed
  let τ : T ⟶ Z := Over.homMk (pointOfClosedPoint g.left x hx) (by
    rw [← Over.w g, pointOfClosedPoint_comp_assoc]
    rfl)
  have hτ : τ ≫ g = 𝟙 T := by
    ext1
    exact pointOfClosedPoint_comp g.left x hx
  refine ⟨P.map τ.op a, ?_⟩
  refine (NatTrans.naturality_apply (toSheafify J P) τ.op a).trans ?_
  rw [ha, ← Functor.map_comp_apply, ← op_comp, hτ, op_id]
  exact Functor.map_id_apply (sheafify J P) _ _

variable {X : Scheme.{u}} [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [GeometricallyIntegral (X ↘ Spec (.of k))]

/-- **A class of degree `g` is effective.** Let `X` be a smooth projective curve of genus `g` over
`k`, let `K/k` be a field extension and let `ℒ ∈ Pic (X_K)` have degree `g`. Then `ℒ ≅ 𝒪(D)` for a
point `D` of `Hilb^g_{X/k}(K)`: by Riemann–Roch `h⁰(ℒ) ≥ χ(ℒ) = g + 1 - g = 1`, and the zero
scheme of a nonzero section of `ℒ` on the integral curve `X_K` is an effective Cartier divisor of
degree `deg ℒ = g`.

(blueprint: `thm-sc-theorem-of-the-base`, surjectivity of `Hilb^g ⟶ Pic^g`) -/
theorem exists_abelClass_eq (K : Type u) [Field K] [Algebra k K]
    (L : (picardSubfunctorDegree (X ↘ Spec (.of k)) (arithmeticGenus k X)).toFunctor.obj
      (.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))))) :
    ∃ D : (hilbertPresheaf (X ↘ Spec (.of k)) (arithmeticGenus k X)).obj
      (.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))),
      abelClass (X ↘ Spec (.of k)) D = L.1 := by
  let T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let XK := pullback (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let π : XK ⟶ Spec (.of K) :=
    pullback.snd (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let : XK.Over (Spec (.of K)) := ⟨π⟩
  obtain ⟨h₁, h₂, h₃, h₄⟩ :=
    smoothOfRelativeDimension_and_isProper_and_geometricallyIntegral_pullback_snd
      (X ↘ Spec (.of k)) K
  have : SmoothOfRelativeDimension 1 (XK ↘ Spec (.of K)) := h₁
  have : IsProper (XK ↘ Spec (.of K)) := h₂
  have : GeometricallyIntegral (XK ↘ Spec (.of K)) := h₃
  have : IsIntegral XK := h₄
  have : GlobalSectionsBijective K XK := .of_geometricallyIntegral
  let ℒ : XK.Modules := (fromSkeleton _).obj (Pic.val (Y := XK) L.1)
  have : SheafOfModules.IsInvertible.{u, u, u} ℒ := Pic.isInvertible (Y := XK) L.1
  have : Modules.IsInvertible ℒ := Modules.IsInvertible.of_sheafOfModules _
  -- `deg ℒ = g`
  have hdeg : ℒ.degree K = arithmeticGenus k X := by
    have h := L.2 K (𝟙 T)
    rwa [picardFibreDegree, baseChangeMap_id, Pic.map_id] at h
  -- `h⁰(ℒ) ≥ χ(ℒ) = 1`
  have hχ := Modules.eulerChar_eq_degree_add (k := K) ℒ
  have hg : arithmeticGenus K XK = arithmeticGenus k X := arithmeticGenus_pullback (k := k) K
  rw [hdeg, hg] at hχ
  have h01 := Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one (k := K) ℒ
  have hpos : 0 < ℒ.finrankH K 0 := by omega
  have : Nontrivial (ℒ.H 0) := Module.nontrivial_of_finrank_pos (R := K) hpos
  obtain ⟨s, hs⟩ := Modules.exists_ne_zero_of_nontrivial_H_zero ℒ
  -- the zero scheme `D` of `s`
  have := Modules.IsInvertible.sheafOfModules_isInvertible (𝟙_ XK.Modules)
  let D := Modules.Hom.zeroLocus s
  have hD : D.IsInvertible := (Modules.Hom.isLocallyPrincipal_zeroLocus s).isInvertible
    fun h ↦ hs ((Modules.Hom.zeroLocus_eq_bot_iff s).1 h)
  have := hD.isInvertible_dual_toModules
  obtain ⟨e⟩ := Modules.Hom.nonempty_iso_dual_toModules_tensorObj s hD
  have hfin : IsFinite (D.subschemeι ≫ π) := hD.isFinite_subschemeι_comp (k := K)
  have hrank : (D.subschemeι ≫ π).finrankΓ = arithmeticGenus k X := by
    have h := hD.degree_dual_toModules (k := K)
    rw [← Modules.degree_congr K (e ≪≫ ρ_ _), hdeg] at h
    exact_mod_cast h.symm
  have hflat : Flat (D.subschemeι ≫ π) := inferInstance
  have hlfp : LocallyOfFinitePresentation (D.subschemeι ≫ π) := inferInstance
  refine ⟨⟨D, hfin, hflat, hlfp, fun t ↦ ?_⟩, ?_⟩
  · exact (Scheme.Hom.finrank_eq_fiberDegree (D.subschemeι ≫ π) t).trans
      ((fiberDegree_eq_finrankΓ _ t).trans hrank)
  · refine Pic.eq_iff_nonempty_iso.2 ⟨abelClassIso (X ↘ Spec (.of k)) _ ≪≫ ?_⟩
    exact (e ≪≫ ρ_ _).symm

end GeometricPoints

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

/-- **All the degree components are isomorphic.** Schemes representing `Pic^0_{X/k}` and
`Pic^d_{X/k}` are isomorphic as `k`-schemes; the isomorphism is tensoring with `𝒪_X(dP)` for a
rational point `P`, which cannot be named for lack of the twisting sheaf.

(blueprint: `sk-prop-picard-degree-decomposition`) -/
theorem nonempty_iso_of_representableBy (d : ℤ) (P₀ Pd : Over (Spec (.of k)))
    (hP₀ : (picardFunctorDegree (X ↘ Spec (.of k)) 0).obj.RepresentableBy P₀)
    (hPd : (picardFunctorDegree (X ↘ Spec (.of k)) d).obj.RepresentableBy Pd) :
    Nonempty (P₀ ≅ Pd) := by
  -- a class `M = 𝒪_X(x)^d` of degree `d`, for a rational point `x`
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton (X ↘ Spec (.of k))
  obtain ⟨x⟩ := Hom.nonempty_fieldPoints (k := k) (X ↘ Spec (.of k))
  have hJ := Hom.isInvertible_ker_fieldPoints x
  have := hJ.isInvertible_toModules
  let M : X.Pic := Pic.ofIsInvertible x.1.ker.toModules ^ (-d)
  have hM : picDegreeHom k X M = .ofAdd d := by
    rw [map_zpow, picDegreeHom_ofIsInvertible, degree_toModules_ker_fieldPoints, ← ofAdd_zsmul,
      smul_eq_mul, neg_mul_neg, _root_.mul_one]
  -- tensoring with `M` identifies `Pic^0_{X/k}` with `Pic^d_{X/k}`
  let e := picardSubfunctorDegreeIsoOfDegree M hM (d := 0) (d' := d) (zero_add d).symm
  exact ⟨hP₀.uniqueUpToIso (hPd.ofIso ((sheafToPresheaf _ _).mapIso
    ((presheafToSheaf (fppfTopology.over (Spec (.of k))) (Type (u + 1))).mapIso e)).symm)⟩

/-- **`Pic^g` is smooth of dimension `g`.** A `k`-scheme representing the degree-`g` part
`Pic^g_{X/k}` of the Picard functor, `g` the genus, is smooth of relative dimension `g` over `k`:
it is an open subscheme of the Picard scheme
(`AlgebraicGeometry.exists_decomposition_picardFunctor`),
which is smooth of dimension `g`, being covered by translates of an open subscheme of the smooth
`g`-dimensional `Hilb^g_{X/k}`
(`AlgebraicGeometry.smoothOfRelativeDimension_of_representableBy_picardFunctor`).

(blueprint: `thm-sc-theorem-of-the-base`, smoothness of `Pic^g`) -/
theorem smoothOfRelativeDimension_of_representableBy_picardFunctorDegree_genus
    (P : Over (Spec (.of k)))
    (hP : (picardFunctorDegree (X ↘ Spec (.of k)) (arithmeticGenus k X)).obj.RepresentableBy P) :
    SmoothOfRelativeDimension (arithmeticGenus k X) P.hom := by
  obtain ⟨A, -, hA, -⟩ := isRepresentable_picardFunctor (X ↘ Spec (.of k))
  obtain ⟨Pd, j, hj, -, -, -, hPd⟩ := exists_decomposition_picardFunctor A hA
  obtain ⟨hg⟩ := hPd (arithmeticGenus k X)
  have := smoothOfRelativeDimension_of_representableBy_picardFunctor A hA
  have := hj (arithmeticGenus k X)
  have := smoothOfRelativeDimension_comp (n := 0) (m := arithmeticGenus k X)
    (j (arithmeticGenus k X)).left A.hom
  rw [zero_add, Over.w (j _)] at this
  let e := hP.uniqueUpToIso hg
  rw [← Over.w e.hom, MorphismProperty.cancel_left_of_respectsIso
    (P := @SmoothOfRelativeDimension (arithmeticGenus k X))]
  exact this

omit [IsSepClosed k] in
/-- **The Abel map `Hilb^g ⟶ Pic^g` is surjective.** For a `k`-scheme `P` representing
`Pic^g_{X/k}`, `g` the genus, there are a proper geometrically integral `k`-scheme `H` (the
Hilbert scheme `Hilb^g_{X/k}`) and a morphism `a : H ⟶ P` of `k`-schemes, `D ↦ 𝒪_X(D)`
(`AlgebraicGeometry.abelMapPresheaf`), which is surjective: a point `p` of `P` gives a class of
degree `g` over an algebraic closure `K` of `κ(p)`, which comes from `Pic (X_K)`
(`AlgebraicGeometry.exists_toSheafify_app_eq_of_isAlgClosed`) and is effective by Riemann–Roch
(`AlgebraicGeometry.exists_abelClass_eq`).

(blueprint: `thm-sc-theorem-of-the-base`, the map `γ_g : Hilb^g ⟶ Pic^g`) -/
theorem exists_surjective_of_representableBy_picardFunctorDegree_genus (P : Over (Spec (.of k)))
    (hP : (picardFunctorDegree (X ↘ Spec (.of k)) (arithmeticGenus k X)).obj.RepresentableBy P) :
    ∃ (H : Over (Spec (.of k))) (a : H ⟶ P), IsProper H.hom ∧ GeometricallyIntegral H.hom ∧
      Surjective a.left := by
  obtain ⟨H, q, -, hq, hqi, eH, -⟩ :=
    hilbertPresheaf_curve_representable (X ↘ Spec (.of k)) (arithmeticGenus k X)
  let J := fppfTopology.over (Spec (.of k))
  let S := picardSubfunctorDegree (X ↘ Spec (.of k)) (arithmeticGenus k X)
  let Φ := abelMapPresheaf (X ↘ Spec (.of k)) (arithmeticGenus k X)
  -- the class of the universal divisor, and the Abel morphism `a`
  let ab : (picardFunctorDegree (X ↘ Spec (.of k)) (arithmeticGenus k X)).obj.obj
      (.op (Over.mk q)) :=
    (toSheafify J S.toFunctor).app _ (Φ.app _ (ULift.up (eH.homEquiv (𝟙 _))))
  let a : Over.mk q ⟶ P := hP.homEquiv.symm ab
  have hab {T : Over (Spec (.of k))} (h : T ⟶ Over.mk q) :
      hP.homEquiv (h ≫ a) =
        (toSheafify J S.toFunctor).app _ (Φ.app _ (ULift.up (eH.homEquiv h))) := by
    rw [hP.homEquiv_comp, hP.homEquiv.apply_symm_apply]
    have h₃ : eH.homEquiv h = (hilbertPresheaf _ _).map h.op (eH.homEquiv (𝟙 _)) := by
      simpa using eH.homEquiv_comp h (𝟙 _)
    rw [h₃]
    refine (NatTrans.naturality_apply (toSheafify J S.toFunctor) h.op _).symm.trans ?_
    exact congrArg _ (NatTrans.naturality_apply Φ h.op _).symm
  refine ⟨Over.mk q, a, hq, hqi, ⟨fun p ↦ ?_⟩⟩
  -- a geometric point `x : Spec K ⟶ P` over `p`
  let κ := P.left.residueField p
  let φ : CommRingCat.of k ⟶ κ := Spec.preimage (P.left.fromSpecResidueField p ≫ P.hom)
  let K := AlgebraicClosure κ
  let : Algebra k K := ((algebraMap κ K).comp φ.hom).toAlgebra
  have hK : Spec.map (CommRingCat.ofHom (algebraMap k K)) =
      Spec.map (CommRingCat.ofHom (algebraMap κ K)) ≫ P.left.fromSpecResidueField p ≫ P.hom := by
    rw [← Spec.map_preimage (P.left.fromSpecResidueField p ≫ P.hom), ← Spec.map_comp]
    rfl
  let x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ P :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap κ K)) ≫ P.left.fromSpecResidueField p)
      (by rw [Category.assoc]; exact hK.symm)
  -- the class of `x` comes from an effective divisor of degree `g` on `X_K`
  obtain ⟨L, hL⟩ := exists_toSheafify_app_eq_of_isAlgClosed S.toFunctor (hP.homEquiv x)
  obtain ⟨D, hD⟩ := exists_abelClass_eq K L
  let h : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk q :=
    eH.homEquiv.symm D
  have hx : h ≫ a = x := by
    refine hP.homEquiv.injective ?_
    rw [hab, ← hL]
    refine congrArg _ (Subtype.ext ?_)
    rw [abelMapPresheaf_app_val]
    simpa [h] using hD
  obtain ⟨pt⟩ : Nonempty (Spec (.of K)) := inferInstance
  refine ⟨h.left pt, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hx]
  change (P.left.fromSpecResidueField p) _ = p
  exact Scheme.fromSpecResidueField_apply _ _

/-- **`Pic^g` is proper.** A `k`-scheme `P` representing the degree-`g` part `Pic^g_{X/k}` of
the Picard functor, `g` the genus, is proper over `k`. The Abel map `Hilb^g_{X/k} ⟶ P`,
`D ↦ 𝒪_X(D)`, is surjective
(`AlgebraicGeometry.exists_surjective_of_representableBy_picardFunctorDegree_genus`), so `P` is
the image of the proper `Hilb^g_{X/k}`; it is locally of finite type, being smooth, and separated,
being an open subscheme of the Picard scheme, a group scheme over a field. Hence `P` is proper
(Stacks `03GN`).

(blueprint: `thm-sc-theorem-of-the-base`, properness of `Pic^g`) -/
theorem isProper_of_representableBy_picardFunctorDegree_genus (P : Over (Spec (.of k)))
    (hP : (picardFunctorDegree (X ↘ Spec (.of k)) (arithmeticGenus k X)).obj.RepresentableBy P) :
    IsProper P.hom := by
  obtain ⟨H, a, hH, -, ha⟩ := exists_surjective_of_representableBy_picardFunctorDegree_genus P hP
  -- `P` is separated: an open subscheme of the Picard scheme, a group scheme over `k`
  obtain ⟨A, hAg, hA, -⟩ := isRepresentable_picardFunctor (X ↘ Spec (.of k))
  obtain ⟨Pd, j, hj, -, -, -, hPd⟩ := exists_decomposition_picardFunctor A hA
  obtain ⟨hg⟩ := hPd (arithmeticGenus k X)
  have := hj (arithmeticGenus k X)
  have hsep : IsSeparated P.hom := by
    rw [← Over.w (hP.uniqueUpToIso hg).hom, MorphismProperty.cancel_left_of_respectsIso
      (P := @IsSeparated), ← Over.w (j _)]
    have : IsSeparated A.hom := GrpObj.isSeparated_hom A
    have : IsSeparated (j (arithmeticGenus k X)).left := inferInstance
    infer_instance
  -- `P` is locally of finite type, being smooth
  have := smoothOfRelativeDimension_of_representableBy_picardFunctorDegree_genus P hP
  have : Smooth P.hom := SmoothOfRelativeDimension.smooth (arithmeticGenus k X) _
  -- `P` is universally closed, being the image of the proper `H`
  have : UniversallyClosed (a.left ≫ P.hom) := by
    rw [Over.w a]
    infer_instance
  have : UniversallyClosed P.hom := .of_comp_surjective a.left P.hom
  exact ⟨⟩

/-- Two representing objects of degree components of the Picard functor are isomorphic over
`k`: both are isomorphic to a representing object of `Pic^0_{X/k}`. -/
lemma nonempty_iso_of_representableBy_picardFunctorDegree (d d' : ℤ) (P P' : Over (Spec (.of k)))
    (hP : (picardFunctorDegree (X ↘ Spec (.of k)) d).obj.RepresentableBy P)
    (hP' : (picardFunctorDegree (X ↘ Spec (.of k)) d').obj.RepresentableBy P') :
    Nonempty (P ≅ P') := by
  obtain ⟨A, -, hA, -⟩ := isRepresentable_picardFunctor (X ↘ Spec (.of k))
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
  obtain ⟨A, -, hA, -⟩ := isRepresentable_picardFunctor (X ↘ Spec (.of k))
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
    GeometricallyIntegral P.hom := by
  obtain ⟨H, a, -, hH, ha⟩ := exists_surjective_of_representableBy_picardFunctorDegree_genus P hP
  have := smoothOfRelativeDimension_of_representableBy_picardFunctorDegree_genus P hP
  have : Smooth P.hom := SmoothOfRelativeDimension.smooth (arithmeticGenus k X) _
  have : GeometricallyIrreducible (a.left ≫ P.hom) := by
    rw [Over.w a]
    infer_instance
  have := GeometricallyIrreducible.of_surjective a.left P.hom
  exact .of_geometricallyReduced_of_geometricallyIrreducible _


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

/-- The tangent subgroup is the subgroup `AlgebraicGeometry.GrpObj.infPoints P` of infinitesimal
points of the group scheme `P`. -/
lemma tangentSubgroup_eq_infPoints : tangentSubgroup P = GrpObj.infPoints P := by
  ext v
  rw [GrpObj.mem_infPoints, ← MonObj.one_eq_one]
  rfl

/-- The kernel of `P(k[ε]) → P(k)` is commutative, even when `P` is not: it is the group of
infinitesimal points of `P` (`AlgebraicGeometry.GrpObj.isMulCommutative_infPoints`). -/
instance : IsMulCommutative (tangentSubgroup P) := by
  rw [tangentSubgroup_eq_infPoints]
  exact GrpObj.isMulCommutative_infPoints P

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
    (c + d) • v = c • v + d • v := by
  -- transport along the bijection `GrpObj.lieEquiv` with the Lie algebra, which turns the group
  -- law into the addition and rescaling into the scalar action of `Γ(Spec k, 𝒪)`
  have hv : v.1 ∈ GrpObj.infPoints P := by
    rw [← tangentSubgroup_eq_infPoints]
    exact v.2
  let r : k →+* Γ(Spec (.of k), ⊤) := (Scheme.ΓSpecIso (.of k)).inv.hom
  have key : GrpObj.infPointsScale P (r (c + d)) ⟨v.1, hv⟩ =
      GrpObj.infPointsScale P (r c) ⟨v.1, hv⟩ * GrpObj.infPointsScale P (r d) ⟨v.1, hv⟩ := by
    refine (GrpObj.lieEquiv P).injective ?_
    rw [GrpObj.lieEquiv_mul]
    change GrpObj.toLie P _ = GrpObj.toLie P _ + GrpObj.toLie P _
    rw [GrpObj.toLie_infPointsScale, GrpObj.toLie_infPointsScale, GrpObj.toLie_infPointsScale,
      map_add, _root_.add_smul]
  exact Subtype.ext congr(Subtype.val $key)

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

section OnePoint

variable [IsSepClosed k] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [GeometricallyIntegral (X ↘ Spec (.of k))]

/-- **`Pic^0_{X/k}` over a one-point base.** If `T` is a `k`-scheme with a single point, every
section of `Pic^0_{X/k}` over `T` is the image of a unique class of fibrewise degree zero on
`X_T`: an invertible module on `T` is trivial, so `Pic (X_T) ≅ Pic_{X/k}(T)` by the split exact
sequence (`AlgebraicGeometry.bijective_pic_split`). -/
lemma bijective_toSheafify_app_picardSubfunctorDegree_zero (T : Over (Spec (.of k)))
    [Subsingleton T.left] (t₀ : T.left) :
    Function.Bijective ((toSheafify (fppfTopology.over (Spec (.of k)))
      (picardSubfunctorDegree (X ↘ Spec (.of k)) 0).toFunctor).app (.op T)) := by
  set f := X ↘ Spec (.of k)
  let J := fppfTopology.over (Spec (.of k))
  let S := picardSubfunctorDegree f 0
  let α : S.toFunctor ⟶ (picardFunctor f).obj := S.ι ≫ toPicardFunctor f
  let β : picardFunctorDegree f 0 ⟶ picardFunctor f :=
    ⟨sheafifyLift J α (picardFunctor f).property⟩
  have fac : toSheafify J S.toFunctor ≫ β.hom = α := toSheafify_sheafifyLift J α _
  have : Presheaf.IsLocallyInjective J α := inferInstance
  have : Presheaf.IsLocallyInjective J β.hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac J α fac
  have hβ : Function.Injective (β.hom.app (.op T)) :=
    (Sheaf.isLocallyInjective_iff_injective β).1 this _
  have hβS {T' : Over (Spec (.of k))} (M : S.toFunctor.obj (.op T')) :
      β.hom.app _ ((toSheafify J S.toFunctor).app _ M) = (toPicardFunctor f).app _ M.1 :=
    ConcreteCategory.congr_hom (NatTrans.congr_app fac (.op T')) M
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
  obtain ⟨pt⟩ := Hom.nonempty_fieldPoints (k := k) f
  have hσ : pt.1 ≫ f = 𝟙 _ := by
    rw [pt.2, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have hsplit := bijective_pic_split f pt.1 hσ
    isIso_pushforwardUnitMap_pullback_snd_of_geometricallyIntegral T
  have hone (a : T.left.Pic) : a = 1 := by
    have := a.isInvertible
    obtain ⟨e⟩ := Modules.IsInvertible.nonempty_iso_unit t₀ ((fromSkeleton _).obj a.val)
    exact Pic.eq_iff_nonempty_iso.2 ⟨e ≪≫ Pic.oneIso.symm⟩
  refine ⟨fun L₁ L₂ h ↦ ?_, fun s ↦ ?_⟩
  · have h' := congrArg (β.hom.app _) h
    rw [hβS, hβS] at h'
    exact Subtype.ext (hsplit.1 (Prod.ext ((hone _).trans (hone _).symm) h'))
  · have hdeg (t : T.left) : picardDegree f (β.hom.app _ s) t = 0 := by
      obtain ⟨Z, g, ⟨a, ha⟩, -, -, z, rfl⟩ := exists_flat_mem_of_mem_fppfTopology_over
        (Presheaf.imageSieve_mem J (toSheafify J S.toFunctor) s) t
      rw [← picardDegree_map, ← NatTrans.naturality_apply β.hom,
        show (picardFunctorDegree f 0).obj.map g.op s = (toSheafify J S.toFunctor).app _ a from
          ha.symm, hβS, picardDegree_toPicardFunctor]
      exact (mem_picardSubfunctorDegree_iff f 0 a.1).1 a.2 z
    obtain ⟨M, hM⟩ := hsplit.2 (1, β.hom.app _ s)
    have hM₂ : (toPicardFunctor f).app _ M = β.hom.app _ s := congrArg Prod.snd hM
    have hMS : M ∈ S.obj (.op T) := (mem_picardSubfunctorDegree_iff f 0 M).2 fun t ↦ by
      rw [← picardDegree_toPicardFunctor, hM₂]
      exact hdeg t
    exact ⟨⟨M, hMS⟩, hβ (by rw [hβS]; exact hM₂)⟩

omit [IsSepClosed k] [GeometricallyIntegral (X ↘ Spec (.of k))] in
/-- Over a one-point base `T`, a class which becomes trivial along some `φ : T' ⟶ T` has
fibrewise degree zero. -/
lemma mem_picardSubfunctorDegree_zero_of_map_eq_one {T T' : Over (Spec (.of k))} (φ : T' ⟶ T)
    [Subsingleton T.left] (t' : T'.left) (L : (pullback (X ↘ Spec (.of k)) T.hom).Pic)
    (hL : Pic.map (baseChangeMap (X ↘ Spec (.of k)) φ) L = 1) :
    L ∈ (picardSubfunctorDegree (X ↘ Spec (.of k)) 0).obj (.op T) := by
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  refine (mem_picardSubfunctorDegree_iff _ 0 L).2 fun t ↦ ?_
  rw [show t = φ.left t' from Subsingleton.elim _ _, ← picardPresheafDegree_map]
  have h1 := (picardSubgroupDegreeZero (X ↘ Spec (.of k)) T').one_mem
  have h2 := (mem_picardSubfunctorDegree_iff _ 0 _).1 h1 t'
  convert h2 using 2
  exact hL

end OnePoint

/-- **The tangent space of the Jacobian.** Let `X` be a smooth projective curve of genus `g`
over a separably closed field `k` and let `J` be a group scheme over `k` representing the
degree-zero part `Pic^0_{X/k}` of the Picard functor, the representation respecting the group
laws (`AlgebraicGeometry.IsPicardZeroMul`). Then the tangent space of `J` at the unit `η[J]` is
isomorphic as a `k`-vector space to `H^1(X, 𝒪_X)`, which has dimension `g` by the definition of
`AlgebraicGeometry.Scheme.arithmeticGenus`.

(blueprint: `sk-prop-picard-jacobian-tangent`) -/
theorem nonempty_tangentSpaceAt_linearEquiv_H_one [IsSepClosed k]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    [GeometricallyIntegral (X ↘ Spec (.of k))] (J : Over (Spec (.of k))) [GrpObj J]
    (e : (picardFunctorDegree (X ↘ Spec (.of k)) 0).obj.RepresentableBy J)
    (he : IsPicardZeroMul (X ↘ Spec (.of k)) e) :
    Nonempty (tangentSpaceAt J η[J] ≃ₗ[k] (Modules.unit X).H 1) := by
  let f := X ↘ Spec (.of k)
  let Jt := fppfTopology.over (Spec (.of k))
  let S := picardSubfunctorDegree f 0
  let Tε := Scheme.dualNumbersOver (Spec (.of k))
  let T₀ := 𝟙_ (Over (Spec (.of k)))
  let iε := Scheme.dualNumbersιOver (Spec (.of k))
  have : Subsingleton (Spec (.of k)).dualNumbers := inferInstanceAs (Subsingleton (Spec (.of k)))
  have : Subsingleton Tε.left := inferInstanceAs (Subsingleton (Spec (.of k)))
  have : Subsingleton T₀.left := inferInstanceAs (Subsingleton (Spec (.of k)))
  obtain ⟨p₀⟩ : Nonempty (Spec (.of k)) := inferInstance
  -- the points of `J` over `T` are the classes of fibrewise degree zero on `X_T`
  have hpts (T : Over (Spec (.of k))) [Subsingleton T.left] (t : T.left) :
      ∃ ψ : picardSubgroupDegreeZero f T ≃* (T ⟶ J), ∀ L,
        ψ L = e.homEquiv.symm ((toSheafify Jt S.toFunctor).app (.op T) L) := by
    obtain ⟨ψ, hψ⟩ := exists_mulEquiv_of_isPicardZeroMul f e he (T := T)
      (G := picardSubgroupDegreeZero f T) Subtype.val (fun _ _ ↦ rfl)
      (Equiv.ofBijective (fun L : picardSubgroupDegreeZero f T ↦
        (toSheafify Jt S.toFunctor).app (.op T) L)
        (bijective_toSheafify_app_picardSubfunctorDegree_zero T t))
      (fun g ↦ ⟨g.2, rfl⟩)
    exact ⟨ψ, hψ⟩
  obtain ⟨ψε, hψε⟩ := hpts Tε p₀
  obtain ⟨ψ₀, hψ₀⟩ := hpts T₀ p₀
  -- pulling back classes along a morphism of one-point bases
  have hnat {T T' : Over (Spec (.of k))} (φ : T' ⟶ T) (L : picardSubgroupDegreeZero f T) :
      φ ≫ e.homEquiv.symm ((toSheafify Jt S.toFunctor).app (.op T) L) =
        e.homEquiv.symm ((toSheafify Jt S.toFunctor).app (.op T')
          ⟨Pic.map (baseChangeMap f φ) L.1, S.map φ.op L.2⟩) := by
    rw [e.comp_homEquiv_symm]
    exact congrArg e.homEquiv.symm
      (NatTrans.naturality_apply (toSheafify Jt S.toFunctor) φ.op L).symm
  let res : picardSubgroupDegreeZero f Tε →* picardSubgroupDegreeZero f T₀ :=
    { toFun L := ⟨Pic.map (baseChangeMap f iε) L.1, S.map iε.op L.2⟩
      map_one' := Subtype.ext (Pic.map_one _)
      map_mul' L L' := Subtype.ext (Pic.map_mul _ L.1 L'.1) }
  have hres (L : picardSubgroupDegreeZero f Tε) : iε ≫ ψε L = ψ₀ (res L) := by
    rw [hψε, hψ₀]
    exact hnat iε L
  have hη : η[J] = ψ₀ 1 := by
    rw [map_one]
    exact MonObj.one_eq_one (M := J)
  -- the tangent space is the kernel of `res`
  let E₁ : tangentSubgroup J ≃* res.ker :=
    { toFun v := ⟨ψε.symm v.1, by
        rw [MonoidHom.mem_ker, ← ψ₀.injective.eq_iff, ← hres, MulEquiv.apply_symm_apply,
          map_one, ← MonObj.one_eq_one]
        exact v.2⟩
      invFun K := ⟨ψε K.1, by
        change iε ≫ ψε K.1 = η[J]
        rw [hres, K.2, hη]⟩
      left_inv v := Subtype.ext (ψε.apply_symm_apply v.1)
      right_inv K := Subtype.ext (ψε.symm_apply_apply K.1)
      map_mul' v w := Subtype.ext (map_mul ψε.symm v.1 w.1) }
  -- the base change `X_ε` is the thickening `X[ε]`, and `X_k` is `X`
  have hpb := Scheme.isPullback_dualNumbersProj f
  let eD : X.dualNumbers ≅ pullback f Tε.hom := hpb.isoPullback
  have hDfst : eD.hom ≫ pullback.fst f Tε.hom = X.dualNumbersProj := hpb.isoPullback_hom_fst
  have hDsnd : eD.hom ≫ pullback.snd f Tε.hom = f.dualNumbers := hpb.isoPullback_hom_snd
  have : IsIso (pullback.fst f T₀.hom) := by
    change IsIso (pullback.fst f (𝟙 _))
    infer_instance
  let e₀ : X ≅ pullback f T₀.hom := (asIso (pullback.fst f T₀.hom)).symm
  have hbfst {T T' : Over (Spec (.of k))} (φ : T' ⟶ T) :
      baseChangeMap f φ ≫ pullback.fst f T.hom = pullback.fst f T'.hom :=
    pullback.lift_fst _ _ _ |>.trans (Category.comp_id _)
  have hbsnd {T T' : Over (Spec (.of k))} (φ : T' ⟶ T) :
      baseChangeMap f φ ≫ pullback.snd f T.hom = pullback.snd f T'.hom ≫ φ.left :=
    pullback.lift_snd _ _ _
  have hiε : X.dualNumbersι ≫ eD.hom = e₀.hom ≫ baseChangeMap f iε := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hbfst, hDfst,
        Scheme.dualNumbersι_comp_proj]
      exact (asIso (pullback.fst f T₀.hom)).inv_hom_id.symm
    · rw [Category.assoc, Category.assoc, hbsnd, hDsnd,
        Scheme.Hom.ι_comp_dualNumbers]
      have he₀ : e₀.hom ≫ pullback.snd f T₀.hom = f := by
        change inv (pullback.fst f T₀.hom) ≫ pullback.snd f T₀.hom = f
        rw [IsIso.inv_comp_eq, pullback.condition]
        exact (Category.comp_id _).symm
      rw [← Category.assoc, he₀]
      rfl
  have hmapiε (L : (pullback f Tε.hom).Pic) :
      Pic.map X.dualNumbersι (Pic.map eD.hom L) =
        Pic.map e₀.hom (Pic.map (baseChangeMap f iε) L) := by
    rw [← Pic.map_comp, ← Pic.map_comp, hiε]
  have hmap₀ (L : (pullback f T₀.hom).Pic) : Pic.map e₀.hom L = 1 ↔ L = 1 := by
    refine ⟨fun h ↦ ?_, fun h ↦ h ▸ Pic.map_one _⟩
    rw [← Pic.map_id L, ← e₀.inv_hom_id, Pic.map_comp, h, Pic.map_one]
  let E₂ : res.ker ≃* (Pic.mapHom X.dualNumbersι).ker :=
    { toFun K := ⟨Pic.map eD.hom K.1.1, by
        rw [MonoidHom.mem_ker, Pic.mapHom_apply, hmapiε, hmap₀]
        exact congrArg Subtype.val K.2⟩
      invFun M := ⟨⟨Pic.map eD.inv M.1, mem_picardSubfunctorDegree_zero_of_map_eq_one iε p₀ _ (by
          rw [← hmap₀, ← hmapiε]
          simp only [← Pic.map_comp, Iso.hom_inv_id, Pic.map_id]
          exact M.2)⟩, by
          refine Subtype.ext ?_
          change Pic.map (baseChangeMap f iε) (Pic.map eD.inv M.1) = 1
          rw [← hmap₀, ← hmapiε]
          simp only [← Pic.map_comp, Iso.hom_inv_id, Pic.map_id]
          exact M.2⟩
      left_inv K := by
        refine Subtype.ext (Subtype.ext ?_)
        change Pic.map eD.inv (Pic.map eD.hom K.1.1) = K.1.1
        simp only [← Pic.map_comp, Iso.inv_hom_id, Pic.map_id]
      right_inv M := by
        refine Subtype.ext ?_
        change Pic.map eD.hom (Pic.map eD.inv M.1) = M.1
        simp only [← Pic.map_comp, Iso.hom_inv_id, Pic.map_id]
      map_mul' K K' := Subtype.ext (Pic.map_mul _ K.1.1 K'.1.1) }
  obtain ⟨Ψ, hΨ⟩ := Scheme.exists_addEquiv_ker_picMap_dualNumbersι X
  let A : tangentSpaceAt J η[J] ≃+ (Modules.unit X).H 1 :=
    ((E₁.trans E₂).toAdditive : Additive (tangentSubgroup J) ≃+ _).trans Ψ
  refine ⟨{ A with map_smul' := fun c v ↦ ?_ }⟩
  -- rescaling `ε` corresponds to multiplication by `c`
  let sc := dualNumbersScale k c
  let c' := Scheme.globalSectionsRingHom k (X := X) c
  have hsc : X.dualNumbersScale c' ≫ eD.hom = eD.hom ≫ baseChangeMap f sc := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hbfst, hDfst,
        Scheme.dualNumbersScale_comp_proj]
    · rw [Category.assoc, Category.assoc, hbsnd, hDsnd, ← Category.assoc,
        hDsnd]
      exact Scheme.dualNumbersScale_comp_dualNumbers f _
  let L := ψε.symm v.1
  have hscL : ψε.symm (c • v).1 =
      ⟨Pic.map (baseChangeMap f sc) L.1, S.map sc.op L.2⟩ := by
    rw [MulEquiv.symm_apply_eq, hψε]
    change sc ≫ v.1 = _
    rw [← hnat, ← hψε, MulEquiv.apply_symm_apply]
  change Ψ (.ofMul (E₂ (E₁ (c • v)))) = c • Ψ (.ofMul (E₂ (E₁ v)))
  refine (hΨ c' _ _ ?_).trans rfl
  change Pic.map eD.hom (ψε.symm (c • v).1).1 = Pic.map (X.dualNumbersScale c') (Pic.map eD.hom L.1)
  rw [hscL, ← Pic.map_comp, ← Pic.map_comp, hsc]

end TangentSpace

section Jacobian

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

variable (k X) in
/-- The degree-zero part `Pic^0(X) = {ℒ ∈ Pic X : deg ℒ = 0}` of the Picard group of a smooth
proper curve `X` over `k`: the kernel of the degree homomorphism
`AlgebraicGeometry.Scheme.picDegreeHom`, `deg ℒ = χ(ℒ) - χ(𝒪_X)`, a subgroup of `Pic X`. Its
underlying set is `AlgebraicGeometry.Scheme.Hom.picZero`
(`AlgebraicGeometry.Scheme.coe_ker_picDegreeHom`).

(blueprint: `sk-prop-jacobian`, `sk-def-pic`) -/
noncomputable abbrev picardZero [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] : Subgroup X.Pic :=
  (picDegreeHom k X).ker

/-- **The `k`-points of `Pic^0_{X/k}`.** For a smooth projective curve `X` over a separably
closed field `k`, the value of the degree-zero part `Pic^0_{X/k}` of the Picard functor on
`Spec k` is `Pic^0(X)`: the map sending `ℒ ∈ Pic^0(X)` to the image of its pullback to
`X ×_k k` is a bijection `Pic^0(X) ≃ Pic^0_{X/k}(k)`.  By the split exact sequence with
`T = Spec k` and `Pic (Spec k) = 0`, `Pic_{X/k}(k) = Pic X`, and its degree-zero part is
`Pic^0(X)`, the fibrewise degree being invariant under extension of the base field.

(blueprint: `thm-sc-jacobian-representability`, the `k`-points of `Pic^0_{X/k}`) -/
theorem exists_picardZero_equiv_picardFunctorDegree_zero [IsSepClosed k]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    [GeometricallyIntegral (X ↘ Spec (.of k))] :
    ∃ Φ : picardZero k X ≃
      (picardFunctorDegree (X ↘ Spec (.of k)) 0).obj.obj (.op (𝟙_ (Over (Spec (.of k))))),
      ∀ L, ∃ h, Φ L = (toSheafify (fppfTopology.over (Spec (.of k)))
        (picardSubfunctorDegree (X ↘ Spec (.of k)) 0).toFunctor).app _
          ⟨Pic.map (pullback.fst (X ↘ Spec (.of k)) (𝟙_ (Over (Spec (.of k)))).hom) L.1, h⟩ := by
  set f := X ↘ Spec (.of k)
  let T₀ := 𝟙_ (Over (Spec (.of k)))
  let J := fppfTopology.over (Spec (.of k))
  let S := picardSubfunctorDegree f 0
  -- a class of degree zero on `X` pulls back to a class of fibrewise degree zero on `X_k`
  have hmem (L : picardZero k X) : Pic.map (pullback.fst f T₀.hom) L.1 ∈ S.obj (.op T₀) := by
    intro K _ _ t
    rw [picardFibreDegree_map_fst]
    have h := L.2
    rwa [MonoidHom.mem_ker, picDegreeHom_apply, Hom.picDegree_eq, ofAdd_eq_one] at h
  -- the comparison `β : Pic^0_{X/k} ⟶ Pic_{X/k}` is injective on sections
  let α : S.toFunctor ⟶ (picardFunctor f).obj := S.ι ≫ toPicardFunctor f
  let β : picardFunctorDegree f 0 ⟶ picardFunctor f :=
    ⟨sheafifyLift J α (picardFunctor f).property⟩
  have fac : toSheafify J S.toFunctor ≫ β.hom = α := toSheafify_sheafifyLift J α _
  have : Presheaf.IsLocallyInjective J α := inferInstance
  have : Presheaf.IsLocallyInjective J β.hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac J α fac
  have hβ : Function.Injective (β.hom.app (.op T₀)) :=
    (Sheaf.isLocallyInjective_iff_injective β).1 this _
  have hβS {T : Over (Spec (.of k))} (M : S.toFunctor.obj (.op T)) :
      β.hom.app _ ((toSheafify J S.toFunctor).app _ M) = (toPicardFunctor f).app _ M.1 :=
    ConcreteCategory.congr_hom (NatTrans.congr_app fac (.op T)) M
  -- the split exact sequence at `T₀ = Spec k`
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
  obtain ⟨pt⟩ := Hom.nonempty_fieldPoints (k := k) f
  have hσ : pt.1 ≫ f = 𝟙 _ := by
    rw [pt.2, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have hsplit := bijective_pic_split f pt.1 hσ
    isIso_pushforwardUnitMap_pullback_snd_of_geometricallyIntegral T₀
  have hone (a : (Spec (.of k)).Pic) : a = 1 := by
    obtain ⟨e⟩ := Modules.IsInvertible.nonempty_iso_unit (X := Spec (.of k)) default
      ((fromSkeleton _).obj a.val)
    exact Pic.eq_iff_nonempty_iso.2 ⟨e ≪≫ Pic.oneIso.symm⟩
  -- `X_k ⟶ X` is an isomorphism
  have : IsIso (pullback.fst f T₀.hom) := by
    change IsIso (pullback.fst f (𝟙 _))
    infer_instance
  have hinv (L : X.Pic) :
      Pic.map (inv (pullback.fst f T₀.hom)) (Pic.map (pullback.fst f T₀.hom) L) = L := by
    rw [← Pic.map_comp, IsIso.inv_hom_id, Pic.map_id]
  have hinv' (M : (pullback f T₀.hom).Pic) :
      Pic.map (pullback.fst f T₀.hom) (Pic.map (inv (pullback.fst f T₀.hom)) M) = M := by
    rw [← Pic.map_comp, IsIso.hom_inv_id, Pic.map_id]
  let φ (L : picardZero k X) : (picardFunctorDegree f 0).obj.obj (.op T₀) :=
    (toSheafify J S.toFunctor).app _ ⟨_, hmem L⟩
  refine ⟨Equiv.ofBijective φ ⟨fun L₁ L₂ h ↦ ?_, fun s ↦ ?_⟩, fun L ↦ ⟨hmem L, rfl⟩⟩
  · have h' := congrArg (β.hom.app _) h
    simp only [φ, hβS] at h'
    have hM := hsplit.1 (a₁ := Pic.map (pullback.fst f T₀.hom) L₁.1)
      (a₂ := Pic.map (pullback.fst f T₀.hom) L₂.1) (Prod.ext (by
        change Pic.map _ _ = Pic.map _ _
        exact (hone _).trans (hone _).symm) h')
    exact Subtype.ext (by rw [← hinv L₁.1, hM, hinv])
  · -- the degree of the image of `s` in `Pic_{X/k}(T₀)` vanishes everywhere
    have hdeg (t : T₀.left) : picardDegree f (β.hom.app _ s) t = 0 := by
      obtain ⟨Z, g, ⟨a, ha⟩, -, -, z, rfl⟩ := exists_flat_mem_of_mem_fppfTopology_over
        (Presheaf.imageSieve_mem J (toSheafify J S.toFunctor) s) t
      rw [← picardDegree_map, ← NatTrans.naturality_apply β.hom,
        show (picardFunctorDegree f 0).obj.map g.op s = (toSheafify J S.toFunctor).app _ a from
          ha.symm, hβS,
        picardDegree_toPicardFunctor]
      exact (mem_picardSubfunctorDegree_iff f 0 a.1).1 a.2 z
    obtain ⟨M, hM⟩ := hsplit.2 (1, β.hom.app _ s)
    have hM₂ : (toPicardFunctor f).app _ M = β.hom.app _ s := congrArg Prod.snd hM
    have hMS : M ∈ S.obj (.op T₀) := (mem_picardSubfunctorDegree_iff f 0 M).2 fun t ↦ by
      rw [← picardDegree_toPicardFunctor, hM₂]
      exact hdeg t
    let L₀ := Pic.map (inv (pullback.fst f T₀.hom)) M
    have hL₀ : L₀ ∈ picardZero k X := by
      have h := hMS k (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k k)))
        (Category.comp_id _))
      rw [← hinv' M, picardFibreDegree_map_fst] at h
      rw [MonoidHom.mem_ker, picDegreeHom_apply, Hom.picDegree_eq, h, ofAdd_zero]
    refine ⟨⟨L₀, hL₀⟩, hβ ?_⟩
    simp only [φ, hβS]
    rw [hinv' M]
    exact hM₂

/-- **The Jacobian is an abelian variety.** Let `X` be a smooth projective curve of genus `g`
over a separably closed field `k`.  Then there is a `k`-scheme `J` carrying a commutative group
scheme structure which is proper, smooth of relative dimension `g` and geometrically integral
over `k`, which represents the degree-zero part `Pic^0_{X/k}` of the Picard functor compatibly
with the group laws, and whose group of `k`-rational points is isomorphic to `Pic^0(X)`.

The tangent space clause `T_e J ≅ H^1(X, 𝒪_X)` is
`AlgebraicGeometry.nonempty_tangentSpaceAt_linearEquiv_H_one` and is not repeated here; the
base-change clause `J(X_{k'}) = J(X) ×_k k'` for `k ⊆ k'` algebraically closed is omitted, the
corresponding compatibility over a general base field being part of
`AlgebraicGeometry.exists_jacobian_descent`.

(blueprint: `sk-prop-jacobian`) -/
theorem exists_jacobian [IsSepClosed k]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    [GeometricallyIntegral (X ↘ Spec (.of k))] :
    ∃ (J : Over (Spec (.of k))) (_ : CommGrpObj J)
      (e : (picardFunctorDegree (X ↘ Spec (.of k)) 0).obj.RepresentableBy J),
      IsProper J.hom ∧ SmoothOfRelativeDimension (arithmeticGenus k X) J.hom ∧
        GeometricallyIntegral J.hom ∧ IsPicardZeroMul (X ↘ Spec (.of k)) e ∧
        Nonempty (picardZero k X ≃* (𝟙_ (Over (Spec (.of k))) ⟶ J)) := by
  obtain ⟨A, -, hA, -⟩ := isRepresentable_picardFunctor (X ↘ Spec (.of k))
  obtain ⟨Pd, -, -, -, -, -, hPd⟩ := exists_decomposition_picardFunctor A hA
  obtain ⟨h₀⟩ := hPd 0
  obtain ⟨_, he⟩ := exists_commGrpObj_isPicardZeroMul (X ↘ Spec (.of k)) h₀
  obtain ⟨Φ, hΦ⟩ := exists_picardZero_equiv_picardFunctorDegree_zero (k := k) (X := X)
  have hρ (a b : picardZero k X) :
      Pic.map (pullback.fst (X ↘ Spec (.of k)) (𝟙_ (Over (Spec (.of k)))).hom) (a * b).1 =
        Pic.map (pullback.fst (X ↘ Spec (.of k)) (𝟙_ (Over (Spec (.of k)))).hom) a.1 *
          Pic.map (pullback.fst (X ↘ Spec (.of k)) (𝟙_ (Over (Spec (.of k)))).hom) b.1 :=
    Pic.map_mul _ a.1 b.1
  obtain ⟨ψ, -⟩ := exists_mulEquiv_of_isPicardZeroMul (X ↘ Spec (.of k)) h₀ he
    (T := 𝟙_ (Over (Spec (.of k))))
    (fun L : picardZero k X ↦
      Pic.map (pullback.fst (X ↘ Spec (.of k)) (𝟙_ (Over (Spec (.of k)))).hom) L.1)
    hρ Φ hΦ
  exact ⟨Pd 0, inferInstance, h₀, isProper_of_representableBy_picardFunctorDegree 0 _ h₀,
    smoothOfRelativeDimension_of_representableBy_picardFunctorDegree 0 _ h₀,
    geometricallyIntegral_of_representableBy_picardFunctorDegree 0 _ h₀, he, ⟨ψ⟩⟩

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

attribute [local instance] Scheme.smoothOfRelativeDimension_baseChange Scheme.isProper_baseChange

/-- **The degree-zero Picard functor over a separable closure.** Let `C` be a smooth projective
geometrically integral curve of genus `g` over `k` and let `k_s` be a separable closure of `k`.
Then `Pic^0_{C_{k_s}/k_s}` is represented, compatibly with the group laws, by an abelian variety
`J_s` of dimension `g` over `k_s`, whose group of `k_s`-points is isomorphic to `Pic^0(C_{k_s})`.

(blueprint: `thm-pd-geometric-pic0`) -/
theorem exists_jacobian_pullback (ks : Type u) [Field ks] [Algebra k ks] [IsSepClosure k ks]
    (C : Scheme.{u}) [C.Over (Spec (.of k))] [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))]
    [IsProper (C ↘ Spec (.of k))] [GeometricallyIntegral (C ↘ Spec (.of k))] (g : ℕ)
    (hg : arithmeticGenus k C = g) :
    ∃ (J : Over (Spec (.of ks))) (_ : CommGrpObj J)
      (e : (picardFunctorDegree (pullback (C ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k ks))) ↘ Spec (.of ks)) 0).obj.RepresentableBy J),
      IsProper J.hom ∧ SmoothOfRelativeDimension g J.hom ∧ GeometricallyIntegral J.hom ∧
        IsPicardZeroMul _ e ∧
        Nonempty (picardZero ks
            (pullback (C ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k ks)))) ≃*
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
        (picardFunctorDegree (C' ↘ Spec (.of K)) d).obj) := by
  set f := C ↘ Spec (.of k)
  set f' := C' ↘ Spec (.of K)
  set g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : IsProper f' := IsProper.isStableUnderBaseChange.of_isPullback h ‹_›
  have : LocallyOfFinitePresentation f' :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) h inferInstance
  -- the identification of the Picard presheaves preserves the fibrewise degrees
  let eP := picardPresheafIsoOfIsPullback h
  have hmem (T : Over (Spec (.of K))) (L : (picardPresheaf f).obj (.op ((Over.map g).obj T))) :
      L ∈ (picardSubfunctorDegree f d).obj (.op ((Over.map g).obj T)) ↔
        eP.hom.app (.op T) L ∈ (picardSubfunctorDegree f' d).obj (.op T) := by
    rw [mem_picardSubfunctorDegree_iff, mem_picardSubfunctorDegree_iff]
    refine forall_congr' fun t ↦ ?_
    rw [picardPresheafIsoOfIsPullback_hom_app,
      picardPresheafDegree_pic_map_of_isPullback f f' (𝟙 T.left) _
        (IsPullback.of_horiz_isIso ⟨by simp⟩) L t]
    rfl
  let eS : (Over.map g).op ⋙ (picardSubfunctorDegree f d).toFunctor ≅
      (picardSubfunctorDegree f' d).toFunctor :=
    NatIso.ofComponents
      (fun T ↦ Equiv.toIso ((eP.app T).toEquiv.subtypeEquiv fun L ↦ hmem T.unop L))
      fun {T T'} φ ↦ by
        ext L
        apply Subtype.ext
        exact NatTrans.naturality_apply eP.hom φ L.1
  exact ⟨overMapOpCompSheafifyIso g _ ≪≫
    (sheafToPresheaf _ _).mapIso ((presheafToSheaf _ _).mapIso eS)⟩

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

/-- **The geometric points of `Pic^0_{C₀/k₀}`.** Let `C₀` be a smooth projective geometrically
integral curve over `k₀`, let `K` be an algebraically closed extension of `k₀` and let `C` be the
base change of `C₀` to `K`. Then the value of `Pic^0_{C₀/k₀}` on `Spec K` is `Pic^0(C)`, and the
identification is equivariant: for a `k₀`-automorphism `σ` of `K`, the automorphism `γ` of `C`
over `C₀` lying over `Spec σ` acts on `Pic^0(C)` by pullback, and this corresponds to the action of
`Spec σ` on `Pic^0_{C₀/k₀}(Spec K)`.

The bijection sends `ℒ ∈ Pic^0(C)` to the image of the corresponding class on
`C₀ ×_{k₀} K ≅ C`. Since `C` has a `K`-point, `Pic(C) ⟶ Pic_{C/K}(K)` is bijective
(`AlgebraicGeometry.bijective_pic_split` with `Pic(Spec K) = 0`), every fppf covering of `Spec K`
having a section; the fibrewise degree of a class over the point `Spec K` is its degree on `C`.
Both maps are natural in `Spec K`, which gives the equivariance. These are Steps 9 and 10 of the
proof of `AlgebraicGeometry.exists_jacobian_descent`.

The instances `[SmoothOfRelativeDimension 1 (C ↘ Spec K)]` and `[IsProper (C ↘ Spec K)]`, which
follow from `hC`, are assumed so that `Pic^0(C)` is defined. -/
theorem exists_picardZero_equiv_picardFunctorDegree {k₀ K : Type u} [Field k₀] [Field K]
    [Algebra k₀ K] [IsAlgClosed K] (C₀ : Scheme.{u}) [C₀.Over (Spec (.of k₀))]
    [SmoothOfRelativeDimension 1 (C₀ ↘ Spec (.of k₀))] [IsProper (C₀ ↘ Spec (.of k₀))]
    [GeometricallyIntegral (C₀ ↘ Spec (.of k₀))] (C : Scheme.{u}) [C.Over (Spec (.of K))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (.of K))] [IsProper (C ↘ Spec (.of K))]
    (p : C ⟶ C₀)
    (hC : IsPullback p (C ↘ Spec (.of K)) (C₀ ↘ Spec (.of k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) :
    ∃ Φ : picardZero K C ≃ (picardFunctorDegree (C₀ ↘ Spec (.of k₀)) 0).obj.obj
        (.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))),
      (∀ L, ∃ h, Φ L = (toSheafify (fppfTopology.over (Spec (.of k₀)))
        (picardSubfunctorDegree (C₀ ↘ Spec (.of k₀)) 0).toFunctor).app _
          ⟨Pic.map hC.isoPullback.inv L.1, h⟩) ∧
      ∀ σ : K ≃ₐ[k₀] K, ∃ γ : C ⟶ C, γ ≫ p = p ∧
        γ ≫ (C ↘ Spec (.of K)) = (C ↘ Spec (.of K)) ≫
          Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ∧
        ∃ act : picardZero K C → picardZero K C,
          (∀ L, (act L).1 = Pic.map γ L.1) ∧
            ∀ L, Φ (act L) =
              (picardFunctorDegree (C₀ ↘ Spec (.of k₀)) 0).obj.map (specAlgEquivOver σ).op
                (Φ L) := by
  set f := C₀ ↘ Spec (.of k₀)
  let T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))
  let J := fppfTopology.over (Spec (.of k₀))
  let S := picardSubfunctorDegree f 0
  let e := hC.isoPullback
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have he₁ : e.hom ≫ pullback.fst f T.hom = p := hC.isoPullback_hom_fst
  have he₂ : e.hom ≫ pullback.snd f T.hom = C ↘ Spec (.of K) := hC.isoPullback_hom_snd
  have hsqE : IsPullback e.hom (C ↘ Spec (.of K)) (pullback.snd f T.hom) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [he₂, Category.comp_id]⟩
  have hsqE' : IsPullback e.inv (pullback.snd f T.hom) (C ↘ Spec (.of K)) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [← he₂, Iso.inv_hom_id_assoc, Category.comp_id]⟩
  have hker (L : C.Pic) :
      L ∈ picardZero K C ↔ Modules.degree K ((fromSkeleton C.Modules).obj L.val) = 0 := by
    rw [MonoidHom.mem_ker, picDegreeHom_apply, Hom.picDegree_eq, ofAdd_eq_one]
  -- the fibrewise degree of a class transported from `C` is its degree
  have hdegρ (L : C.Pic) {K' : Type u} [Field K'] [Algebra k₀ K']
      (t : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k₀ K'))) ⟶ T) :
      picardFibreDegree f (Pic.map e.inv L) t =
        Modules.degree K ((fromSkeleton C.Modules).obj L.val) := by
    let : (pullback f (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k₀ K')))).hom).Over
        (Spec (.of K')) := ⟨pullback.snd _ _⟩
    change Modules.degree K' ((fromSkeleton _).obj
      (Pic.map (baseChangeMap f t) (Pic.map e.inv L)).val) = _
    rw [← Pic.map_comp]
    have sq := (isPullback_baseChangeMap f t).paste_horiz hsqE'
    rw [Category.comp_id] at sq
    exact (Modules.degree_congr K' (fromSkeletonToSkeletonIso _)).trans
      (Modules.degree_pullback_of_isPullback t.left _ sq ((fromSkeleton C.Modules).obj L.val))
  have hmem (L : picardZero K C) : Pic.map e.inv L.1 ∈ S.obj (.op T) := fun K' _ _ t ↦ by
    rw [hdegρ]
    exact (hker L.1).1 L.2
  -- the comparison `β : Pic^0_{C₀/k₀} ⟶ Pic_{C₀/k₀}` is injective on sections
  let α : S.toFunctor ⟶ (picardFunctor f).obj := S.ι ≫ toPicardFunctor f
  let β : picardFunctorDegree f 0 ⟶ picardFunctor f :=
    ⟨sheafifyLift J α (picardFunctor f).property⟩
  have fac : toSheafify J S.toFunctor ≫ β.hom = α := toSheafify_sheafifyLift J α _
  have : Presheaf.IsLocallyInjective J α := inferInstance
  have : Presheaf.IsLocallyInjective J β.hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac J α fac
  have hβ : Function.Injective (β.hom.app (.op T)) :=
    (Sheaf.isLocallyInjective_iff_injective β).1 this _
  have hβS {T' : Over (Spec (.of k₀))} (M : S.toFunctor.obj (.op T')) :
      β.hom.app _ ((toSheafify J S.toFunctor).app _ M) = (toPicardFunctor f).app _ M.1 :=
    ConcreteCategory.congr_hom (NatTrans.congr_app fac (.op T')) M
  have hf := isIso_pushforwardUnitMap_pullback_snd_of_geometricallyIntegral (k := k₀) (X := C₀)
  have hinv (L : C.Pic) : Pic.map e.hom (Pic.map e.inv L) = L := by
    rw [← Pic.map_comp, Iso.hom_inv_id, Pic.map_id]
  have hinv' (M : (pullback f T.hom).Pic) : Pic.map e.inv (Pic.map e.hom M) = M := by
    rw [← Pic.map_comp, Iso.inv_hom_id, Pic.map_id]
  let φ (L : picardZero K C) : (picardFunctorDegree f 0).obj.obj (.op T) :=
    (toSheafify J S.toFunctor).app _ ⟨_, hmem L⟩
  have hφinj : Function.Injective φ := fun L₁ L₂ h ↦ by
    have h' := congrArg (β.hom.app _) h
    simp only [φ, hβS] at h'
    obtain ⟨N, ⟨i⟩⟩ := exists_iso_tensorObj_of_toPicardFunctor_app_eq f hf _ _ h'
    obtain ⟨eN⟩ := Modules.IsInvertible.nonempty_iso_unit (X := Spec (.of K)) default
      ((fromSkeleton _).obj N.val)
    have hρ : Pic.map e.inv L₁.1 = Pic.map e.inv L₂.1 :=
      Pic.eq_iff_nonempty_iso.2 ⟨i ≪≫ (Iso.refl _ ⊗ᵢ ((Modules.pullback _).mapIso eN ≪≫
        Modules.pullbackObjUnitIso _)) ≪≫ ρ_ _⟩
    exact Subtype.ext (by rw [← hinv L₁.1, hρ, hinv])
  have hφsurj : Function.Surjective φ := fun s ↦ by
    -- the degree of the image of `s` in `Pic_{C₀/k₀}(T)` vanishes everywhere
    have hdeg (t : T.left) : picardDegree f (β.hom.app _ s) t = 0 := by
      obtain ⟨Z, g, ⟨a, ha⟩, -, -, z, rfl⟩ := exists_flat_mem_of_mem_fppfTopology_over
        (Presheaf.imageSieve_mem J (toSheafify J S.toFunctor) s) t
      refine (picardDegree_map f g (β.hom.app _ s) z).symm.trans ?_
      rw [← NatTrans.naturality_apply β.hom,
        show (picardFunctorDegree f 0).obj.map g.op s = (toSheafify J S.toFunctor).app _ a from
          ha.symm, hβS, picardDegree_toPicardFunctor]
      exact (mem_picardSubfunctorDegree_iff f 0 a.1).1 a.2 z
    -- the image of `s` comes from a class on an fppf covering of `Spec K`, which has a `K`-point
    obtain ⟨t₀⟩ : Nonempty T.left := inferInstanceAs (Nonempty (Spec (.of K)))
    obtain ⟨Z, g, ⟨MZ, hMZ⟩, -, hg, z, -⟩ := exists_flat_mem_of_mem_fppfTopology_over
      (Presheaf.imageSieve_mem J (toPicardFunctor f) (β.hom.app _ s)) t₀
    have : JacobsonSpace Z.left := LocallyOfFiniteType.jacobsonSpace g.left
    obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (Z := Set.univ) ⟨z, trivial⟩
      isClosed_univ.isLocallyClosed
    let τ : T ⟶ Z := Over.homMk (pointOfClosedPoint g.left x hx) (by
      rw [← Over.w g, pointOfClosedPoint_comp_assoc]
      rfl)
    have hτ : τ ≫ g = 𝟙 T := by
      ext1
      exact pointOfClosedPoint_comp g.left x hx
    let M := Pic.map (baseChangeMap f τ) MZ
    have hM₂ : (toPicardFunctor f).app _ M = β.hom.app _ s := by
      have h₁ := NatTrans.naturality_apply (toPicardFunctor f) τ.op MZ
      refine h₁.trans ?_
      rw [hMZ, ← Functor.map_comp_apply, ← op_comp, hτ, op_id]
      exact Functor.map_id_apply (picardFunctor f).obj _ _
    have hMS : M ∈ S.obj (.op T) := (mem_picardSubfunctorDegree_iff f 0 M).2 fun t ↦ by
      rw [← picardDegree_toPicardFunctor, hM₂]
      exact hdeg t
    have hL₀ : Pic.map e.hom M ∈ picardZero K C := by
      rw [hker, ← hdegρ _ (𝟙 T), hinv']
      exact hMS K (𝟙 T)
    refine ⟨⟨_, hL₀⟩, hβ ?_⟩
    simp only [φ, hβS]
    rw [hinv' M]
    exact hM₂
  refine ⟨Equiv.ofBijective φ ⟨hφinj, hφsurj⟩, fun L ↦ ⟨hmem L, rfl⟩, fun σ ↦ ?_⟩
  -- the Galois action
  let ψ := specAlgEquivOver σ
  let b := baseChangeMap f ψ
  have hb₁ : b ≫ pullback.fst f T.hom = pullback.fst f T.hom :=
    pullback.lift_fst _ _ _ |>.trans (Category.comp_id _)
  have hb₂ : b ≫ pullback.snd f T.hom =
      pullback.snd f T.hom ≫ Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) :=
    pullback.lift_snd _ _ _
  let γ := e.hom ≫ b ≫ e.inv
  have hγ : IsPullback γ (C ↘ Spec (.of K)) (C ↘ Spec (.of K))
      (Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom)) := by
    have := (hsqE.paste_horiz (isPullback_baseChangeMap f ψ)).paste_horiz hsqE'
    simp only [Category.id_comp, Category.assoc] at this
    exact this
  have hact (L : picardZero K C) : Pic.map γ L.1 ∈ picardZero K C := by
    rw [hker]
    exact (Modules.degree_congr K (fromSkeletonToSkeletonIso _)).trans
      ((Modules.degree_pullback_of_isPullback _ _ hγ
        ((fromSkeleton C.Modules).obj L.1.val)).trans ((hker L.1).1 L.2))
  refine ⟨γ, ?_, ?_, fun L ↦ ⟨_, hact L⟩, fun L ↦ rfl, fun L ↦ ?_⟩
  · rw [← he₁]
    simp only [γ, Category.assoc, Iso.inv_hom_id_assoc, hb₁]
  · rw [← he₂]
    simp only [γ, Category.assoc, Iso.inv_hom_id_assoc, hb₂]
  · change (toSheafify J S.toFunctor).app _ ⟨_, hmem _⟩ =
      (picardFunctorDegree f 0).obj.map ψ.op ((toSheafify J S.toFunctor).app _ ⟨_, hmem L⟩)
    have hnat := NatTrans.naturality_apply (toSheafify J S.toFunctor) ψ.op
      (⟨_, hmem L⟩ : S.toFunctor.obj (.op T))
    refine (congrArg _ (Subtype.ext ?_)).trans hnat
    change Pic.map e.inv (Pic.map γ L.1) = Pic.map b (Pic.map e.inv L.1)
    rw [← Pic.map_comp, ← Pic.map_comp]
    simp only [γ, Iso.inv_hom_id_assoc]


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
represented, compatibly with the group laws, by an abelian variety of dimension `g` over `k`. No
rational point of `C` is assumed.

This is Steps 1–7 of the proof of `AlgebraicGeometry.exists_jacobian_descent`: the Jacobian of
`C_{k_s}` carries the canonical descent datum, which is defined at a finite separable level `K`,
is effective there, and descends the geometric properties to `k`. The group law of the descended
scheme is the one induced by the group law of `Pic^0_{C/k}`
(`AlgebraicGeometry.exists_commGrpObj_isPicardZeroMul`), so it need not be descended separately.

(blueprint: `thm-pd-jacobian-general-field`) -/
theorem exists_commGrpObj_representableBy_picardFunctorDegree (ks : Type u) [Field ks]
    [Algebra k ks] [IsSepClosure k ks] (C : Scheme.{u}) [C.Over (Spec (.of k))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))] [IsProper (C ↘ Spec (.of k))]
    [GeometricallyIntegral (C ↘ Spec (.of k))] (g : ℕ) (hg : arithmeticGenus k C = g) :
    ∃ (J : Over (Spec (.of k))) (_ : CommGrpObj J)
      (e : (picardFunctorDegree (C ↘ Spec (.of k)) 0).obj.RepresentableBy J),
      IsProper J.hom ∧ SmoothOfRelativeDimension g J.hom ∧ GeometricallyIntegral J.hom ∧
        IsPicardZeroMul _ e := by
  -- Step 1: the Jacobian `J_s` of `C_{k_s}` represents the restriction of `Pic^0_{C/k}`.
  obtain ⟨Js, _, rJs, hJsP, hJsS, hJsG, -, -⟩ := exists_jacobian_pullback ks C g hg
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
  -- Step 5: the group law of `Pic^0_{C/k}` makes `J` a commutative group scheme.
  obtain ⟨_, hr⟩ := exists_commGrpObj_isPicardZeroMul (C ↘ Spec (.of k)) r
  exact ⟨J, inferInstance, r, hP, hS, hG, hr⟩

/-- **The Jacobian over a general base field, by Galois descent.** Let `k₀` be any field, `k_s` a
separable closure of `k₀`, `k̄₀` an algebraic closure of `k₀` containing `k_s`, and let `C₀` be a
proper smooth geometrically connected curve of genus `g` over `k₀`.  Let `C` be the base change
`C₀ ×_{k₀} k̄₀`, presented by a cartesian square.  Then the Jacobian of `C` descends to `k₀`:
there is a `k₀`-scheme `J₀` carrying a commutative group scheme structure, proper, smooth of
relative dimension `g` and geometrically integral over `k₀`, which represents `Pic^0_{C₀/k₀}`
compatibly with the group laws, whose base change `J₀ ×_{k₀} k̄₀` represents `Pic^0_{C/k̄₀}`, and
whose group of `k̄₀`-points is isomorphic to `Pic^0(C)`.  The isomorphism is equivariant: every
`k₀`-algebra automorphism `σ` of `k̄₀` induces the automorphism `γ` of `C` over `C₀` lying over
`Spec σ`, base change along `γ` preserves `Pic^0(C)`, and the isomorphism intertwines that
action with the action on `k̄₀`-points by precomposition with
`AlgebraicGeometry.specAlgEquivOver σ`. Restricted to `ℓⁿ`-torsion, it gives the `Gal(k̄₀/k₀)`-
equivariant isomorphism `J₀[ℓⁿ](k̄₀) ≅ Pic^0(C)[ℓⁿ]` of the blueprint.

No rational point of `C₀` is assumed. The instances `[SmoothOfRelativeDimension 1 (C ↘ Spec K)]`
and `[IsProper (C ↘ Spec K)]`, which follow from `hC`, are assumed so that `Pic^0(C)` is defined.

(blueprint: `sk-prop-jacobian-descent`) -/
theorem exists_jacobian_descent (k₀ ks K : Type u) [Field k₀] [Field ks] [Field K]
    [Algebra k₀ ks] [Algebra k₀ K] [Algebra ks K] [IsScalarTower k₀ ks K]
    [IsSepClosure k₀ ks] [IsAlgClosure k₀ K] (C₀ : Scheme.{u}) [C₀.Over (Spec (.of k₀))]
    [SmoothOfRelativeDimension 1 (C₀ ↘ Spec (.of k₀))] [IsProper (C₀ ↘ Spec (.of k₀))]
    [GeometricallyConnected (C₀ ↘ Spec (.of k₀))] (g : ℕ) (hg : arithmeticGenus k₀ C₀ = g)
    (C : Scheme.{u}) [C.Over (Spec (.of K))] [SmoothOfRelativeDimension 1 (C ↘ Spec (.of K))]
    [IsProper (C ↘ Spec (.of K))] (p : C ⟶ C₀)
    (hC : IsPullback p (C ↘ Spec (.of K)) (C₀ ↘ Spec (.of k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) :
    ∃ (J₀ : Over (Spec (.of k₀))) (_ : CommGrpObj J₀)
      (r : (picardFunctorDegree (C₀ ↘ Spec (.of k₀)) 0).obj.RepresentableBy J₀),
      IsProper J₀.hom ∧ SmoothOfRelativeDimension g J₀.hom ∧ GeometricallyIntegral J₀.hom ∧
        IsPicardZeroMul _ r ∧
        Nonempty ((picardFunctorDegree (C ↘ Spec (.of K)) 0).obj.RepresentableBy
          (Over.mk (Limits.pullback.snd J₀.hom
            (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))))) ∧
        ∃ e : picardZero K C ≃*
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
  obtain ⟨J₀, _, r, hP, hS, hG, hr⟩ :=
    exists_commGrpObj_representableBy_picardFunctorDegree ks C₀ g hg
  -- Step 8: its base change to `K` represents `Pic^0_{C/K}`.
  obtain ⟨e⟩ := nonempty_picardFunctorDegree_iso_of_isPullback p hC 0
  -- Steps 9–11: the geometric points, equivariantly and as groups.
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed k₀
  obtain ⟨Φ, hΦ, hΦσ⟩ := exists_picardZero_equiv_picardFunctorDegree C₀ C p hC
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_of_isPicardZeroMul _ r hr
    (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (fun L : picardZero K C ↦ Pic.map hC.isoPullback.inv L.1)
    (fun a b ↦ Pic.map_mul _ a.1 b.1) Φ hΦ
  refine ⟨J₀, inferInstance, r, hP, hS, hG, hr,
    ⟨(r.ofAdjunction (Over.mapPullbackAdj _)).ofIso e⟩, ψ, fun σ ↦ ?_⟩
  obtain ⟨γ, hγp, hγ, act, hact, hΦσ⟩ := hΦσ σ
  refine ⟨γ, hγp, hγ, act, hact, fun L ↦ r.homEquiv.injective ?_⟩
  simp only [hψ, Equiv.apply_symm_apply, r.homEquiv_comp, hΦσ]

end Descent

end AlgebraicGeometry
