/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian

/-!
# The degree decomposition of the Picard scheme: group structures and translations

Let `X` be a smooth projective geometrically integral curve over a field `k`. This file completes
the degree decomposition `Pic_{X/k} = ∐_d Pic^d_{X/k}` of
`AlgebraicGeometry.exists_decomposition_picardFunctor` by its group-theoretic parts.

* The fibrewise degree is a group homomorphism `Pic (X_T) →* (T → ℤ)`, natural in `T`
  (`AlgebraicGeometry.picardPresheafDegreeHom`), whose kernel is the degree-zero subgroup
  (`AlgebraicGeometry.ker_picardPresheafDegreeHom`); hence `Pic^d · Pic^e ⊆ Pic^{d+e}`
  (`AlgebraicGeometry.mul_mem_picardSubfunctorDegree`). On the sheafification `Pic_{X/k}` with its
  inherited group law, the degree is again additive (`AlgebraicGeometry.picardDegree_mul`).
* The open and closed subscheme `P^0` of a scheme `P` representing `Pic_{X/k}` is a subgroup
  scheme: the inclusion `P^0 ⟶ P` is a morphism of group objects
  (`AlgebraicGeometry.exists_decomposition_picardFunctor_isMonHom`).
* Tensoring with a class `M ∈ Pic X` of degree `e` induces an isomorphism between schemes
  representing `Pic^d_{X/k}` and `Pic^{d+e}_{X/k}` whose functor of points is
  `ℒ ↦ ℒ ⊗ pr_X^* M` (`AlgebraicGeometry.exists_iso_representableBy_picardFunctorDegree`); with
  `M = 𝒪_X(d x)` for a rational point `x` this identifies `P^0` with `P^d`
  (`AlgebraicGeometry.exists_iso_representableBy_picardFunctorDegree_zero`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj CartesianMonoidalCategory

namespace AlgebraicGeometry

open Scheme

section DegreeHom

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [SmoothOfRelativeDimension 1 f] [IsProper f]

omit [SmoothOfRelativeDimension 1 f] in
/-- The fibrewise degree of a class at a point `t` is its degree on the fibre over the residue
field `κ(t)`. -/
lemma exists_picardFibreDegree_eq_picardPresheafDegree {T : Over (Spec (.of k))} (t : T.left) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K)
      (τ : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ T),
      ∀ L : (picardPresheaf f).obj (.op T),
        picardFibreDegree f L τ = picardPresheafDegree f L t := by
  let φ := T.left.fromSpecResidueField t ≫ T.hom
  let : Algebra k (T.left.residueField t) := (Spec.preimage φ).hom.toAlgebra
  let τ : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (T.left.residueField t)))) ⟶ T :=
    Over.homMk (T.left.fromSpecResidueField t) (Spec.map_preimage φ).symm
  obtain ⟨s⟩ : Nonempty (Spec (T.left.residueField t)) := inferInstance
  refine ⟨_, inferInstance, inferInstance, τ, fun L ↦ ?_⟩
  rw [picardFibreDegree_eq_picardPresheafDegree f L τ s,
    show τ.left s = t from Scheme.fromSpecResidueField_apply _ _]

/-- **The fibrewise degree is additive**: `deg (ℒ ⊗ ℳ)_t = deg ℒ_t + deg ℳ_t`. -/
lemma picardPresheafDegree_mul {T : Over (Spec (.of k))} (L M : (pullback f T.hom).Pic)
    (t : T.left) :
    picardPresheafDegree f (L * M : (pullback f T.hom).Pic) t =
      picardPresheafDegree f L t + picardPresheafDegree f M t := by
  obtain ⟨K, _, _, τ, h⟩ := exists_picardFibreDegree_eq_picardPresheafDegree f t
  rw [← h, ← h, ← h]
  exact picardFibreDegree_mul f τ L M

omit [SmoothOfRelativeDimension 1 f] in
/-- The fibrewise degree of the unit class is zero. -/
lemma picardPresheafDegree_one {T : Over (Spec (.of k))} (t : T.left) :
    picardPresheafDegree f (1 : (pullback f T.hom).Pic) t = 0 := by
  obtain ⟨K, _, _, τ, h⟩ := exists_picardFibreDegree_eq_picardPresheafDegree f t
  rw [← h]
  exact picardFibreDegree_one f τ

/-- **The degree as a homomorphism.** For a smooth proper curve `f : X ⟶ Spec k` and a
`k`-scheme `T`, the fibrewise degree `ℒ ↦ (t ↦ deg ℒ_t)` is a group homomorphism from `Pic (X_T)`
to the group of functions `T → ℤ` (written multiplicatively); it is natural in `T`
(`AlgebraicGeometry.picardPresheafDegreeHom_map`) and its values are locally constant
(`AlgebraicGeometry.isLocallyConstant_picardPresheafDegree`).

(blueprint: `prop-pd-picard-degree-decomposition`, part (1)) -/
noncomputable def picardPresheafDegreeHom (T : Over (Spec (.of k))) :
    (pullback f T.hom).Pic →* (T.left → Multiplicative ℤ) where
  toFun L t := .ofAdd (picardPresheafDegree f L t)
  map_one' := funext fun t ↦ by
    change Multiplicative.ofAdd (picardPresheafDegree f (1 : (pullback f T.hom).Pic) t) = 1
    rw [picardPresheafDegree_one, ofAdd_zero]
  map_mul' L M := funext fun t ↦ by
    change Multiplicative.ofAdd (picardPresheafDegree f (L * M : (pullback f T.hom).Pic) t) = _
    rw [picardPresheafDegree_mul, ofAdd_add]
    rfl

lemma picardPresheafDegreeHom_apply (T : Over (Spec (.of k))) (L : (pullback f T.hom).Pic)
    (t : T.left) :
    picardPresheafDegreeHom f T L t = .ofAdd (picardPresheafDegree f L t) :=
  rfl

/-- **The degree homomorphism is natural**: the degree of the pullback of `ℒ` along `φ : T' ⟶ T`
is the degree of `ℒ` composed with `φ`.

(blueprint: `prop-pd-picard-degree-decomposition`, part (1)) -/
lemma picardPresheafDegreeHom_map {T T' : Over (Spec (.of k))} (φ : T' ⟶ T)
    (L : (pullback f T.hom).Pic) (t : T'.left) :
    picardPresheafDegreeHom f T' (Pic.map (baseChangeMap f φ) L) t =
      picardPresheafDegreeHom f T L (φ.left t) :=
  congrArg Multiplicative.ofAdd (picardPresheafDegree_map f φ L t)

/-- **`Pic^0` is the kernel of the degree.** The classes of fibrewise degree zero are the kernel
of the degree homomorphism `AlgebraicGeometry.picardPresheafDegreeHom`.

(blueprint: `prop-pd-picard-degree-decomposition`, part (1)) -/
theorem ker_picardPresheafDegreeHom (T : Over (Spec (.of k))) :
    (picardPresheafDegreeHom f T).ker = picardSubgroupDegreeZero f T := by
  ext L
  change _ ↔ L ∈ (picardSubfunctorDegree f 0).obj (.op T)
  rw [MonoidHom.mem_ker, mem_picardSubfunctorDegree_iff, funext_iff]
  exact forall_congr' fun t ↦ ofAdd_eq_one

/-- **`Pic^d · Pic^e ⊆ Pic^{d+e}`**: the product of a class of fibrewise degree `d` and a class
of fibrewise degree `e` has fibrewise degree `d + e`.

(blueprint: `prop-pd-picard-degree-decomposition`, part (1)) -/
theorem mul_mem_picardSubfunctorDegree {T : Over (Spec (.of k))} {d e : ℤ}
    {L M : (pullback f T.hom).Pic} (hL : L ∈ (picardSubfunctorDegree f d).obj (.op T))
    (hM : M ∈ (picardSubfunctorDegree f e).obj (.op T)) :
    L * M ∈ (picardSubfunctorDegree f (d + e)).obj (.op T) := fun K _ _ t ↦ by
  rw [picardFibreDegree_mul f t L M, hL K t, hM K t]

/-- The inverse of a class of fibrewise degree `d` has fibrewise degree `-d`. -/
theorem inv_mem_picardSubfunctorDegree {T : Over (Spec (.of k))} {d : ℤ}
    {L : (pullback f T.hom).Pic} (hL : L ∈ (picardSubfunctorDegree f d).obj (.op T)) :
    L⁻¹ ∈ (picardSubfunctorDegree f (-d)).obj (.op T) := fun K _ _ t ↦ by
  have h := picardFibreDegree_mul f t L⁻¹ L
  rw [inv_mul_cancel, picardFibreDegree_one, hL K t] at h
  omega

attribute [local instance] sheafifyGroup in
/-- **The degree on `Pic_{X/k}` is a homomorphism of sheaves of groups.** For sections `x`, `y`
of the relative Picard functor over `T`, with the group law that the sheafification inherits
from the Picard presheaf (`CategoryTheory.sheafifyGroup`), the degree of `x * y` is the sum of
the degrees of `x` and `y`.

(blueprint: `prop-pd-picard-degree-decomposition`, part (1)) -/
theorem picardDegree_mul {T : Over (Spec (.of k))}
    (x y : (sheafify (fppfTopology.over (Spec (.of k)))
      (picardPresheafGrp f ⋙ forget GrpCat)).obj (.op T)) :
    picardDegree f (x * y) = picardDegree f x + picardDegree f y := by
  let J := fppfTopology.over (Spec (.of k))
  funext t
  obtain ⟨Z, g, ⟨⟨L, hL⟩, ⟨M, hM⟩⟩, -, -, z, rfl⟩ := exists_flat_mem_of_mem_fppfTopology_over
    (J.intersection_covering (SheafifyGrp.imageSieve_mem (J := J) x)
      (SheafifyGrp.imageSieve_mem (J := J) y)) t
  rw [Pi.add_apply, picardDegree_eq f x g L hL, picardDegree_eq f y g M hM,
    picardDegree_eq f (x * y) g (L * M : (pullback f Z.hom).Pic)
      (map_sheafify_mul J (picardPresheafGrp f) x y g L M hL hM).symm, picardPresheafDegree_mul]

end DegreeHom

section SubgroupScheme

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The inclusion of `Pic^0` is a group homomorphism.** Let `P` represent `Pic_{X/k}` and `P₀`
represent `Pic^0_{X/k}`, both respecting the group laws, and let `j : P₀ ⟶ P` send the point of
`P₀` classifying a class of fibrewise degree zero to the point of `P` classifying the same
class. Then `j` is a morphism of group objects.

(blueprint: `prop-pd-picard-degree-decomposition`, part (3)) -/
theorem isMonHom_of_isPicardMul {P P₀ : Over (Spec (.of k))} [GrpObj P] [GrpObj P₀]
    (hP : (picardFunctor f).obj.RepresentableBy P) (hPm : IsPicardMul f hP)
    (e : (picardFunctorDegree f 0).obj.RepresentableBy P₀) (he : IsPicardZeroMul f e)
    (hsub : ∀ {T : Over (Spec (.of k))} (L M : (pullback f T.hom).Pic),
      L ∈ (picardSubfunctorDegree f 0).obj (.op T) →
        M ∈ (picardSubfunctorDegree f 0).obj (.op T) →
          L * M ∈ (picardSubfunctorDegree f 0).obj (.op T))
    (j : P₀ ⟶ P)
    (hj : ∀ {T : Over (Spec (.of k))} (L : (picardPresheaf f).obj (.op T))
      (hL : L ∈ (picardSubfunctorDegree f 0).obj (.op T)),
      e.homEquiv.symm ((toSheafify (fppfTopology.over (Spec (.of k)))
          (picardSubfunctorDegree f 0).toFunctor).app (.op T) ⟨L, hL⟩) ≫ j =
        hP.homEquiv.symm ((toPicardFunctor f).app (.op T) L)) :
    IsMonHom j := by
  let J := fppfTopology.over (Spec (.of k))
  let S := (picardSubfunctorDegree f 0).toFunctor
  have hmul {Y : Over (Spec (.of k))} (a b : Y ⟶ P₀) : (a * b) ≫ j = (a ≫ j) * (b ≫ j) := by
    apply hP.homEquiv.injective
    refine SheafifyGrp.ext (J := J) (P := picardPresheaf f) _
      (J.intersection_covering (SheafifyGrp.imageSieve_mem (J := J) (P := S) (e.homEquiv a))
        (SheafifyGrp.imageSieve_mem (J := J) (P := S) (e.homEquiv b)))
      fun Z g ⟨⟨⟨L, hL₀⟩, hL⟩, ⟨⟨M, hM₀⟩, hM⟩⟩ ↦ ?_
    have ha : g ≫ a = e.homEquiv.symm ((toSheafify J S).app (.op Z) ⟨L, hL₀⟩) := by
      rw [hL]; exact e.homEquiv.eq_symm_apply.2 (e.homEquiv_comp g a)
    have hb : g ≫ b = e.homEquiv.symm ((toSheafify J S).app (.op Z) ⟨M, hM₀⟩) := by
      rw [hM]; exact e.homEquiv.eq_symm_apply.2 (e.homEquiv_comp g b)
    have hLM := he (T := Z) L M hL₀ hM₀ (hsub L M hL₀ hM₀)
    refine (hP.homEquiv_comp g _).symm.trans (Eq.trans ?_ (hP.homEquiv_comp g _))
    congr 1
    rw [← Category.assoc, MonObj.comp_mul, ha, hb, ← hLM, hj, hPm, MonObj.comp_mul,
      ← Category.assoc, ← Category.assoc, ha, hb, hj, hj]
  refine ⟨?_, ?_⟩
  · rw [MonObj.one_eq_one, MonObj.one_eq_one]
    have h := hmul (1 : 𝟙_ _ ⟶ P₀) 1
    rw [_root_.mul_one] at h
    exact mul_eq_left.mp h.symm
  · rw [MonObj.mul_eq_mul, MonObj.mul_eq_mul, hmul, MonObj.comp_mul, tensorHom_fst,
      tensorHom_snd]

variable [IsSepClosed k] [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [GeometricallyIntegral (X ↘ Spec (.of k))]

/-- **`Pic^0` is an open and closed subgroup scheme of the Picard scheme.** Let `X` be a smooth
projective curve over a separably closed field `k` and let `P` represent `Pic_{X/k}`. Then `P`
is a commutative group scheme whose group law is the tensor product of invertible modules, and
its decomposition into the open and closed subschemes `P^d` representing `Pic^d_{X/k}`
(`AlgebraicGeometry.exists_decomposition_picardFunctor_representableBy`) can be chosen such
that `P^0` is a commutative group scheme representing `Pic^0_{X/k}` compatibly with the group
laws, and the open immersion `P^0 ⟶ P` is a morphism of group objects.

(blueprint: `prop-pd-picard-degree-decomposition`, part (3)) -/
theorem exists_decomposition_picardFunctor_isMonHom (P : Over (Spec (.of k)))
    (hP : (picardFunctor (X ↘ Spec (.of k))).obj.RepresentableBy P) :
    ∃ (_ : CommGrpObj P) (Pd : ℤ → Over (Spec (.of k))) (j : ∀ d, Pd d ⟶ P)
      (e : ∀ d, (picardFunctorDegree (X ↘ Spec (.of k)) d).obj.RepresentableBy (Pd d))
      (_ : CommGrpObj (Pd 0)),
      IsPicardMul (X ↘ Spec (.of k)) hP ∧ IsPicardZeroMul (X ↘ Spec (.of k)) (e 0) ∧
      IsMonHom (j 0) ∧
      (∀ d, IsOpenImmersion (j d).left) ∧
      (∀ d, IsClopen (Set.range (j d).left.base)) ∧
      (∀ d d', d ≠ d' → Disjoint (Set.range (j d).left.base) (Set.range (j d').left.base)) ∧
      (⋃ d, Set.range (j d).left.base) = Set.univ := by
  obtain ⟨Pd, j, e, h₁, -, h₂, h₃, h₄, hj⟩ :=
    exists_decomposition_picardFunctor_representableBy P hP
  obtain ⟨_, hPm⟩ := exists_commGrpObj_isPicardMul (X ↘ Spec (.of k)) hP
  obtain ⟨_, he⟩ := exists_commGrpObj_isPicardZeroMul (X ↘ Spec (.of k)) (e 0)
  refine ⟨inferInstance, Pd, j, e, inferInstance, hPm, he,
    isMonHom_of_isPicardMul _ hP hPm (e 0) he (fun L M hL hM ↦ ?_) (j 0) (hj 0), h₁, h₂, h₃, h₄⟩
  simpa using mul_mem_picardSubfunctorDegree (X ↘ Spec (.of k)) hL hM

end SubgroupScheme

section Translation

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]

/-- For representations `e`, `e'` of the same functor, the comparison isomorphism
`e.uniqueUpToIso e'` turns `e` into `e'`. -/
lemma _root_.CategoryTheory.Functor.RepresentableBy.homEquiv_comp_uniqueUpToIso_hom
    {C : Type*} [Category C] {F : Cᵒᵖ ⥤ Type*} {Y Y' : C} (e : F.RepresentableBy Y)
    (e' : F.RepresentableBy Y') {Z : C} (a : Z ⟶ Y) :
    e'.homEquiv (a ≫ (e.uniqueUpToIso e').hom) = e.homEquiv a := by
  rw [e'.homEquiv_comp,
    show (e.uniqueUpToIso e').hom = e'.homEquiv.symm (e.homEquiv (𝟙 Y)) from rfl,
    Equiv.apply_symm_apply, ← e.homEquiv_comp, Category.comp_id]

/-- **Translation by a class of degree `e`.** Let `M ∈ Pic X` have degree `e` and `d' = d + e`.
Schemes `P`, `P'` representing `Pic^d_{X/k}` and `Pic^{d'}_{X/k}` are isomorphic through an
isomorphism whose functor of points is tensoring with `pr_X^* M`: the point of `P` classifying a
class `ℒ` is sent to the point of `P'` classifying `ℒ ⊗ pr_X^* M`
(`AlgebraicGeometry.picardSubfunctorDegreeMulMapFst`). The inverse is tensoring with
`pr_X^* M⁻¹`, by the same statement applied to `M⁻¹`.

(blueprint: `prop-pd-picard-degree-decomposition`, part (4)) -/
theorem exists_iso_representableBy_picardFunctorDegree {d d' e : ℤ} (M : X.Pic)
    (hM : picDegreeHom k X M = .ofAdd e) (h : d' = d + e) (P P' : Over (Spec (.of k)))
    (hP : (picardFunctorDegree (X ↘ Spec (.of k)) d).obj.RepresentableBy P)
    (hP' : (picardFunctorDegree (X ↘ Spec (.of k)) d').obj.RepresentableBy P') :
    ∃ φ : P ≅ P', ∀ {T : Over (Spec (.of k))}
      (L : (picardSubfunctorDegree (X ↘ Spec (.of k)) d).toFunctor.obj (.op T)),
      hP.homEquiv.symm ((toSheafify (fppfTopology.over (Spec (.of k)))
          (picardSubfunctorDegree (X ↘ Spec (.of k)) d).toFunctor).app (.op T) L) ≫ φ.hom =
        hP'.homEquiv.symm ((toSheafify (fppfTopology.over (Spec (.of k)))
          (picardSubfunctorDegree (X ↘ Spec (.of k)) d').toFunctor).app (.op T)
            ((picardSubfunctorDegreeMulMapFst M hM h).app (.op T) L)) := by
  let J := fppfTopology.over (Spec (.of k))
  let ε := picardSubfunctorDegreeIsoOfDegree M hM h
  let E := (sheafToPresheaf J _).mapIso ((presheafToSheaf J (Type (u + 1))).mapIso ε)
  let R' := hP'.ofIso E.symm
  refine ⟨hP.uniqueUpToIso R', fun {T} L ↦ ?_⟩
  rw [eq_comm, Equiv.symm_apply_eq]
  have h₁ := hP.homEquiv_comp_uniqueUpToIso_hom R'
    (hP.homEquiv.symm ((toSheafify J (picardSubfunctorDegree (X ↘ Spec (.of k)) d).toFunctor).app
      (.op T) L))
  rw [Equiv.apply_symm_apply] at h₁
  have h₂ := ((E.app (.op T)).toEquiv.symm_apply_eq).1 h₁
  refine Eq.trans ?_ h₂.symm
  exact (congr_arg (fun ψ ↦ ψ.app (.op T) L) (toSheafify_naturality J ε.hom))

variable [IsSepClosed k] [GeometricallyIntegral (X ↘ Spec (.of k))]

/-- **`Pic^0 ≅ Pic^d` by tensoring with `𝒪_X(dx)`.** Let `X` be a smooth projective curve over a
separably closed field `k`. There are a rational point `x` of `X` and an isomorphism between
schemes `P₀`, `P_d` representing `Pic^0_{X/k}` and `Pic^d_{X/k}` whose functor of points is
`ℒ ↦ ℒ ⊗ pr_X^* 𝒪_X(dx)`. Here `𝒪_X(dx)` is the class `M` of `𝒪_X(-x)^{⊗(-d)}`, `𝒪_X(-x)` the
ideal sheaf of `x`, and the inverse isomorphism is tensoring with `pr_X^* 𝒪_X(-dx)`.

(blueprint: `prop-pd-picard-degree-decomposition`, part (4)) -/
theorem exists_iso_representableBy_picardFunctorDegree_zero (d : ℤ) (P₀ Pd : Over (Spec (.of k)))
    (hP₀ : (picardFunctorDegree (X ↘ Spec (.of k)) 0).obj.RepresentableBy P₀)
    (hPd : (picardFunctorDegree (X ↘ Spec (.of k)) d).obj.RepresentableBy Pd) :
    ∃ (x : (X ↘ Spec (.of k)).fieldPoints k) (M : X.Pic) (hM : picDegreeHom k X M = .ofAdd d),
      (letI := (Hom.isInvertible_ker_fieldPoints x).isInvertible_toModules;
        M = Pic.ofIsInvertible x.1.ker.toModules ^ (-d)) ∧
      ∃ φ : P₀ ≅ Pd, ∀ {T : Over (Spec (.of k))}
        (L : (picardSubfunctorDegree (X ↘ Spec (.of k)) 0).toFunctor.obj (.op T)),
        hP₀.homEquiv.symm ((toSheafify (fppfTopology.over (Spec (.of k)))
            (picardSubfunctorDegree (X ↘ Spec (.of k)) 0).toFunctor).app (.op T) L) ≫ φ.hom =
          hPd.homEquiv.symm ((toSheafify (fppfTopology.over (Spec (.of k)))
            (picardSubfunctorDegree (X ↘ Spec (.of k)) d).toFunctor).app (.op T)
              ((picardSubfunctorDegreeMulMapFst M hM (zero_add d).symm).app (.op T) L)) := by
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton (X ↘ Spec (.of k))
  obtain ⟨x⟩ := Hom.nonempty_fieldPoints (k := k) (X ↘ Spec (.of k))
  have := (Hom.isInvertible_ker_fieldPoints x).isInvertible_toModules
  have hM : picDegreeHom k X (Pic.ofIsInvertible x.1.ker.toModules ^ (-d)) = .ofAdd d := by
    rw [map_zpow, picDegreeHom_ofIsInvertible, degree_toModules_ker_fieldPoints, ← ofAdd_zsmul,
      smul_eq_mul, neg_mul_neg, _root_.mul_one]
  exact ⟨x, _, hM, rfl, exists_iso_representableBy_picardFunctorDegree _ hM _ P₀ Pd hP₀ hPd⟩

end Translation

end AlgebraicGeometry
