/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.VectorProjectiveCompletionData
import Sheaf.AlgebraicGeometry.SymmetricAlgebraDehomogenization

/-! # Affine dehomogenizations of a presented projective bundle

Source: Stacks Project, Constructions, Tags 01OA and 01NG.
(blueprint: lem-amb-vector-projective-dehomogenization). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Pointwise
noncomputable section
namespace AlgebraicGeometry.VectorProjectiveCompletion

private theorem degree_eq (S : Scheme.{u}) (F : S.Modules) (P : Presentation S F)
    (V : S.affineOpens) (n : ℕ) :
    P.algebra.grading V n = ((P.equiv V).toLinearMap.comp
      (SymmetricAlgebra.ι Γ(S, V.1) (Γ(S, V.1) × F.val.obj (op V.1)))).range ^ n := by
  rw [P.grade_eq]
  change (((SymmetricAlgebra.ι Γ(S, V.1)
    (Γ(S, V.1) × F.val.obj (op V.1))).range)^n).map
      (P.equiv V).toAlgHom.toLinearMap = _
  rw [Submodule.map_pow, ← LinearMap.range_comp]
  rfl
private theorem t_mem (S : Scheme.{u}) (F : S.Modules) (P : Presentation S F)
    (V : S.affineOpens) : t P V ∈ P.algebra.grading V 1 := by
  rw [degree_eq, pow_one]
  exact LinearMap.mem_range_self _ (1, 0)

private theorem x_mem (S : Scheme.{u}) (F : S.Modules) (P : Presentation S F)
    (V : S.affineOpens) (m : F.val.obj (op V.1)) :
    x P V m ∈ P.algebra.grading V (1 • (1 : ℕ)) := by
  rw [degree_eq]
  simp only [one_smul, pow_one]
  exact LinearMap.mem_range_self _ (0, m)
private theorem t_restriction (S : Scheme.{u}) (F : S.Modules) (P : Presentation S F)
    (U V : S.affineOpens) (h : U.1 ≤ V.1) : P.algebra.res h (t P V) = t P U := by
  simpa only [t, map_one, map_zero] using P.restriction U V h 1 0
private theorem x_restriction (S : Scheme.{u}) (F : S.Modules) (P : Presentation S F)
    (U V : S.affineOpens) (h : U.1 ≤ V.1) (m : F.val.obj (op V.1)) :
    P.algebra.res h (x P V m) = x P U (F.val.map (homOfLE h).op m) := by
  simpa only [x, map_zero] using P.restriction U V h 0 m
private def awayRestriction (S : Scheme.{u}) (F : S.Modules) (P : Presentation S F)
    (U V : S.affineOpens) (h : U.1 ≤ V.1) :
    HomogeneousLocalization.Away (P.algebra.grading V) (t P V) →+*
      HomogeneousLocalization.Away (P.algebra.grading U) (t P U) :=
  HomogeneousLocalization.map (P.algebra.res h) (by
    rintro z ⟨n, rfl⟩
    exact ⟨n, by rw [map_pow, t_restriction S F P U V h]⟩)
private theorem awayRestriction_mk (S : Scheme.{u}) (F : S.Modules) (P : Presentation S F)
    (U V : S.affineOpens) (h : U.1 ≤ V.1) (n : ℕ) (a : P.algebra.obj V)
    (ha : a ∈ P.algebra.grading V (n • (1 : ℕ))) :
    awayRestriction S F P U V h
      (HomogeneousLocalization.Away.mk (P.algebra.grading V) (t_mem S F P V) n a ha) =
    HomogeneousLocalization.Away.mk (P.algebra.grading U) (t_mem S F P U) n
      (P.algebra.res h a) ((P.algebra.res h).map_mem ha) := by
  simp only [awayRestriction, HomogeneousLocalization.Away.mk, HomogeneousLocalization.map_mk]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mk]
  congr 1
  apply Subtype.ext
  simp only [map_pow, t_restriction S F P U V h]
private theorem scalar_as_mk (S : Scheme.{u}) (F : S.Modules) (P : Presentation S F)
    (V : S.affineOpens) (r : Γ(S, V.1)) :
    algebraMap Γ(S, V.1)
      (HomogeneousLocalization.Away (P.algebra.grading V) (t P V)) r =
    HomogeneousLocalization.Away.mk (P.algebra.grading V) (t_mem S F P V) 0
      (algebraMap Γ(S, V.1) (P.algebra.obj V) r)
      (by simpa only [zero_smul, SetLike.GradeZero.coe_algebraMap] using
        (algebraMap Γ(S, V.1) (P.algebra.grading V 0) r).property) := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_algebraMap, HomogeneousLocalization.Away.val_mk,
    pow_zero]
  rfl

private theorem awayRestriction_scalar (S : Scheme.{u}) (F : S.Modules)
    (P : Presentation S F) (U V : S.affineOpens) (h : U.1 ≤ V.1) (r : Γ(S, V.1)) :
    awayRestriction S F P U V h
      (algebraMap Γ(S, V.1)
        (HomogeneousLocalization.Away (P.algebra.grading V) (t P V)) r) =
      algebraMap Γ(S, U.1)
        (HomogeneousLocalization.Away (P.algebra.grading U) (t P U))
          (S.presheaf.map (homOfLE h).op r) := by
  rw [scalar_as_mk, awayRestriction_mk]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_algebraMap,
    P.algebra.res_algebraMap, pow_zero]
  rfl
private theorem generator_as_mk (S : Scheme.{u}) (F : S.Modules) (P : Presentation S F)
    (a : ∀ V : S.affineOpens, SymmetricAlgebraSheaf.sections F (op V.1) ≃+*
      HomogeneousLocalization.Away (P.algebra.grading V) (t P V))
    (hgen : ∀ (V : S.affineOpens) (m : F.val.obj (op V.1)),
      (a V (SymmetricAlgebra.ι _ _ m)).val =
        algebraMap (P.algebra.obj V) (Localization.Away (t P V)) (x P V m) *
          IsLocalization.Away.invSelf (t P V))
    (V : S.affineOpens) (m : F.val.obj (op V.1)) :
    a V (SymmetricAlgebra.ι _ _ m) =
      HomogeneousLocalization.Away.mk (P.algebra.grading V) (t_mem S F P V) 1
        (x P V m) (x_mem S F P V m) := by
  apply HomogeneousLocalization.val_injective
  rw [hgen, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk',
    IsLocalization.mk'_eq_mul_mk'_one]
  simp only [pow_one]
  rfl
private theorem dehom_restriction (S : Scheme.{u}) (F : S.Modules) (P : Presentation S F)
    (a : ∀ V : S.affineOpens, SymmetricAlgebraSheaf.sections F (op V.1) ≃+*
      HomogeneousLocalization.Away (P.algebra.grading V) (t P V))
    (hgen : ∀ (V : S.affineOpens) (m : F.val.obj (op V.1)),
      (a V (SymmetricAlgebra.ι _ _ m)).val =
        algebraMap (P.algebra.obj V) (Localization.Away (t P V)) (x P V m) *
          IsLocalization.Away.invSelf (t P V))
    (hscalar : ∀ (V : S.affineOpens) (r : Γ(S, V.1)),
      a V (algebraMap Γ(S, V.1) (SymmetricAlgebraSheaf.sections F (op V.1)) r) =
        algebraMap Γ(S, V.1)
          (HomogeneousLocalization.Away (P.algebra.grading V) (t P V)) r)
    (U V : S.affineOpens) (h : U.1 ≤ V.1) (f : SymmetricAlgebraSheaf.sections F (op V.1)) :
    awayRestriction S F P U V h (a V f) =
      a U (SymmetricAlgebraSheaf.restriction F (homOfLE h).op f) := by
  induction f using SymmetricAlgebra.induction with
  | algebraMap r =>
      rw [hscalar, awayRestriction_scalar, SymmetricAlgebraSheaf.restriction_algebraMap,
        hscalar]
  | ι m =>
      rw [generator_as_mk S F P a hgen, awayRestriction_mk,
        SymmetricAlgebraSheaf.restriction_ι, generator_as_mk S F P a hgen]
      simp only [x_restriction]
  | mul f g hf hg => simp only [map_mul, hf, hg]
  | add f g hf hg => simp only [map_add, hf, hg]

private theorem awayι_map {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    (G : ℕ → σ) (H : ℕ → τ) [GradedRing G] [GradedRing H]
    (φ : G →+*ᵍ H)
    (hφ : HomogeneousIdeal.irrelevant H ≤ (HomogeneousIdeal.irrelevant G).map φ)
    (s : A) (t : B) (hs : s ∈ G 1) (ht : t ∈ H 1) (h : φ s = t) :
    Spec.map (CommRingCat.ofHom (HomogeneousLocalization.map φ (by
      rintro z ⟨n, rfl⟩
      exact ⟨n, by rw [map_pow, h]⟩))) ≫
      Proj.awayι G s hs Nat.one_pos =
    Proj.awayι H t ht Nat.one_pos ≫ Proj.map φ hφ := by
  subst t
  exact (Proj.awayι_comp_map φ hφ Nat.one_pos s hs).symm
set_option backward.isDefEq.respectTransparency.types false in
private theorem chart_restriction (S : Scheme.{u}) (F : S.Modules) (P : Presentation S F)
    (ht : ∀ V : S.affineOpens, t P V ∈ P.algebra.grading V 1)
    (a : ∀ V : S.affineOpens, SymmetricAlgebraSheaf.sections F (op V.1) ≃+*
      HomogeneousLocalization.Away (P.algebra.grading V) (t P V))
    (hgen : ∀ (V : S.affineOpens) (m : F.val.obj (op V.1)),
      (a V (SymmetricAlgebra.ι _ _ m)).val =
        algebraMap (P.algebra.obj V) (Localization.Away (t P V)) (x P V m) *
          IsLocalization.Away.invSelf (t P V))
    (hscalar : ∀ (V : S.affineOpens) (r : Γ(S, V.1)),
      a V (algebraMap Γ(S, V.1) (SymmetricAlgebraSheaf.sections F (op V.1)) r) =
        algebraMap Γ(S, V.1)
          (HomogeneousLocalization.Away (P.algebra.grading V) (t P V)) r)
    (U V : S.affineOpens) (h : U.1 ≤ V.1) :
    Spec.map (CommRingCat.ofHom (SymmetricAlgebraSheaf.restriction F (homOfLE h).op)) ≫
      chartMap P ht a V = chartMap P ht a U := by
  have hr : (SymmetricAlgebraSheaf.restriction F (homOfLE h).op).comp
      (a V).symm.toRingHom = (a U).symm.toRingHom.comp (awayRestriction S F P U V h) := by
    apply RingHom.ext
    intro z
    apply (a U).injective
    change a U (SymmetricAlgebraSheaf.restriction F (homOfLE h).op ((a V).symm z)) =
      a U ((a U).symm (awayRestriction S F P U V h z))
    rw [RingEquiv.apply_symm_apply, ← dehom_restriction S F P a hgen hscalar,
      RingEquiv.apply_symm_apply]
  have hc := awayι_map (P.algebra.grading V) (P.algebra.grading U)
    (P.algebra.res h) (P.algebra.irrelevant_le_map_res h) (t P V) (t P U) (ht V) (ht U)
      (t_restriction S F P U V h)
  change Spec.map (CommRingCat.ofHom (awayRestriction S F P U V h)) ≫
    Proj.awayι (P.algebra.grading V) (t P V) (ht V) Nat.one_pos =
    Proj.awayι (P.algebra.grading U) (t P U) (ht U) Nat.one_pos ≫
      Proj.map (P.algebra.res h) (P.algebra.irrelevant_le_map_res h) at hc
  simp only [chartMap, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  rw [hr, CommRingCat.ofHom_comp, Spec.map_comp_assoc]
  apply congrArg (fun f ↦ Spec.map (CommRingCat.ofHom (a U).symm.toRingHom) ≫ f)
  rw [← Category.assoc, hc, Category.assoc]
  rw [← P.algebra.relProjFunctor_map_homOfLE h,
    P.algebra.relProjFunctor_map_relProjι]

/-- Every affine presentation has its dehomogenization with the prescribed generator formula.
Source: Stacks Project, Constructions, Tags 01OA and 01NG.
(blueprint: lem-amb-vector-projective-dehomogenization).

Proof: apply the symmetric algebra dehomogenization to each affine section ring.
Its generator map is division by the distinguished degree-one coordinate, and it fixes
coefficients. This works on every affine open without assuming its module of sections free.
The proof by homogeneous fractions is valid also for zero rings. Restrictions preserve t
and carry x(m) to x(res(m)); the same equality on scalars and generators proves naturality
on every element. Proj functoriality on away charts and the defining relative-Proj
restriction cocone then give the stated equation of scheme morphisms. -/
theorem exists_affineDehomogenization (S : Scheme.{u}) (F : S.Modules)
    (P : Presentation S F) :
    ∃ (ht : ∀ V : S.affineOpens, t P V ∈ P.algebra.grading V 1)
      (a : ∀ V : S.affineOpens, SymmetricAlgebraSheaf.sections F (op V.1) ≃+*
        HomogeneousLocalization.Away (P.algebra.grading V) (t P V)),
      (∀ (V : S.affineOpens) (m : F.val.obj (op V.1)),
        (a V (SymmetricAlgebra.ι _ _ m)).val =
          algebraMap (P.algebra.obj V) (Localization.Away (t P V)) (x P V m) *
            IsLocalization.Away.invSelf (t P V)) ∧
      (∀ (V : S.affineOpens) (r : Γ(S, V.1)),
        a V (algebraMap Γ(S, V.1) (SymmetricAlgebraSheaf.sections F (op V.1)) r) =
          algebraMap Γ(S, V.1)
            (HomogeneousLocalization.Away (P.algebra.grading V) (t P V)) r) ∧
      (∀ (U V : S.affineOpens) (h : U.1 ≤ V.1),
        Spec.map (CommRingCat.ofHom (SymmetricAlgebraSheaf.restriction F (homOfLE h).op)) ≫
          chartMap P ht a V = chartMap P ht a U) := by
  classical
  have hex (V : S.affineOpens) := SymmetricAlgebra.exists_dehomogenization
    Γ(S, V.1) (F.val.obj (op V.1)) (P.equiv V) (P.algebra.grading V)
      (degree_eq S F P V)
  choose a hgen hscalar using hex
  exact ⟨t_mem S F P, a, hgen, hscalar, chart_restriction S F P _ a hgen hscalar⟩

end AlgebraicGeometry.VectorProjectiveCompletion
