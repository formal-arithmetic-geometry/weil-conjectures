/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.CompletePullbackReduction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

public import WeilConjectures.SixFunctors.ProEtale.DirectImageConeTowerNormalizationDefs
import WeilConjectures.SixFunctors.ProEtale.DirectImageConeTowerStrictComparison
import WeilConjectures.SixFunctors.ProEtale.DirectImageConeTowerKInjectiveNormalization

/-!
# Strict direct-image comparison for the reduction cone tower

Source: `literature/blueprint/latest/blueprint/sec-proper-base-change/
sk-prop-pbc-complete/prop-weil-pbc-direct-image-limits.proof.md`, proof (2),
the strict equality of reduction towers on a K-injective representative
(blueprint: `lem-weil-pbc-direct-image-cone-tower-strictness`).

The comparison is normalized on both summands of every mapping cone in every
tower level. The final clause records its K-injective realization through the
canonical right-derived-functor units and the direct-image mate.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesDerived AdicCompletion.finiteRingMonoidalObject
  AdicCompletion.finiteRingCommutative AdicCompletion.finiteModulesDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Existence of the normalized strict direct-image cone tower comparison.
The proof first writes every reduction level as the mapping cone of the scalar
endomorphism and uses the canonical two-summand biproduct comparison obtained
from the inclusions and projections. Additivity of direct image preserves the
four biproduct identities, and the coefficient mate `eta_f` carries scalar
multiplication to the same scalar after direct image. Thus the comparison is a
chain isomorphism, commutes with the `(pi, 1)` transitions, and is natural in
the input complex. For a K-injective representative, the right-derived
direct-image unit and the mate of the module adjunction identify this map with
the strict map; the triangle identity gives the displayed normalization.
Source: proof (2), the scalar-compatible cone calculation and derived mate
normalization (blueprint: lem-weil-pbc-direct-image-cone-tower-strictness-existence).
-/
theorem directImageConeTowerStrictness_exists :
    ∃ e : strictRed l E X ⋙ (push l E f).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      Functor.mapHomologicalComplex
        (CondensedRing.lowerStar (DerivedNakayama.integerRing l E) f)
          (ComplexShape.up ℤ) ⋙ strictRed l E Y,
      IsStrictDirectImageConeTower l E f e ∧
      IsKInjectiveDirectImageNormalization l E f e := by
  obtain ⟨e, he⟩ := strictDirectImageConeTower_comparison_exists l E f
  exact ⟨e, he, strictDirectImageConeTower_normalized l E f e he⟩

/-- Uniqueness of the normalized strict direct-image cone tower comparison.
At each degree and level the mapping cone is the biproduct of the shifted and
unshifted terms. The two strict normalization equations give the composites
of either candidate with both canonical cone inclusions. Since direct image
is additive, the corresponding inclusions and projections satisfy the usual
biproduct matrix identities after applying `push`; biproduct extensionality
therefore makes the two component maps equal. Naturality in the complex and
compatibility with all transitions then make the natural isomorphisms equal.
Source: proof (2), the finite biproduct summand uniqueness calculation
(blueprint: lem-weil-pbc-direct-image-cone-tower-strictness-uniqueness).
-/
theorem directImageConeTowerStrictness_unique
    {e e' : strictRed l E X ⋙ (push l E f).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      Functor.mapHomologicalComplex
        (CondensedRing.lowerStar (DerivedNakayama.integerRing l E) f)
          (ComplexShape.up ℤ) ⋙ strictRed l E Y}
    (he : IsStrictDirectImageConeTower l E f e)
    (he' : IsStrictDirectImageConeTower l E f e') : e = e' := by
  apply Iso.ext
  apply NatTrans.ext
  funext I
  apply HomologicalComplex.hom_ext
  intro i
  apply NatTrans.ext
  funext n
  rcases n with ⟨n⟩
  have hid := CochainComplex.mappingCone.id_X ((complexPowerMap l E X).app I) i (i + 1) rfl
  have h₁ := he.1 I i n
  have h₂ := he.2 I i n
  rw [← he'.1 I i n] at h₁
  rw [← he'.2 I i n] at h₂
  calc ((e.hom.app I).f i).app (op n)
      = ((push l E f).map
          (((CochainComplex.mappingCone.fst ((complexPowerMap l E X).app I)).1.v i (i + 1) rfl ≫
              (CochainComplex.mappingCone.inl ((complexPowerMap l E X).app I)).v (i + 1) i
                (by omega)) +
            (CochainComplex.mappingCone.snd ((complexPowerMap l E X).app I)).v i i (add_zero i) ≫
              (CochainComplex.mappingCone.inr ((complexPowerMap l E X).app I)).f i)).app (op n) ≫
          ((e.hom.app I).f i).app (op n) := by
        rw [hid]; simp
    _ = ((push l E f).map
          (((CochainComplex.mappingCone.fst ((complexPowerMap l E X).app I)).1.v i (i + 1) rfl ≫
              (CochainComplex.mappingCone.inl ((complexPowerMap l E X).app I)).v (i + 1) i
                (by omega)) +
            (CochainComplex.mappingCone.snd ((complexPowerMap l E X).app I)).v i i (add_zero i) ≫
              (CochainComplex.mappingCone.inr ((complexPowerMap l E X).app I)).f i)).app (op n) ≫
          ((e'.hom.app I).f i).app (op n) := by
        simp only [Functor.map_add, Functor.map_comp, NatTrans.app_add, NatTrans.comp_app,
          Preadditive.add_comp, Category.assoc, h₁, h₂]
    _ = ((e'.hom.app I).f i).app (op n) := by
        rw [hid]; simp

/-- The normalized strict cone comparison exists uniquely by the two summand
equations and has the canonical K-injective descent comparison.
Source: proof (2), strict equality of the reduction tower on a K-injective
representative (blueprint: `lem-weil-pbc-direct-image-cone-tower-strictness`).
Proof: `directImageConeTowerStrictness_exists` gives a comparison with both
normalizations; any other comparison satisfying the conjunction satisfies the
summand equations, so equals it by `directImageConeTowerStrictness_unique`. -/
theorem directImageConeTowerStrictness :
    ∃! e : strictRed l E X ⋙ (push l E f).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      Functor.mapHomologicalComplex
        (CondensedRing.lowerStar (DerivedNakayama.integerRing l E) f)
          (ComplexShape.up ℤ) ⋙ strictRed l E Y,
      IsStrictDirectImageConeTower l E f e ∧
      IsKInjectiveDirectImageNormalization l E f e := by
  obtain ⟨e, he, hn⟩ := directImageConeTowerStrictness_exists l E f
  refine ⟨e, ⟨he, hn⟩, ?_⟩
  intro e' he'
  exact directImageConeTowerStrictness_unique (l := l) (E := E) (f := f)
    (e := e') (e' := e) he'.1 he

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
