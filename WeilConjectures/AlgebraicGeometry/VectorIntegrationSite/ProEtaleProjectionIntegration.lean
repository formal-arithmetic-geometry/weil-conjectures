/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleProjectiveCoefficient
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift

/-! # Canonical pro-etale ordered integration arrows
Source: main-20261015 vector-bundle integration and projective-line normalization
(blueprint: def-pur-proetale-projection-integration).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite
variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

private theorem properProjection_isIso_of_projection
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (W : DerivedCategory (Sheaf (Scheme.ProEt.topology X) B))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) B))
    (h : IsIso (((rightDerivedLowerStarProjectionMap B f).app W).app K)) :
    IsIso (properProjection B f W K) := by
  have := h
  delta properProjection
  exact ((((symmetry B Y).app K).app _ ≪≫
    asIso (((rightDerivedLowerStarProjectionMap B f).app W).app K) ≪≫
      (lowerStar B f).rightDerivedFunctor.mapIso
        (((symmetry B X).app W).app _)).isIso_hom)

private theorem properProjection_comparison_isIso
    (R : Type (u + 1)) [CommRing R] [Finite R] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f]
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)))
    (hM : DerivedCategory.TStructure.t.plus M) (a b : ℤ)
    (ht : _root_.DerivedCategory.torAmplitudeIn
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) a b M)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    IsIso (properProjection (ModuleCat.{u + 1} R) f
      ((comparison R X).obj M) ((comparison R Y).obj K.obj)) := by
  let B := ModuleCat.{u + 1} R
  have hML : DerivedCategory.TStructure.t.plus
      (((Etale.derivedTensor B X).obj M).obj
        ((Etale.upperStar B f).leftDerivedFunctor.obj K.obj)) := by
    obtain ⟨c, hc⟩ := K.property
    have : DerivedCategory.TStructure.t.IsGE K.obj c := hc
    have := (Etale.upperStar B f).isGE_mapDerivedCategory_obj K.obj c
    have : DerivedCategory.TStructure.t.IsGE
        ((Etale.upperStar B f).leftDerivedFunctor.obj K.obj) c :=
      DerivedCategory.TStructure.t.isGE_of_iso
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory B f).app K.obj).symm c
    exact ⟨a + c, DerivedCategory.isGE_tensor_of_torAmplitudeIn ht
      ((Etale.upperStar B f).leftDerivedFunctor.obj K.obj) c⟩
  have := Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite R f
  have := isIso_rightDerivedLowerStarProjectionMap_app_app_leftDerived B f M K.obj hM hML
  have hp := NatTrans.isIso_app_app_of_iso (rightDerivedLowerStarProjectionMap B f)
    ((comparisonUpperStar B X).leftDerivedFunctorIsoMapDerivedCategory.app M)
    ((comparisonUpperStar B Y).leftDerivedFunctorIsoMapDerivedCategory.app K.obj)
  exact properProjection_isIso_of_projection B f
    ((comparison R X).obj M) ((comparison R Y).obj K.obj) hp

set_option linter.unusedVariables false in
/-- Invertibility of the specified proper projection on bounded etale-origin inputs.
Source: Stacks 0GL1; Step 7 of the node
(blueprint: def-pur-proetale-projection-integration).
Proof: tensor the ordinary projection comparison square with the two canonical site
comparisons. The Tate line is locally free, so the proper projection theorem applies
without flatness of the coefficient ring over the Kummer ring. All four boundary
comparisons and the ordinary projection are invertible, hence so is this map.
-/
theorem projectiveProjection_isIso (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γ(T, ⊤)))
    (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)))) :
    IsIso (properProjection (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
      (ProjectiveLine T ↘ T)
      (line l E n r hA (ProjectiveLine T))
      ((comparison (Scheme.finiteTateCoefficient l E n) T).obj K.obj)) := by
  let R := Scheme.finiteTateCoefficient l E n
  let B := ModuleCat.{u + 1} R
  let P := ProjectiveLine T
  let q : P ⟶ T := ProjectiveLine T ↘ T
  let M := (linePlus l E n r hA P).obj
  have hN : 0 < l ^ (r + 1) := pow_pos (Fact.out : l.Prime).pos _
  have hP : IsUnit ((l ^ (r + 1) : ℕ) : Γ(P, ⊤)) := by
    simpa only [Nat.cast_pow, map_natCast] using (hT.map q.appTop.hom).pow (r + 1)
  have hflat : ObjectProperty.flat (Scheme.finiteEtaleTateLine P (l ^ (r + 1)) R hA) := by
    apply (ObjectProperty.flat_iff_preservesFiniteLimits _).2
    exact (Scheme.finite_etale_torsion_twist_line P (l ^ (r + 1)) hN
      (fun x ↦ by
        simpa only [map_natCast] using hP.map (P.presheaf.germ ⊤ x (by trivial)).hom)
      R hA 1).2.2.1
  have ht := Etale.DerivedCategory.torAmplitudeIn.shift
    (DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hflat) (2 : ℤ)
  exact properProjection_comparison_isIso R q M
    (linePlus l E n r hA P).property _ _ ht K

/-- The Hom type of the projective counit, using the canonical tensor source.
Source: Stacks 0GL1 (blueprint: def-pur-proetale-projection-integration). -/
@[implicit_reducible]
def ProjectiveEpsilonHom (T : Scheme.{u})
    (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) T) :=
  ProperIntegrationHom (Scheme.finiteTateCoefficient l E n) (ProjectiveLine T ↘ T)
    (line l E n r hA (ProjectiveLine T)) K

/-- The counit is uniquely determined by the actual proper projection and trace.
Source: Stacks 0GL1 (blueprint: def-pur-proetale-projection-integration).
Proof: the projection is invertible by projectiveProjection_isIso. Compose its
inverse with tensor of the supported trace and the right unitor. Cancellation
with the projection proves uniqueness.
-/
theorem existsUniqueProjectiveEpsilon (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γ(T, ⊤))) (hI : (ProjectiveLine.infinity T).ker.IsInvertible)
    (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)))) :
    ∃! e : ProjectiveEpsilonHom l E n T r hA K.obj,
      ProperIntegrationEquation (Scheme.finiteTateCoefficient l E n) (ProjectiveLine T ↘ T)
        (line l E n r hA (ProjectiveLine T)) K.obj (projectiveTrace l E n T hT hI r hA) e := by
  have hp := projectiveProjection_isIso l E n T hT r hA K
  refine ⟨properIntegration (Scheme.finiteTateCoefficient l E n) (ProjectiveLine T ↘ T)
    (line l E n r hA (ProjectiveLine T)) K.obj
    (projectiveTrace l E n T hT hI r hA) hp, ?_, ?_⟩
  · simp [ProperIntegrationEquation, properIntegration]
  · intro e he
    apply (cancel_epi (properProjection
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) (ProjectiveLine T ↘ T)
      (line l E n r hA (ProjectiveLine T))
      ((comparison (Scheme.finiteTateCoefficient l E n) T).obj K.obj))).1
    simpa [ProperIntegrationEquation, properIntegration] using he

/-- The unique counit determined by the actual proper projection and trace.
Source: Stacks 0GL1 (blueprint: def-pur-proetale-projection-integration). -/
@[irreducible]
def projectiveEpsilon (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γ(T, ⊤))) (hI : (ProjectiveLine.infinity T).ker.IsInvertible)
    (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)))) :
    ProjectiveEpsilonHom l E n T r hA K.obj :=
  (existsUniqueProjectiveEpsilon l E n T hT hI r hA K).exists.choose

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
