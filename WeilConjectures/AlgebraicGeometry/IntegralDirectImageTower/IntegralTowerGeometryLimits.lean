/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralDirectImageTowerData
import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralTowerOrdinaryLimit
import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralTowerLimitAdjunction
import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralTowerOpenMate
import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralTowerReductionPullback
import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralTowerFiniteOpenSupport

/-! # Components of the integral direct-image tower argument -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem moduleCast_heq {R : Type (u + 1)} [Ring R] {M N : ModuleCat R}
    (h : M = N) (x : M) : HEq (eqToHom h x) x := by
  subst N
  rfl

private theorem semilinearCast_sections {R S : Type (u + 1)} [Ring R] [Ring S]
    (φ ψ : R →+* S) (hφ : φ = ψ)
    {M M' : ModuleCat R} {N N' : ModuleCat S} (a : M = M') (b : N = N')
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N)
    (g : M' ⟶ (ModuleCat.restrictScalars ψ).obj N') (h : HEq f g) (x : M) :
    eqToHom b (f x) = g (eqToHom a x) := by
  subst ψ
  subst M'
  subst N'
  cases h
  rfl

private theorem moduleCast_naturality {R : Type (u + 1)} [Ring R]
    {M M' N N' : ModuleCat R} (hM : M = M') (hN : N = N')
    (f : M ⟶ N) (f' : M' ⟶ N') (h : HEq f f') :
    f ≫ eqToHom hN = eqToHom hM ≫ f' := by
  subst M'
  subst N'
  cases h
  rfl

private def evaluationSectionIso (s : Presentation l E) (T : Scheme.{u})
    (n : ℕ) (M : spCoefficientTowers l E T) (U : T.ProEtᵒᵖ) :
    ((SpTowerShriek.ev l E T n).obj
      ((s.base.realization T).functor.obj M)).val.obj U ≅
      ((spCoefficientEvaluation l E T (s.towers T).equivalence n).obj M).val.obj U := by
  have h := eq_of_heq ((s.base.sections T M n U).trans
    ((s.towers T).sections M n U).symm)
  let P := ((s.base.realization T).functor.obj M).val.obj (op (n, U.unop))
  have hc : ((eqToHom (WeilConjectures.SemilinearSections.evaluation_ring
      (Scheme.ProEt.topology T) (SpTowerShriek.B l E T)
      (SpTowerShriek.tau l E T) n).symm).hom.app U).hom =
      RingHom.id _ := by
    rw [ObjectProperty.eqToHom_hom, eqToHom_app]
    rfl
  change (ModuleCat.restrictScalars _).obj P ≅ _
  exact ModuleCat.restrictScalarsId'App _ hc P ≪≫ eqToIso h

private theorem evaluationSectionIso_sections (s : Presentation l E) (T : Scheme.{u})
    (n : ℕ) (M : spCoefficientTowers l E T) (U : T.ProEtᵒᵖ)
    (x : ((SpTowerShriek.ev l E T n).obj
      ((s.base.realization T).functor.obj M)).val.obj U) :
    HEq ((evaluationSectionIso l E s T n M U).hom x) x := by
  have h := eq_of_heq ((s.base.sections T M n U).trans
    ((s.towers T).sections M n U).symm)
  exact moduleCast_heq h x

private def evaluationObjectIso (s : Presentation l E) (T : Scheme.{u})
    (n : ℕ) (M : spCoefficientTowers l E T) :
    (SpTowerShriek.ev l E T n).obj ((s.base.realization T).functor.obj M) ≅
      (spCoefficientEvaluation l E T (s.towers T).equivalence n).obj M := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (evaluationSectionIso l E s T n M) ?_
  intro U V f
  have hU := eq_of_heq ((s.base.sections T M n U).trans
    ((s.towers T).sections M n U).symm)
  have hV := eq_of_heq ((s.base.sections T M n V).trans
    ((s.towers T).sections M n V).symm)
  have hr : ((WeilConjectures.SemilinearSections.ring
      (WeilConjectures.coefficientSequenceTopology (Scheme.ProEt.topology T))
      (WeilConjectures.SemilinearSections.systemRing
        (Scheme.ProEt.topology T) (SpTowerShriek.B l E T)
        (SpTowerShriek.tau l E T))).obj.map
          (Prod.mkHom (𝟙 n) f.unop).op).hom =
      ((SpTowerShriek.B l E T n).obj.map f).hom := by
    change ((forget₂ CommRingCat RingCat).map
      ((((WeilConjectures.SemilinearSections.rings
        (Scheme.ProEt.topology T) (SpTowerShriek.B l E T)
        (SpTowerShriek.tau l E T)).map (𝟙 (op n))).hom.app U) ≫
        (SpTowerShriek.B l E T n).obj.map f)).hom = _
    rw [(WeilConjectures.SemilinearSections.rings
      (Scheme.ProEt.topology T) (SpTowerShriek.B l E T)
      (SpTowerShriek.tau l E T)).map_id]
    rfl
  ext x
  exact semilinearCast_sections _ _ hr hU hV
    (((s.base.realization T).functor.obj M).val.map
      (Prod.mkHom (𝟙 n) f.unop).op)
    (((s.towers T).equivalence.functor.obj M).level n |>.val.map f)
    ((s.base.restrictions T M (Prod.mkHom (𝟙 n) f.unop).op).trans
      ((s.towers T).restrictions M n f).symm) x

private def normalizedEvaluation (s : Presentation l E) : Evaluation l E s where
  ordinary T n := NatIso.ofComponents (evaluationObjectIso l E s T n) (by
    intro M N a
    ext U x
    have h := moduleCast_naturality
      (eq_of_heq ((s.base.sections T M n U).trans
        ((s.towers T).sections M n U).symm))
      (eq_of_heq ((s.base.sections T N n U).trans
        ((s.towers T).sections N n U).symm))
      (((s.base.realization T).functor.map a).val.app (op (n, U.unop)))
      (((s.towers T).equivalence.functor.map a).app n |>.val.app U)
      ((s.base.morphisms T a (op (n, U.unop))).trans
        ((s.towers T).morphisms a n U).symm)
    exact congrArg (fun t ↦ t x) h)
  sections T n M U x := evaluationSectionIso_sections l E s T n M U x

/-- Construct normalized scalar/pullback comparisons and the total derived restricted limit.
Source: blueprint latest direct-image.proof.md paragraph (2), and the original node's
representative-normalization step.
Proof: identify the two sequence-site presentations by their identical local sections and
restriction maps. Scalar extension commutes with inverse image on generators: send
1 tensor f*(x) to f*(1 tensor x). These maps commute with quotient transitions and descend
on flat-term K-flat complexes using the fixed universal derived reduction counit. Their
representative equation is the localization equation. The open mate is invertible by the
exact slice tensor identity. Ordinary strict reduction is left adjoint to the inverse limit
of scalar-restricted levels: transpose each tensor map, then use the limit universal property.
This gives the specified ordinary unit formula. Derive this adjunction using K-flat and
K-injective resolutions; K-injectives compute the total right derived functor. The derived
hom-equivalence on representatives is the specified normalization. All these constructions
are valid for arbitrary schemes, including the empty scheme and zero modules.
(blueprint: lem-sp-integral-tower-geometry-limits). -/
theorem normalized_geometry_limits (s : Presentation l E) :
    ∃ (q : ReductionGeometry l E s) (_hq : OpenReductionIsIso l E s q),
      Nonempty (∀ T : Scheme.{u}, Limit l E s T) := by
  classical
  let q : ReductionGeometry l E s :=
    { evaluation := normalizedEvaluation l E s
      pullback := fun f ↦
        (normalized_reduction_pullback_existsUnique l E s
          (normalizedEvaluation l E s) f).exists.choose }
  refine ⟨q, ?_, ?_⟩
  · intro U T j hj N
    have hc : IsIso ((s.operations.openOp j).derivedAdjunction.counit.app
        ((derivedReduction l E s T).obj
          ((CondensedRing.openImmersionLowerShriek
            (spIntegralCondensed l E) j).mapDerivedCategory.obj N))) :=
      (s.laws.detects T _).2 (fun n ↦ finite_open_reduction_support l E s j N n)
    exact open_reduction_isIso_of_support l E s q j N hc
  · have hL (T : Scheme.{u}) : Nonempty (Limit l E s T) := by
      obtain ⟨adj, hnorm⟩ := ordinary_limit_adjunction l E s T
      exact limit_of_normalized_ordinary_adjunction l E s T adj hnorm
    exact ⟨fun T ↦ (hL T).some⟩

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
