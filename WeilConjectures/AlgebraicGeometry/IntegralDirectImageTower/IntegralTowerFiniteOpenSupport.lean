/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralDirectImageTowerData
import all WeilConjectures.Algebra.Homology.RingedOpenScalar.RingedOpenScalarAdjunction
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSlicePresentation
import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.SectionModuleOperationsData
import all WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerOpenAdjunctionEvaluation

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

/-! # Finite evaluated reduction preserves open support -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local instance 2000] localizedModuleExtension_additive
  localizedModuleExtension_limits localizedModuleExtension_colimits
  localizedModuleRestriction_additive localizedModuleRestriction_limits
  localizedModuleRestriction_colimits

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

private theorem evaluated_counit_isIso
    {A B C D : Type v} [Category.{w} A] [Category.{w} B]
    [Category.{w} C] [Category.{w} D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {P : A ⥤ C} {Q : B ⥤ D} (a : L ⊣ R) (b : L' ⊣ R')
    (e : L ⋙ Q ≅ P ⋙ L') (d : R ⋙ P ≅ Q ⋙ R')
    (hu : ∀ X, P.map (a.unit.app X) ≫ d.hom.app (L.obj X) ≫
      R'.map (e.hom.app X) = b.unit.app (P.obj X))
    (X : B) [IsIso (b.counit.app (Q.obj X))] :
    IsIso (Q.map (a.counit.app X)) := by
  have h := (RingedOpenScalar.equations_of_inverseMate e d.symm a b
    (RingedOpenScalar.inverseMate_of_unit e d.symm a b hu)).2 X
  rw [← h]
  infer_instance

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
