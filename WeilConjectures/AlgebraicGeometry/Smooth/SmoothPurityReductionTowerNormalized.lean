/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerData
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerDescent
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerAdjunct
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTorIntervals
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionLevelConstructible

/-! # The reduction tower is normalized

Source: blueprint latest, sec-smooth-purity, normalized-towers-reduction
(blueprint: det-sp-reduction-tower-normalized).

The data declarations are re-exported unchanged from SmoothPurityReductionTowerData.
The proof assembles strict descent, the actual reduction adjuncts, the Tor interval
comparison and finite-level constructibility. Positive level n+1 is indexed by n.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local instance] Sheaf.monoidalCategory

/-- Reconstruct the section-ring isomorphism from its multiplicative abelian map.
Source: IntegralCriterionReductions.liftSectionRingIso, Stacks 00YV. -/
private theorem ringPresheafMon_eq
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    [HasWeakSheafify J Ab.{u + 1}] [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (R : Sheaf J RingCat.{u + 1}) :
    (sheafToPresheaf J Ab.{u + 1}).monObjObj
      ((sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R) =
        R.obj.monObjCompForget₂ := by
  apply MonObj.ext
  let A := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  let : MonObj A.obj := R.obj.monObjCompForget₂
  exact Sheaf.μ_comp_map_mul A

private theorem liftSectionRingIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J Ab.{u + 1}] [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (A : Sheaf J Ab.{u + 1}) [MonObj A] [IsCommMonObj A]
    (S : Sheaf J CommRingCat.{u + 1})
    (a : A ≅ (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    [IsMonHom a.hom] :
    ∃! e : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J A ≅ S,
      (sheafCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})).map e.hom = a.hom := by
  let F := (Monoidal.monFunctorCategoryEquivalence Cᵒᵖ Ab.{u + 1}).functor
  let h := Functor.whiskerRight
    (F.map ((sheafToPresheaf J Ab.{u + 1}).mapMon.map (Mon.ofHom a.hom)))
    InternalAbelianSheafModule.monToRing
  let k := Functor.whiskerRight
    (F.map ((sheafToPresheaf J Ab.{u + 1}).mapMon.map (Mon.ofHom a.inv)))
    InternalAbelianSheafModule.monToRing
  let R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
  let B := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  have hmon : (sheafToPresheaf J Ab.{u + 1}).monObjObj B = R.obj.monObjCompForget₂ :=
    ringPresheafMon_eq J R
  let BP := F.obj ((sheafToPresheaf J Ab.{u + 1}).mapMon.obj (Mon.mk B)) ⋙
    InternalAbelianSheafModule.monToRing
  let b : BP ≅ R.obj := by
    refine NatIso.ofComponents (fun U ↦ ?_) (fun _ ↦ ?_)
    · refine @RingEquiv.toRingCatIso (BP.obj U) (R.obj.obj U)
        (RingCat.ring _) (RingCat.ring _) ?_
      refine { toEquiv := Equiv.refl _, map_add' := fun _ _ ↦ rfl, map_mul' := ?_ }
      intro x y
      change (((sheafToPresheaf J Ab.{u + 1}).monObjObj B).mul.app U).hom
        (TensorProduct.tmul ℤ x y) = _
      have hh := congrArg (fun m : MonObj B.obj ↦ m.mul) hmon
      rw [hh]
      rfl
    · ext x
      rfl
  let d : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J A ≅ S :=
    { hom := ⟨{ app := fun U ↦
                  @CommRingCat.ofHom
                    ((InternalAbelianSheafModule.sectionRingSheaf J A).obj.obj U)
                    (S.obj.obj U) _ _ ((h ≫ b.hom).app U).hom
                naturality := fun U V f ↦ by
                  apply (forget₂ CommRingCat RingCat).map_injective
                  exact (h ≫ b.hom).naturality f }⟩
      inv := ⟨{ app := fun U ↦
                  @CommRingCat.ofHom (S.obj.obj U)
                    ((InternalAbelianSheafModule.sectionRingSheaf J A).obj.obj U)
                    _ _ ((b.inv ≫ k).app U).hom
                naturality := fun U V f ↦ by
                  apply (forget₂ CommRingCat RingCat).map_injective
                  exact (b.inv ≫ k).naturality f }⟩
      hom_inv_id := by
        ext U x
        have hh := congr_app (congrArg (fun f : A ⟶ A ↦ f.hom) a.hom_inv_id) U
        exact ConcreteCategory.congr_hom hh x
      inv_hom_id := by
        ext U x
        have hh := congr_app (congrArg (fun f : B ⟶ B ↦ f.hom) a.inv_hom_id) U
        exact ConcreteCategory.congr_hom hh x }
  have hd : (sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).map d.hom = a.hom := by
    ext U x
    rfl
  refine ⟨d, hd, ?_⟩
  intro e he
  apply Iso.ext
  apply (sheafCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})).map_injective
  exact he.trans hd.symm

/-- Reduction is functorial into the ordinary derived category of strict coefficient
 towers, all its reduction maps are isomorphisms, and on qcqs schemes it carries
 bounded constructible integral complexes to normalized constructible finite-Tor towers,
 preserving every Tor interval, also as a cohomological interval at every level.
Source: blueprint latest, normalized-towers-reduction; Stacks 06YS, 06YY, 0G7E
(blueprint: det-sp-reduction-tower-normalized).

Proof:
1. Transport strict tensor descent to the fixed tower presentation, obtaining the
coefficient identification, ordinary and derived functors, comparison, and evaluations.
2. Identify the specified transition adjuncts with the successive derived scalar
extension isomorphisms. This proves normalization on every object without qcqs.
3. On a qcqs scheme the integral Tor comparison supplies finite Tor amplitude and
transfers every Tor interval to each reduction, also bounding its cohomology.
4. A common refinement of the integral cohomology stratifications, finite scalar
matrix resolutions, and their reduced truncation triangles give constructibility
of every finite-level cohomology sheaf.
5. Choose a finite integral Tor interval, widening its lower endpoint to the minimum
of its endpoints to make it ordered. Step 3 gives this same ordered Tor and
cohomological interval at every level. Combine it with step 4 for the finite-level
predicate and the common bounds, then with step 2 for the normalized predicate.
-/
theorem sp_reduction_tower_normalized (D : SpCoefficientTowersAbelian l E T) :
    Nonempty (SpReductionTower l E T D) := by
  have hlimit :=
    (sfb_integral_coefficient_limit l E T).choose_spec.choose_spec.choose_spec.2.2.2.2.2
  have hmon : IsMonHom (spIntegralAbComparison l E T).hom := hlimit.choose_spec.1.1
  obtain ⟨coefficient, hcomparison, _⟩ := liftSectionRingIso (Scheme.ProEt.topology T)
    (condensedRingObj (spIntegralCondensed l E) T)
    (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
    (spIntegralAbComparison l E T)
  have hcoefficient : ∀ (U : T.ProEtᵒᵖ)
      (x : (condensedRingObj (spIntegralCondensed l E) T).obj.obj U),
      coefficient.hom.hom.app U x = (spIntegralAbComparison l E T).hom.hom.app U x := by
    intro U x
    exact ConcreteCategory.congr_hom
      (congr_app (congrArg (fun f ↦ f.hom) hcomparison) U) x
  obtain ⟨ordinary, hadditive, level, transition, red, counit, universal,
      computes, evaluation, hevaluation⟩ :=
    sp_reduction_tower_presentation_descent l E T D coefficient
  have normalized := sp_reduction_tower_adjunct_normalization l E T D coefficient
    ordinary level transition red counit universal computes evaluation
  refine ⟨{
    coefficient := coefficient
    coefficient_normalized := hcoefficient
    ordinary := ordinary
    additive := hadditive
    level := level
    transition := transition
    red := red
    counit := counit
    universal := universal
    computes := computes
    evaluation := evaluation
    evaluation_normalized := hevaluation
    normalized := normalized
    constructible := ?_ }⟩
  intro hcompact hseparated M hM
  obtain ⟨hfinite, hinterval⟩ :=
    sp_reduction_tower_tor_intervals l E T D coefficient red evaluation M hM
  have hconstructible := sp_reduction_tower_level_constructibility l E T D coefficient
    hcoefficient red evaluation M hM
  refine ⟨hfinite, ⟨?_, normalized M⟩, hinterval⟩
  obtain ⟨a, b, htor⟩ := hfinite
  have hab : min a b ≤ b := min_le_right a b
  have hordered := htor.mono (min_le_left a b) le_rfl
  have hlevel := hinterval (min a b) b hab hordered
  constructor
  · intro n
    exact ⟨⟨min a b, b, hab, (hlevel n).2⟩, hconstructible n,
      min a b, b, (hlevel n).1⟩
  · exact ⟨min a b, b, min a b, b, hab, hab, fun n ↦
      ⟨(hlevel n).2, (hlevel n).1⟩⟩

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

end AlgebraicGeometry.ProEtale
