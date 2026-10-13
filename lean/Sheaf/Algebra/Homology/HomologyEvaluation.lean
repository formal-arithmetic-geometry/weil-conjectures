/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.Algebra.Homology.HomComplexProjections
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Homology evaluation and locally split finite free complexes

Source: Stacks Project, Tags 0A8X, 08DH and 0BQY.
(blueprint: lem-sc-homology-evaluation-formal-complex). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory

/-- Restriction to an open scheme followed by an over site preserves zero morphisms.
Source: Stacks Project, Tag 08DL, termwise restriction.
(blueprint: lem-sc-homology-evaluation-formal-complex). -/
theorem moduleOpenOver_preservesZeroMorphisms (X : Scheme.{u})
    (V : X.Opens) (W : V.toScheme.Opens) :
    (Scheme.Modules.restrictFunctor V.ι ⋙
      SheafOfModules.overFunctor V.toScheme.ringCatSheaf W).PreservesZeroMorphisms := by
  constructor
  intro M N
  ext A x
  rfl

/-- Termwise restriction to an open scheme followed by an over site.
Source: Stacks Project, Tag 08DL, termwise restriction.
(blueprint: lem-sc-homology-evaluation-formal-complex). -/
noncomputable def moduleOpenOverComplexFunctor (X : Scheme.{u})
    (V : X.Opens) (W : V.toScheme.Opens) :
    CochainComplex X.Modules ℤ ⥤
      CochainComplex (SheafOfModules.{u} (V.toScheme.ringCatSheaf.over W)) ℤ :=
  letI := moduleOpenOver_preservesZeroMorphisms X V W
  (Scheme.Modules.restrictFunctor V.ι ⋙
    SheafOfModules.overFunctor V.toScheme.ringCatSheaf W).mapHomologicalComplex
      (ComplexShape.up ℤ)

/-- A complex admits a finite free, zero-differential model by a quasi-isomorphism roof.
Source: Stacks Project, Tag 0BQY, zero-differential Koszul calculation.
(blueprint: lem-sc-homology-evaluation-formal-complex). -/
def HasFiniteFreeZeroModel
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (T : CochainComplex (SheafOfModules.{u} R) ℤ) : Prop :=
  ∃ (E L : CochainComplex (SheafOfModules.{u} R) ℤ)
    (q : L ⟶ T) (p : L ⟶ E),
    QuasiIso q ∧ QuasiIso p ∧
      (∀ a b : ℤ, E.d a b = 0) ∧
      (∃ a b : ℤ, ∀ k : ℤ, k < a ∨ b < k → IsZero (E.X k)) ∧
      (∀ k : ℤ, ∃ r : ℕ, Nonempty (E.X k ≅
        SheafOfModules.free (R := R) (ULift.{u} (Fin r))))

/-- The degree component used to evaluate a Hom cocycle on a cycle.
Source: Stacks Project, Tag 0A8X, product definition of the Hom complex.
(blueprint: lem-sc-homology-evaluation-formal-complex). -/
noncomputable def homologyEvaluationProjection (X : AlgebraicGeometry.Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ) :
    (homComplex (R := X.sheaf) T J).X n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.X (-n)) (J.X 0) :=
  (Classical.choose (homComplex_projections_exists.{u, u, u, u}
    (R := X.sheaf))) T J n (-n) 0 (by omega)

/-- Characterization of evaluation on classes by its action on local cycle representatives.
Source: Stacks Project, Tags 0A8X and 08DH, evaluation of the Hom complex.
(blueprint: lem-sc-homology-evaluation-formal-complex). -/
def IsHomologyEvaluation (X : AlgebraicGeometry.Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ)
    (e : (homComplex (R := X.sheaf) T J).homology n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.homology (-n)) (J.homology 0)) : Prop :=
  let P := homComplex (R := X.sheaf) T J
  ∀ (U : X.Opens)
    (φ : (P.cycles n).val.obj (op U))
    (z : (T.cycles (-n)).val.obj (op U)) (b : (J.cycles 0).val.obj (op U)),
    (J.iCycles 0).val.app (op U) b =
      ((homologyEvaluationProjection X T J n).val.app (op U)
        ((P.iCycles n).val.app (op U) φ)).app
          (op (Over.mk (𝟙 U))) ((T.iCycles (-n)).val.app (op U) z) →
    (e.val.app (op U)
      ((P.homologyπ n).val.app (op U) φ)).app
        (op (Over.mk (𝟙 U))) ((T.homologyπ (-n)).val.app (op U) z) =
      (J.homologyπ 0).val.app (op U) b

/-- The uniquely characterized homology evaluation is perfect wherever the first complex
has a finite free zero-differential model and the second is a K-injective resolution
of a degree-zero module. No closed immersion or Koszul regularity enters this lemma.

Source: Stacks Project, sites-cohomology.tex, section-hom-complexes (0A8X);
cohomology.tex, section-internal-hom (08DH); duality.tex,
lemma-regular-ideal-ext (0BQY), zero-differential Hom calculation.
(blueprint: lem-sc-homology-evaluation-formal-complex).

Proof: Evaluate a degree-n Hom cocycle on a degree-minus-n cycle using the displayed
product projection. The Hom differential equation says the result is a degree-zero
cycle of J. Replacing the Hom cocycle by a boundary changes this value by a boundary
of J; replacing the T cycle by a boundary does the same. The bilinear evaluation
therefore descends through both homology cokernels. Curry it using the internal
Hom adjunction. Local lifts of classes to cycles exist because the homology class
maps are sheaf epimorphisms. This proves the displayed formula and also uniqueness:
check a map into internal Hom after evaluating on such lifts on a covering, then use
separatedness. The formula commutes with open restriction, which preserves cycles,
boundaries, homology and internal Hom. On the specified open site replace T by E
through the two quasi-isomorphisms in its roof. K-injectivity of the restricted J
makes both induced Hom-complex maps quasi-isomorphisms; evaluation commutes with
these maps. For E the Hom complex is a finite product of shifts of Hom(E^p,J).
Each E^p is finite free, so Hom(E^p,-) is exact. Only the p=-n summand contributes
to degree-n homology because J has no other cohomology. Its contribution is exactly
Hom(E^(-n),H^0(J)), and evaluation is the identity under this identification.
Thus evaluation is an isomorphism for E and hence for T. Rank zero, empty opens,
zero coefficient rings, and degrees outside the finite support give the same
calculation with zero objects. No chosen map or arbitrary existence witness
appears in the characterization of evaluation. -/
theorem exists_homologyEvaluation (X : AlgebraicGeometry.Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ)
    (hJ : ∀ k : ℤ, k ≠ 0 → IsZero (J.homology k)) :
    ∃! e : (homComplex (R := X.sheaf) T J).homology n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.homology (-n)) (J.homology 0),
      IsHomologyEvaluation X T J n e ∧
        ∀ (V : X.Opens) (W : V.toScheme.Opens),
          let Fc := moduleOpenOverComplexFunctor X V W
          CochainComplex.IsKInjective (Fc.obj J) →
          HasFiniteFreeZeroModel (V.toScheme.ringCatSheaf.over W) (Fc.obj T) →
          IsIso (((Scheme.Modules.restrictFunctor V.ι).map e).over W) := by sorry

/-- Homology evaluation, specified uniquely by cycle evaluation and its local calculation.
Source: Stacks Project, Tags 0A8X and 08DH.
(blueprint: lem-sc-homology-evaluation-formal-complex). -/
noncomputable def homologyEvaluation (X : AlgebraicGeometry.Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ)
    (hJ : ∀ k : ℤ, k ≠ 0 → IsZero (J.homology k)) :
    (homComplex (R := X.sheaf) T J).homology n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.homology (-n)) (J.homology 0) :=
  (exists_homologyEvaluation X T J n hJ).exists.choose

/-- The local perfection assertion for the uniquely specified evaluation map.
Source: Stacks Project, Tags 0A8X, 08DH and 0BQY.
(blueprint: lem-sc-homology-evaluation-formal-complex). -/
theorem homologyEvaluation_isIso (X : AlgebraicGeometry.Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ)
    (hJ : ∀ k : ℤ, k ≠ 0 → IsZero (J.homology k))
    (V : X.Opens) (W : V.toScheme.Opens)
    (hI : CochainComplex.IsKInjective ((moduleOpenOverComplexFunctor X V W).obj J))
    (hT : HasFiniteFreeZeroModel (V.toScheme.ringCatSheaf.over W)
      ((moduleOpenOverComplexFunctor X V W).obj T)) :
    IsIso (((Scheme.Modules.restrictFunctor V.ι).map
      (homologyEvaluation X T J n hJ)).over W) :=
  (exists_homologyEvaluation X T J n hJ).exists.choose_spec.2 V W hI hT

end CategoryTheory
