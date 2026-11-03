/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerInjectiveComponents
public import WeilConjectures.ProperBaseChange.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.Algebra.Homology.RestrictedTowerResolution.RestrictedTowerResolutionAcyclicity
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Canonical Roos triangle after completed scalar forgetting

Source: the Normalization sub-step of
`det-sp-integral-adjunction-bijection`, with the coefficient-limit convention of
`sk-def-sp-coefficient-towers` and Stacks Project Tags 0940 and 0941
(blueprint: lem-sp-completed-tower-roos).

The coefficient ring used for the strict tower is the canonical inverse limit of
`spCoefficientCommRings`; the pulled-back condensed integer ring is recorded by the
coefficient-limit comparison prerequisite.  The forgetting functor is the actual
levelwise restriction of scalars, including every strict-system transition.  The
right-derived inverse-limit interface supplies the K-injective resolutions, evaluation
comparison, normalized limit-cone projections, and the natural Roos triangle.

## Main definitions and statement

- `spCanonicalReduction`: the fixed pulled-back ell-power quotient maps.
- `spCondensedCoefficientLimitComparison`: the uniquely reduction-normalized ring iso.
- `spCompletedForgetting`: concrete scalar restriction retaining strict transitions.
- `spCompletedEvaluationCompatibility`: normalized derived level and transition comparisons.
- `spCompletedTowerRoos`: the natural, projection-normalized distinguished Roos triangle.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

attribute [local instance high] SheafOfModules.systemRingHasDerived
attribute [local instance high] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

/-- The coefficient-sized small presentation of the pro-etale site.
Source: sk-def-pe-site and def-weil-size-convention;
(blueprint: lem-sp-completed-tower-roos). -/
local instance proEtEssentiallySmall :
    EssentiallySmall.{max u (u + 1)} T.ProEt :=
  essentiallySmallSelf.{u, u, u + 1} _

/-- The normalized abelian coefficient-tower datum.
Source: `det-sp-coefficient-towers-abelian`, clauses (1)--(3).
Proof step: choose the supplied normalized equivalence; its transition and morphism
fields are the data used by the scalar-restriction functor below. -/
noncomputable def spTowerAbelianData :
    SpCoefficientTowersAbelian l E T :=
  Classical.choice (sp_coefficient_towers_abelian l E T)

/-- The commutative-ring inverse limit of the actual finite coefficient rings.
Source: `sk-def-sp-coefficient-towers`, coefficient-limit paragraph.
Proof step: use the categorical limit cone itself, retaining its commutative-ring
structure and hence its canonical projections. -/
noncomputable abbrev spCompletedCommRing :
    Sheaf (Scheme.ProEt.topology T) CommRingCat.{max u (u + 1)} :=
  limit (spCoefficientCommRings.{u, u} l E T)

/-- The underlying ring sheaf of the canonical completed coefficient ring. -/
noncomputable abbrev spCompletedRing :
    Sheaf (Scheme.ProEt.topology T) RingCat.{max u (u + 1)} :=
  (sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{max u (u + 1)} RingCat.{max u (u + 1)})).obj
      (spCompletedCommRing l E T)

/-- The pulled-back condensed coefficient ring from the coefficient convention.
Source: `det-def-sfb-pulled-back-coefficients` and the derived-Nakayama coefficient
construction. -/
noncomputable abbrev spCondensedCoefficientRing :
    Sheaf (Scheme.ProEt.topology T) Ab.{u + 1} :=
  condensedRingObj (DerivedNakayama.integerRing l E) T

/-- The canonical cone from the completed coefficient ring to the finite levels.
Source: `sk-def-sp-coefficient-towers`, coefficient-limit projections.
Proof step: package the universal limit projections as a natural transformation. -/
noncomputable def spCompletedCoefficientMap :
    (Functor.const ℕᵒᵖ).obj (spCompletedCommRing l E T) ⟶
      spCoefficientCommRings.{u, u} l E T := by
  let B := spCoefficientCommRings.{u, u} l E T
  exact {
    app := fun n ↦ limit.π B n
    naturality := by
      intro i j f
      exact (limit.w B f).symm }

/-- The canonical finite-level projection after forgetting commutativity.
Source: `sk-def-sp-coefficient-towers`, coefficient-limit projections. -/
noncomputable abbrev spCompletedProjection (n : ℕ) :
    spCompletedRing l E T ⟶
      (spCoefficientCommRings.{u, u} l E T ⋙
        sheafCompose (Scheme.ProEt.topology T)
          (forget₂ CommRingCat.{max u (u + 1)} RingCat.{max u (u + 1)})).obj (op n) :=
  (sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{max u (u + 1)} RingCat.{max u (u + 1)})).map
      ((spCompletedCoefficientMap l E T).app (op n))

/-- The underlying abelian sheaf of the canonical completed commutative ring. -/
noncomputable abbrev spCompletedRingAb :
    Sheaf (Scheme.ProEt.topology T) Ab.{u + 1} :=
  (sheafCompose (Scheme.ProEt.topology T)
    (forget₂ RingCat.{max u (u + 1)} Ab.{u + 1})).obj
      (spCompletedRing l E T)

/-- The underlying abelian sheaf at a finite coefficient level. -/
noncomputable abbrev spCoefficientLevelAb (n : ℕ) :
    Sheaf (Scheme.ProEt.topology T) Ab.{u + 1} :=
  (spCoefficientCommRings.{u, u} l E T ⋙
    sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{max u (u + 1)} RingCat.{max u (u + 1)}) ⋙
    sheafCompose (Scheme.ProEt.topology T)
      (forget₂ RingCat.{max u (u + 1)} Ab.{u + 1})).obj (op n)

/-- The finite-level projection viewed as a map of abelian sheaves. -/
noncomputable abbrev spCompletedProjectionAb (n : ℕ) :
    spCompletedRingAb l E T ⟶
      spCoefficientLevelAb l E T n :=
  (sheafCompose (Scheme.ProEt.topology T)
    (forget₂ RingCat.{max u (u + 1)} Ab.{u + 1})).map
    (spCompletedProjection l E T n)

/-- Forgetting coefficient multiplication preserves filtered colimits.
Source: the algebraic forgetful functors used in `sk-def-sp-coefficient-towers`;
(blueprint: lem-sp-completed-tower-roos). -/
local instance spForgetAbFiltered : PreservesFilteredColimits
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
  comp_preservesFilteredColimits _ _

/-- The canonical coefficient forgetful functor commutes with sheafification.
Source: `sk-def-sp-coefficient-towers`, finite constant sheaves;
(blueprint: lem-sp-completed-tower-roos). -/
local instance spProetPreservesSheafification :
    (Scheme.ProEt.topology T).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
  GrothendieckTopology.instPreservesSheafification _ _

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientRingSheafify in
/-- The unique ring comparison normalized against the independently fixed reductions.
Source: `sk-def-sp-coefficient-towers` and `det-def-sfb-pulled-back-coefficients`;
(blueprint: lem-sp-completed-tower-roos).
Every composite with a limit projection must equal `spCanonicalReduction`, which was defined
without reference to this iso. Joint monicity of the projections pins the iso uniquely. -/
def spCondensedCoefficientLimitComparison : Prop :=
  ∃! (e : spCondensedCoefficientRing l E T ≅ spCompletedRingAb l E T),
    IsMonHom e.hom ∧ IsMonHom e.inv ∧
      ∀ n : ℕ, e.hom ≫ spCompletedProjectionAb l E T n = spCanonicalReduction l E T n

/-- Additivity of the recorded normalized coefficient-tower equivalence.
Source: det-sp-coefficient-towers-abelian;
(blueprint: lem-sp-completed-tower-roos). -/
local instance spTowerEquivalenceAdditive :
    (spTowerAbelianData l E T).equivalence.functor.Additive :=
  (spTowerAbelianData l E T).equivalenceAdditive

/-- The ordinary derived category of modules over the completed ring.
Source: def-weil-abstract-derived-category;
(blueprint: lem-sp-completed-tower-roos). -/
local instance spCompletedModulesHasDerived :
    HasDerivedCategory.{max u (u + 1) + 1}
      (ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
        (spCompletedRing l E T)) :=
  HasDerivedCategory.standard _

/-- The ordinary derived category of strict completed-module towers.
Source: def-weil-abstract-derived-category;
(blueprint: lem-sp-completed-tower-roos). -/
local instance spCompletedTowerHasDerived :
    HasDerivedCategory.{max u (u + 1) + 1}
      (ℕᵒᵖ ⥤ ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
        (spCompletedRing l E T)) :=
  HasDerivedCategory.standard _

/-- The actual completed scalar-forgetting functor.
Source: Stacks 03CZ and 0940; blueprint `lem-sp-completed-tower-roos`.
Proof step: compose the normalized tower equivalence with
`RestrictedTowerResolution.restrictionFunctor`.  The latter applies
`SheafOfModules.restrictScalars` along each limit projection and keeps the strict
transition maps, with the canonical scalar-composition comparison on every arrow. -/
noncomputable def spCompletedForgetting :
    spCoefficientTowers l E T ⥤
      (ℕᵒᵖ ⥤ ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
        (spCompletedRing l E T)) := by
  let B : ℕᵒᵖ ⥤
      Sheaf (Scheme.ProEt.topology T) CommRingCat.{max u (u + 1)} :=
    spCoefficientCommRings.{u, u} l E T
  let A : Sheaf (Scheme.ProEt.topology T) CommRingCat.{max u (u + 1)} :=
    spCompletedCommRing l E T
  let α : (Functor.const ℕᵒᵖ).obj A ⟶ B := spCompletedCoefficientMap l E T
  exact (spTowerAbelianData l E T).equivalence.functor ⋙
    SheafOfModules.RestrictedTowerResolution.restrictionFunctor.{u + 1, u, max u (u + 1)}
      (C := T.ProEt) (J := Scheme.ProEt.topology T)
      (A := A) (B := B) (α := α)

/-- The levelwise restriction appearing in `spCompletedForgetting`.
Source: `def-pc-sheaf-restrict-scalars`; blueprint `lem-sp-completed-tower-roos`.
Proof step: evaluate the normalized strict system at level `n` and restrict scalars
along the canonical map `spCompletedProjection n`. -/
noncomputable abbrev spRestrictedLevel (n : ℕ) :
    spCoefficientTowers l E T ⥤
      ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
        (spCompletedRing l E T) :=
  spCoefficientEvaluation l E T (spTowerAbelianData l E T).equivalence n ⋙
    SheafOfModules.restrictScalars (spCompletedProjection l E T n)

/-- The exactness statement for the concrete scalar-forgetting functor.
Source: Stacks 03CZ and 0940; blueprint `lem-sp-completed-tower-roos`.
Proof step: restriction of scalars leaves the underlying sheaf and all kernels and
cokernels unchanged; the normalized tower equivalence is levelwise exact. -/
theorem spCompletedForgetting_exact :
    PreservesFiniteLimits (spCompletedForgetting l E T) ∧
      PreservesFiniteColimits (spCompletedForgetting l E T) := by
  sorry

/-- Finite-limit preservation by concrete completed scalar restriction.
Source: spCompletedForgetting_exact, kernel clause;
(blueprint: lem-sp-completed-tower-roos). -/
local instance spCompletedForgettingLimits :
    PreservesFiniteLimits (spCompletedForgetting l E T) :=
  (spCompletedForgetting_exact l E T).1

/-- Finite-colimit preservation by concrete completed scalar restriction.
Source: spCompletedForgetting_exact, cokernel clause;
(blueprint: lem-sp-completed-tower-roos). -/
local instance spCompletedForgettingColimits :
    PreservesFiniteColimits (spCompletedForgetting l E T) :=
  (spCompletedForgetting_exact l E T).2

/-- Additivity of the concrete composite of equivalence and scalar restriction.
Source: det-sp-coefficient-towers-abelian and def-pc-sheaf-restrict-scalars;
(blueprint: lem-sp-completed-tower-roos). -/
local instance spCompletedForgettingAdditive : (spCompletedForgetting l E T).Additive := by
  dsimp [spCompletedForgetting]
  infer_instance

/-- Additivity after evaluation of concrete scalar restriction.
Source: def-pc-sheaf-restrict-scalars, level evaluation;
(blueprint: lem-sp-completed-tower-roos). -/
local instance spRestrictedLevelAdditive (n : ℕ) : (spRestrictedLevel l E T n).Additive := by
  change (spCompletedForgetting l E T ⋙ (evaluation ℕᵒᵖ _).obj (op n)).Additive
  infer_instance

/-- Finite-limit preservation after level evaluation.
Source: spCompletedForgetting_exact, levelwise kernels;
(blueprint: lem-sp-completed-tower-roos). -/
local instance spRestrictedLevelLimits (n : ℕ) :
    PreservesFiniteLimits (spRestrictedLevel l E T n) := by
  change PreservesFiniteLimits (spCompletedForgetting l E T ⋙
    (evaluation ℕᵒᵖ _).obj (op n))
  infer_instance

/-- Finite-colimit preservation after level evaluation.
Source: spCompletedForgetting_exact, levelwise cokernels;
(blueprint: lem-sp-completed-tower-roos). -/
local instance spRestrictedLevelColimits (n : ℕ) :
    PreservesFiniteColimits (spRestrictedLevel l E T n) := by
  change PreservesFiniteColimits (spCompletedForgetting l E T ⋙
    (evaluation ℕᵒᵖ _).obj (op n))
  infer_instance

/-- Restriction at level `n` on the ordinary unbounded derived categories.
Source: `lem-weil-pbc-exact-functor-derived-factorization`;
(blueprint: lem-sp-completed-tower-roos).
Apply the exact-functor localization to `spRestrictedLevel`, so its value is
`Res_{a_n} C_n`, independently of the later `Edata` comparison. -/
noncomputable abbrev spRestrictedLevelDerived (n : ℕ) :=
  (spRestrictedLevel l E T n).mapDerivedCategory

/-- The retained ordinary successor transition between restricted level functors.
Source: `sk-def-sp-coefficient-towers`, actual semilinear transitions;
(blueprint: lem-sp-completed-tower-roos).
This is the corresponding arrow of the concrete scalar-forgotten strict tower. -/
noncomputable def spRestrictedTransition (n : ℕ) :
    spRestrictedLevel l E T (n + 1) ⟶ spRestrictedLevel l E T n where
  app M := ((spCompletedForgetting l E T).obj M).map (homOfLE (Nat.le_succ n)).op
  naturality _M _N f := ((spCompletedForgetting l E T).map f).naturality _ |>.symm

/-- The actual localized successor transition `u_n` on `Res_{a_n} C_n`.
Source: `lem-weil-pbc-exact-functor-derived-factorization`;
(blueprint: lem-sp-completed-tower-roos).
Localize the retained transition termwise via the canonical natural-transformation lift. -/
noncomputable abbrev spRestrictedDerivedTransition (n : ℕ) :
    spRestrictedLevelDerived l E T (n + 1) ⟶ spRestrictedLevelDerived l E T n :=
  Functor.mapDerivedCategoryNatTrans (spRestrictedTransition l E T n)

/-- The termwise derived functor of the concrete forgetting functor.
Source: `def-weil-abstract-derived-category`.
Proof step: apply Mathlib's localization functor to the additive concrete functor. -/
noncomputable abbrev spCompletedDerived :
    DerivedCategory.{max u (u + 1) + 1} (spCoefficientTowers l E T) ⥤
      DerivedCategory.{max u (u + 1) + 1}
        (ℕᵒᵖ ⥤ ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
          (spCompletedRing l E T)) :=
  letI : (spCompletedForgetting l E T).Additive := by
    dsimp [spCompletedForgetting]
    infer_instance
  (spCompletedForgetting l E T).mapDerivedCategory

/-- The total derived inverse-limit functor after scalar forgetting.
Source: Stacks 0940 and `lem-weil-pbc-ringed-strict-tower-homotopy-limit`.
Proof step: compose `spCompletedDerived` with the right-derived inverse limit. -/
noncomputable abbrev spCompletedTotal
    (RF : DerivedCategory.{max u (u + 1) + 1}
      (ℕᵒᵖ ⥤ ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
        (spCompletedRing l E T)) ⥤
      DerivedCategory.{max u (u + 1) + 1}
        (ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
          (spCompletedRing l E T))) :
    DerivedCategory.{max u (u + 1) + 1} (spCoefficientTowers l E T) ⥤
      DerivedCategory.{max u (u + 1) + 1}
        (ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
          (spCompletedRing l E T)) :=
  spCompletedDerived l E T ⋙ RF

/-- The derived object at one level of the scalar-forgotten Roos tower.
Source: `lem-weil-pbc-exact-functor-derived-factorization`;
(blueprint: lem-sp-completed-tower-roos).
This evaluates `Edata (D(F) C)` in the derived category over the canonical limit ring.
It is an object, unlike the ordinary module-valued functor `spCompletedEvaluation`
in `Sheaf.Paper.SmoothPurityTowerReconstructionData`. -/
noncomputable abbrev spRoosDerivedLevel
    (Edata : DerivedCategory.{max u (u + 1) + 1}
      (ℕᵒᵖ ⥤ ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
        (spCompletedRing l E T)) ⥤
      (ℕᵒᵖ ⥤ DerivedCategory.{max u (u + 1) + 1}
        (ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
          (spCompletedRing l E T))))
    (C : DerivedCategory.{max u (u + 1) + 1} (spCoefficientTowers l E T))
    (n : ℕ) :
    DerivedCategory.{max u (u + 1) + 1}
      (ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
        (spCompletedRing l E T)) :=
  (Edata.obj ((spCompletedDerived l E T).obj C)).obj (op n)

/-- The actual localized successor transition in the derived tower.
Source: `sk-def-sp-coefficient-towers`, semilinear transition clause; blueprint
`lem-sp-completed-tower-roos`.
Proof step: apply the derived evaluation functor to the successor morphism in the
strict-system index; no replacement transition is introduced. This is an arrow between
derived objects, unlike the ordinary natural transformation `spCompletedTransition`
in `Sheaf.Paper.SmoothPurityTowerReconstructionData`. -/
noncomputable abbrev spRoosDerivedTransition
    (Edata : DerivedCategory.{max u (u + 1) + 1}
      (ℕᵒᵖ ⥤ ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
        (spCompletedRing l E T)) ⥤
      (ℕᵒᵖ ⥤ DerivedCategory.{max u (u + 1) + 1}
        (ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
          (spCompletedRing l E T))))
    (C : DerivedCategory.{max u (u + 1) + 1} (spCoefficientTowers l E T))
    (n : ℕ) :
    spRoosDerivedLevel l E T Edata C (n + 1) ⟶
      spRoosDerivedLevel l E T Edata C n :=
  (Edata.obj ((spCompletedDerived l E T).obj C)).map
    (homOfLE (Nat.le_succ n)).op

/-- The canonical derived comparison with restricted levels, including its transition square.
Source: `lem-weil-pbc-exact-functor-derived-factorization` and the Normalization sub-step;
(blueprint: lem-sp-completed-tower-roos).
The equation on complexes fixes the comparison using the two exact localization factors and
`ε`. The second equation identifies the separately localized retained transitions with the
arrows of `Edata (D(F) C)`, so neither the levels nor their transitions are freely chosen. -/
noncomputable def spCompletedEvaluationCompatibility
    (Edata : DerivedCategory.{max u (u + 1) + 1}
      (ℕᵒᵖ ⥤ ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
        (spCompletedRing l E T)) ⥤
      (ℕᵒᵖ ⥤ DerivedCategory.{max u (u + 1) + 1}
        (ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
          (spCompletedRing l E T))))
    (ε : DerivedCategory.Q ⋙ Edata ≅
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        (Functor.whiskeringRight ℕᵒᵖ
          (CochainComplex (ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
            (spCompletedRing l E T)) ℤ)
          (DerivedCategory.{max u (u + 1) + 1}
            (ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
              (spCompletedRing l E T)))).obj DerivedCategory.Q) : Prop :=
  ∃ (κ : ∀ n : ℕ, spRestrictedLevelDerived l E T n ≅
        (spCompletedDerived l E T ⋙ Edata) ⋙
          (evaluation ℕᵒᵖ (DerivedCategory.{max u (u + 1) + 1}
            (ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
              (spCompletedRing l E T)))).obj (op n)),
    (∀ (n : ℕ) (X : CochainComplex (spCoefficientTowers l E T) ℤ),
      (κ n).hom.app (DerivedCategory.Q.obj X) ≫
          (Edata.map ((spCompletedForgetting l E T).mapDerivedCategoryFactors.hom.app X)).app
            (op n) ≫
          (ε.app (((spCompletedForgetting l E T).mapHomologicalComplex (.up ℤ)).obj X)).hom.app
            (op n) =
        (spRestrictedLevel l E T n).mapDerivedCategoryFactors.hom.app X) ∧
    (∀ (C : DerivedCategory.{max u (u + 1) + 1} (spCoefficientTowers l E T)) (n : ℕ),
      (spRestrictedDerivedTransition l E T n).app C ≫ (κ n).hom.app C =
        (κ (n + 1)).hom.app C ≫ spRoosDerivedTransition l E T Edata C n)

/-- The canonical complex-level limit cone used for projection normalization.
Source: Stacks 0940 and `lem-weil-derived-limit-tower-core-property-triangle`;
blueprint `lem-sp-completed-tower-roos`.
Proof step: apply the degreewise limit projections to the homological complex and
use the limit naturality equation for every tower arrow. -/
noncomputable def spCompletedLimitCone
    (I : CochainComplex
      (ℕᵒᵖ ⥤ ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
        (spCompletedRing l E T)) ℤ) : Cone I.asFunctor where
  pt := ((lim : (ℕᵒᵖ ⥤ ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
      (spCompletedRing l E T)) ⥤
      ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
        (spCompletedRing l E T)).mapHomologicalComplex (.up ℤ)).obj I
  π :=
    { app := fun n ↦
        (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app I
      naturality := by
        intro n m f
        ext q
        simp }

/-- The canonical complex-level limit cone is limiting.
Source and proof step: degreewise limits in the abelian module category, as in
`derivedCategory_towerLimit_triangle`; blueprint `lem-sp-completed-tower-roos`. -/
noncomputable def spCompletedLimitCone_isLimit
    (I : CochainComplex
      (ℕᵒᵖ ⥤ ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
        (spCompletedRing l E T)) ℤ) :
    IsLimit (spCompletedLimitCone l E T I) := by
  exact HomologicalComplex.isLimitOfEval I.asFunctor
    (spCompletedLimitCone l E T I) (fun q ↦ limit.isLimit (I.X q))

/-- The projection-normalization predicate for the completed tower.
Source: `lem-weil-derived-limit-tower-core-property-triangle` and Stacks 0941;
blueprint `lem-sp-completed-tower-roos`.
Proof step: on a K-injective representative `I`, the upstream unit `η` identifies
`Q (lim I)` with the right-derived limit, while the evaluation comparison `ε`
identifies each evaluated `Q I` with `E (Q I)`.  The first map is therefore the
product lift of the localized cone projections `Q.map (c.π.app (op n))`.
-/
noncomputable def spCompletedProjectionNormalization
    (RF : DerivedCategory.{max u (u + 1) + 1}
      (ℕᵒᵖ ⥤ ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
        (spCompletedRing l E T)) ⥤
      DerivedCategory.{max u (u + 1) + 1}
        (ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
          (spCompletedRing l E T)))
    (η : (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
        (spCompletedRing l E T)) ⥤
        ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
          (spCompletedRing l E T)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
        DerivedCategory.Q ⋙ RF)
    (hη : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I))
    (Edata : DerivedCategory.{max u (u + 1) + 1}
      (ℕᵒᵖ ⥤ ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
        (spCompletedRing l E T)) ⥤
      (ℕᵒᵖ ⥤ DerivedCategory.{max u (u + 1) + 1}
        (ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
          (spCompletedRing l E T))))
    [hproducts : HasCountableProducts
      (DerivedCategory.{max u (u + 1) + 1}
        (ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
          (spCompletedRing l E T)))]
    (ε : DerivedCategory.Q ⋙ Edata ≅
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        (Functor.whiskeringRight ℕᵒᵖ
          (CochainComplex (ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
            (spCompletedRing l E T)) ℤ)
          (DerivedCategory.{max u (u + 1) + 1}
            (ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
              (spCompletedRing l E T)))).obj DerivedCategory.Q)
    (p : ∀ Z, RF.obj Z ⟶ ∏ᶜ (fun n : ℕ ↦ (Edata.obj Z).obj (op n)))
    (C : DerivedCategory.{max u (u + 1) + 1} (spCoefficientTowers l E T)) : Prop :=
  ∃ (I : CochainComplex
      (ℕᵒᵖ ⥤ ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
        (spCompletedRing l E T)) ℤ)
    (hI : CochainComplex.IsKInjective I)
    (e : DerivedCategory.Q.obj I ≅ (spCompletedDerived l E T).obj C),
    letI : IsIso (η.app I) := hη I hI
    RF.map e.hom ≫ p ((spCompletedDerived l E T).obj C) =
      ((asIso (η.app I)).inv ≫
        Limits.Pi.lift (fun n : ℕ ↦
          DerivedCategory.Q.map
            ((spCompletedLimitCone l E T I).π.app (op n))) ≫
        Limits.Pi.map (fun n : ℕ ↦
          (ε.app I).inv.app (op n))) ≫
        Limits.Pi.map (fun n : ℕ ↦ (Edata.map e.hom).app (op n))

/-- The completed-tower Roos statement.
Source: Stacks Project Tags 0940 and 0941 and the Normalization sub-step of
`det-sp-integral-adjunction-bijection` (blueprint: lem-sp-completed-tower-roos).
Proof plan:
1. The finite constant comparison identifies the explicit continuous ell-power reductions
with the constant quotient reductions. Completeness and cofinality of ell- and uniformizer-
power ideals give the projection-normalized coefficient ring iso; the limit projections
force uniqueness. Restriction keeps the underlying sheaf and its kernels and cokernels;
levelwise exactness in both tower categories proves `spCompletedForgetting_exact`.
2. Apply exact-functor localization to F and its evaluations. Its factorization isos give
κ, and localization of the retained successor natural transformation gives its transition
square. Apply `ringedStrictTowerHomotopyLimitIndependentCoefficients` to the completed
coefficient ring for RF, η, shifts, ε, and K-injective resolutions. The right-derived
triangulated interface supplies the triangulated structure; compose with D(F) for L.
3. The module category is Grothendieck, hence has enough injectives, and countable products
are exact on the pro-etale site. On a K-injective strict-tower representative I, apply
`derivedCategory_towerLimit_triangle` to `spCompletedLimitCone I`, whose universal property
is `spCompletedLimitCone_isLimit`. Its first arrow is `Pi.lift (Q.map c.π)`.
4. Transport this core triangle by η, the resolution iso, and ε. Projection extensionality
identifies its first map with the stated normalized p. The κ transition square identifies
the second map with the actual 1-s on the restricted levels. Transport the connecting
map by the inverse product comparison and the shifted limit comparison. The resulting
triangle iso preserves distinguishedness; naturality gives the final p and δ equations. -/
theorem spCompletedTowerRoos :
    spCondensedCoefficientLimitComparison l E T ∧
      (PreservesFiniteLimits (spCompletedForgetting l E T) ∧
        PreservesFiniteColimits (spCompletedForgetting l E T)) ∧
      ∃ (RF : DerivedCategory.{max u (u + 1) + 1}
          (ℕᵒᵖ ⥤ ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
            (spCompletedRing l E T)) ⥤
          DerivedCategory.{max u (u + 1) + 1}
            (ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
              (spCompletedRing l E T)))
        (η : (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
            (spCompletedRing l E T)) ⥤
            ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
              (spCompletedRing l E T)).mapHomologicalComplex
              (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
            DerivedCategory.Q ⋙ RF),
        RF.IsRightDerivedFunctor η
          (HomologicalComplex.quasiIso
            (ℕᵒᵖ ⥤ ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
              (spCompletedRing l E T)) (ComplexShape.up ℤ)) ∧
        (∀ I, CochainComplex.IsKInjective I → IsIso (η.app I)) ∧
        (∀ X : CochainComplex
            (ℕᵒᵖ ⥤ ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
              (spCompletedRing l E T)) ℤ,
          ∃ (I : CochainComplex
              (ℕᵒᵖ ⥤ ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
                (spCompletedRing l E T)) ℤ) (j : X ⟶ I),
            I.IsKInjective ∧ QuasiIso j) ∧
        ∃ (_hshift : RF.CommShift ℤ)
          (_hproducts : HasCountableProducts
            (DerivedCategory.{max u (u + 1) + 1}
              (ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
                (spCompletedRing l E T))))
          (Edata : DerivedCategory.{max u (u + 1) + 1}
              (ℕᵒᵖ ⥤ ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
                (spCompletedRing l E T)) ⥤
              (ℕᵒᵖ ⥤ DerivedCategory.{max u (u + 1) + 1}
                (ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
                  (spCompletedRing l E T))))
          (ε : DerivedCategory.Q ⋙ Edata ≅
            HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
              (Functor.whiskeringRight ℕᵒᵖ
                (CochainComplex (ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
                  (spCompletedRing l E T)) ℤ)
                (DerivedCategory.{max u (u + 1) + 1}
                  (ringedSiteModules.{max u (u + 1), max u (u + 1), u, u + 1}
                    (spCompletedRing l E T)))).obj DerivedCategory.Q)
          (p : ∀ Z, RF.obj Z ⟶
            ∏ᶜ (fun n : ℕ ↦ (Edata.obj Z).obj (op n)))
          (δ : ∀ Z, (∏ᶜ (fun n : ℕ ↦ (Edata.obj Z).obj (op n))) ⟶
            (RF.obj Z)⟦(1 : ℤ)⟧),
          spCompletedEvaluationCompatibility l E T Edata ε ∧
          RF.IsTriangulated ∧
          (∀ C : DerivedCategory.{max u (u + 1) + 1} (spCoefficientTowers l E T),
            IsDerivedLimitTriangle
              (fun n : ℕ ↦ spRoosDerivedTransition l E T Edata C n)
              ((spCompletedTotal l E T RF).obj C)
              (p ((spCompletedDerived l E T).obj C))
              (δ ((spCompletedDerived l E T).obj C))) ∧
          (∀ (C : DerivedCategory.{max u (u + 1) + 1} (spCoefficientTowers l E T))
              (hη : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I)),
            spCompletedProjectionNormalization l E T RF η hη Edata ε p C) ∧
          (∀ {C D : DerivedCategory.{max u (u + 1) + 1} (spCoefficientTowers l E T)}
              (v : C ⟶ D),
            RF.map ((spCompletedDerived l E T).map v) ≫
                p ((spCompletedDerived l E T).obj D) =
              p ((spCompletedDerived l E T).obj C) ≫
                Limits.Pi.map (fun n ↦
                  (Edata.map ((spCompletedDerived l E T).map v)).app (op n))) ∧
          (∀ {C D : DerivedCategory.{max u (u + 1) + 1} (spCoefficientTowers l E T)}
              (v : C ⟶ D),
            Limits.Pi.map (fun n ↦
                (Edata.map ((spCompletedDerived l E T).map v)).app (op n)) ≫
                δ ((spCompletedDerived l E T).obj D) =
              δ ((spCompletedDerived l E T).obj C) ≫
                (RF.map ((spCompletedDerived l E T).map v))⟦(1 : ℤ)⟧') := by
  sorry

end AlgebraicGeometry.ProEtale
