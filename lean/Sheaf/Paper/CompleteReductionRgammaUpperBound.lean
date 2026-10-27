/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.Paper.CompleteReductionSectionsModel
public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.CategoryTheory.StrictRoosModel
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.Paper.ReductionSectionsNormalizedResolution
import Sheaf.Paper.ReductionSectionsMilnor

/-!
# Complete reductions, ordinary derived sections and the one-degree limit bound

Source: Stacks Project, Cohomology on Sites, Tags 0D6K and 0A07;
Bhatt--Scholze, Proposition 3.5.1 and Definition 3.5.2; More on Algebra, Tags
07KW, 07KY and 08U5 (blueprint: lem-sfb-complete-reduction-rgamma-upper-bound).

A strict K-injective tower resolution computes the derived sections of the actual
quotient reductions. The comparison into its abelian-group Roos fibre is specified
by the ordinary-limit inclusion and the derived-sections unit. Thus the comparison
retains the completion augmentation, including its specified nullhomotopy.

## Main declarations

- `sections` and `rgamma`: ordinary module sections and their total right derived functor.
- `sectionTower` and `limitToRoos`: the strict section tower and its normalized comparison.
- `complete_reduction_rgamma_upper_bound`: the comparison isomorphism and upper bound.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CompleteReductionSections

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (U : Scheme.{u})

attribute [local instance] roosTowerEnoughInjectives roosLimitAdditive

/-- Complete reduction sections are the strict-tower derived inverse limit, and a
uniform upper bound on reduction cohomology loses at most one degree. A natural-number
index n denotes the positive exponent n+1. The first clause specifies the comparison
on every K-flat representative: j resolves its actual reduction tower; a is the unique
limit lift of the tensor units; c is the derived-limit comparison characterized by
its K-injective derived-sections unit and the strict ordinary-limit inclusion.

Source: Stacks 0D6K, 0A07, 07KW, 07KY and 08U5; Bhatt--Scholze, Proposition 3.5.1(1)
and Definition 3.5.2 (blueprint: lem-sfb-complete-reduction-rgamma-upper-bound).

Proof plan:
1. The internal/sectionwise equivalence of
   def-weil-pbc-internal-abelian-sheaf-module-equivalence leaves sections unchanged and
   preserves exact complexes, quasi-isomorphisms and K-injectives.
2. sk-def-pe-derived-completion identifies completeness with invertibility of the
   specified augmentation of the strict tensor-reduction tower of any K-flat model P.
3. Realize ordinary sections as direct image to the point, with constant-sheaf inverse
   image and the integer-to-coefficient unit map (def-weil-pbc-constant-sheaf,
   def-weil-pbc-sheafification, lem-weil-pbc-sheafification-sets-exact and
   def-weil-pbc-ringed-topos-morphism).
4. Resolve the strict tower by a K-injective complex with injective tower terms.
   lem-weil-ringed-tower-pushforward-limit-comparison identifies sections of its limit
   with the derived limit of its sections. The ordinary-limit inclusion gives c with
   the displayed normalization. The completion augmentation followed by this comparison
   is the displayed invertible map. lem-weil-pbc-ringed-strict-tower-homotopy-limit
   identifies the target with the Roos fibre of the actual quotient transitions.
5. lem-pc-derived-limit-milnor-sequence gives the Milnor short exact sequence with
   end terms R^1 lim H^(q-1) and lim H^q, without any Mittag--Leffler hypothesis.
6. For q > h+1 both towers vanish. lem-pc-derived-limit-roos-abelian-groups identifies
   their limits with the kernel and cokernel of 0 to 0, so the middle group vanishes.
This also applies to negative h, the zero complex, the empty scheme and E = Q_l. -/
theorem complete_reduction_rgamma_upper_bound
    (K : DerivedCategory (AdicCompletion.Modules l E U))
    (_hK : IsDerivedComplete l E U K) :
    (∀ (P : CochainComplex (AdicCompletion.Modules l E U) ℤ),
      (HomologicalComplex.quasiIso (AdicCompletion.Modules l E U) (.up ℤ)).kFlat P →
      ∀ e : DerivedCategory.Q.obj P ≅ K,
      ∃ (I : CochainComplex (ℕᵒᵖ ⥤ AdicCompletion.Modules l E U) ℤ)
        (j : Functor.ofOpSequence
          (X := fun n : ℕ ↦ (AdicCompletion.level l E U n).obj P)
          (AdicCompletion.levelStep l E U P) ⟶ I.asFunctor),
        I.IsKInjective ∧ (∀ q : ℤ, Injective (I.X q)) ∧
        (∀ n : ℕ, QuasiIso (j.app (op n))) ∧
        ∃ a : P ⟶ limit I.asFunctor,
          (∀ n : ℕ, a ≫ limit.π I.asFunctor (op n) =
            AdicCompletion.levelUnit l E U P n ≫ j.app (op n)) ∧
          ∃ c : (rgamma l E U).obj (DerivedCategory.Q.obj (limit I.asFunctor)) ≅
              DerivedCategory.Q.obj (roosF.obj (sectionTower l E U I)),
            (sections l E U).rightDerivedFunctorUnit.app
                ((HomotopyCategory.quotient _ _).obj (limit I.asFunctor)) ≫ c.hom =
              DerivedCategory.Q.map (limitToRoos l E U I) ∧
            IsIso ((rgamma l E U).map (e.inv ≫ DerivedCategory.Q.map a) ≫ c.hom)) ∧
    ∀ h : ℤ,
      (∀ (n : ℕ) (q : ℤ), h < q →
        IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
          ((rgamma l E U).obj (AdicCompletion.integralLevel l E U K n)))) →
      ∀ q : ℤ, h + 1 < q →
        IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
          ((rgamma l E U).obj K)) := by
  have comparison : ∀ (P : CochainComplex (AdicCompletion.Modules l E U) ℤ),
      (HomologicalComplex.quasiIso (AdicCompletion.Modules l E U) (.up ℤ)).kFlat P →
      ∀ e : DerivedCategory.Q.obj P ≅ K,
      ∃ (I : CochainComplex (ℕᵒᵖ ⥤ AdicCompletion.Modules l E U) ℤ)
        (j : Functor.ofOpSequence
          (X := fun n : ℕ ↦ (AdicCompletion.level l E U n).obj P)
          (AdicCompletion.levelStep l E U P) ⟶ I.asFunctor),
        I.IsKInjective ∧ (∀ q : ℤ, Injective (I.X q)) ∧
        (∀ n : ℕ, QuasiIso (j.app (op n))) ∧
        ∃ a : P ⟶ limit I.asFunctor,
          (∀ n : ℕ, a ≫ limit.π I.asFunctor (op n) =
            AdicCompletion.levelUnit l E U P n ≫ j.app (op n)) ∧
          ∃ c : (rgamma l E U).obj (DerivedCategory.Q.obj (limit I.asFunctor)) ≅
              DerivedCategory.Q.obj (roosF.obj (sectionTower l E U I)),
            (sections l E U).rightDerivedFunctorUnit.app
                ((HomotopyCategory.quotient _ _).obj (limit I.asFunctor)) ≫ c.hom =
              DerivedCategory.Q.map (limitToRoos l E U I) ∧
            IsIso ((rgamma l E U).map (e.inv ≫ DerivedCategory.Q.map a) ≫ c.hom) := by
    intro P hP e
    obtain ⟨I, j, hI, hterms, hj, a, ha, c, hc, haug⟩ :=
      reduction_sections_normalized_resolution l E U P hP
    have hcomplete := (AdicCompletion.isDerivedComplete_iff l E U K P hP e).mp _hK
    have : IsIso (e.inv ≫ DerivedCategory.Q.map (AdicCompletion.augmentation l E U P)) :=
      hcomplete
    have hη : IsIso (DerivedCategory.Q.map (AdicCompletion.augmentation l E U P)) :=
      IsIso.of_isIso_comp_left e.inv _
    have : IsIso (DerivedCategory.Q.map a) := haug hη
    exact ⟨I, j, hI, hterms, hj, a, ha, c, hc, inferInstance⟩
  refine ⟨comparison, ?_⟩
  intro h hlevels q hq
  obtain ⟨P, hP, ⟨e⟩, _⟩ := _hK
  obtain ⟨I, j, hI, _, hj, a, _, c, _, hiso⟩ := comparison P hP e
  have := hiso
  let z := asIso ((rgamma l E U).map (e.inv ≫ DerivedCategory.Q.map a) ≫ c.hom)
  obtain ⟨α, β, hz, hseq⟩ := reduction_sections_milnor l E U K P hP e I hI j hj
    ((rgamma l E U).obj K) z q
  have towerZero (i : ℤ) (hi : h < i) :
      IsZero (AdicCompletion.derivedTower l E U K ⋙ rgamma l E U ⋙
        DerivedCategory.homologyFunctor Ab.{u + 1} i) := by
    apply Functor.isZero
    intro n
    exact hlevels n.unop i hi
  have hleft : IsZero (((lim : (ℕᵒᵖ ⥤ Ab.{u + 1}) ⥤ Ab.{u + 1}).rightDerived 1).obj
      (AdicCompletion.derivedTower l E U K ⋙ rgamma l E U ⋙
        DerivedCategory.homologyFunctor Ab.{u + 1} (q - 1))) := by
    exact Functor.map_isZero _ (towerZero (q - 1) (by omega))
  have hright : IsZero (limit (AdicCompletion.derivedTower l E U K ⋙ rgamma l E U ⋙
      DerivedCategory.homologyFunctor Ab.{u + 1} q)) :=
    (limit.isLimit _).isZero_pt (towerZero q (by omega))
  exact hseq.exact.isZero_X₂ (hleft.eq_of_src _ _) (hright.eq_of_tgt _ _)

end AlgebraicGeometry.ProEtale.CompleteReductionSections
