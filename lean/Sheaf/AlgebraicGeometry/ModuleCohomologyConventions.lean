/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q22 and H3
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
import WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleCechCocycleLiftMax
import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion
import WeilConjectures.AlgebraicGeometry.EtaleSiteCechComplexComparison

/-!
# Module cohomology is abelian cohomology

Source: Weil conjectures blueprint, main-20261015, sec-proper-base-change,
sk-def-pbc-conventions/sk-def-pbc-conventions-module-cohomology.md;
Stacks Project, Tags 03FD and 0D6J(3)
(blueprint: det-pbc-conventions-module-cohomology).

## Main declarations

* `moduleEvaluationForgetIso`: the identity of underived section functors.
* `moduleEvaluationForgetComparison`: its canonical higher-derived comparison.
* `module_cohomology_conventions`: all three numbered clauses of the blueprint.

The constant-coefficient ModuleCat encoding is the one recorded by
`def-weil-pbc-etale-sheaves` and `def-weil-pbc-derived-categories`. The explicit
constant-ring module equivalence identifies it with modules over the constant ring sheaf.
Cohomology over an etale object is the right derived functor of evaluation, as in
`def-weil-pbc-sites-and-cohomology`; localization identifies it with cohomology on
that object's small etale site. Comparisons below are the unit-compatible derived
comparisons of the identity on section groups, rather than arbitrary object isomorphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Evaluation commutes with forgetting constant module coefficients by the identity
on sections and section maps. Source: Stacks Project, Tag 03FD, equality of section
complexes (blueprint: det-pbc-conventions-module-cohomology). -/
def moduleEvaluationForgetIso (Λ : Type (u + 1)) [CommRing Λ]
    (T : Scheme.{u}) (U : T.Etale) :
    (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
      (evaluation _ _).obj (op U)) ⋙
        forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} ≅
      moduleAbelianForget Λ T ⋙
        (sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation _ _).obj (op U)) :=
  Iso.refl _

/-- The canonical derived evaluation comparison induced by the identity on sections.
Source: Stacks Project, Tag 03FD; its degree-zero normalization is the identity
(blueprint: det-pbc-conventions-module-cohomology). -/
def moduleEvaluationForgetComparison (Λ : Type (u + 1)) [CommRing Λ]
    (T : Scheme.{u}) (U : T.Etale) (q : ℕ) :
    (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
        (evaluation T.Etaleᵒᵖ (ModuleCat.{u + 1} Λ)).obj (op U)).rightDerived q ⋙
        forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} ⟶
      moduleAbelianForget Λ T ⋙
        (sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
          (evaluation T.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op U)).rightDerived q :=
  letI : PreservesColimitsOfSize.{u + 1, u + 1}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1, u + 1} Λ
  Functor.rightDerivedBaseChange.{u + 1, u + 2, u + 1, u + 2,
    u + 1, u + 2, u + 1, u + 2, u + 1, u + 1, u + 1, u + 1}
    (B := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (B' := Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (C := ModuleCat.{u + 1} Λ) (C' := AddCommGrpCat.{u + 1})
    (G := sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
      (evaluation T.Etaleᵒᵖ (ModuleCat.{u + 1} Λ)).obj (op U))
    (G' := sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (evaluation T.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op U))
    (β := moduleAbelianForget Λ T)
    (γ := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
    (moduleEvaluationForgetIso Λ T U).hom q

/-- The Cech criterion on all etale objects gives abelian evaluation acyclicity.
Source: Stacks 03FD, second proof paragraph, via 03FC and 03F9
(blueprint: det-pbc-conventions-module-cohomology). -/
private theorem moduleForget_injective_evaluation_isZero
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective G]
    (W : X.Etale) (n : ℕ) :
    IsZero (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (Opposite.op W)).rightDerived
        (n + 1)).obj ((moduleAbelianForget Λ X).obj G)) := by
  obtain ⟨e, ⟨eAb⟩⟩ := moduleSheaf_constantRing_equivalence Λ X
  let O := (sheafCompose X.smallEtaleTopology
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    ((constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of Λ))
  let I : SheafOfModules.{u + 1} O := e.functor.obj G
  have : Injective I := (e.map_injective_iff G).mpr inferInstance
  let J := X.smallEtaleTopology.toPrecoverage
  have hcech (U : X.Etale) (T : Type (u + 1)) (V : T → X.Etale)
      (f : ∀ t : T, V t ⟶ U) (hf : Sieve.ofArrows V f ∈ X.smallEtaleTopology U)
      (p : ℕ) (hp : 0 < p) :
      IsZero (((cechComplexFunctor fun t : T ↦ Over.mk (f t)).obj
        ((Over.forget U).op ⋙ ((SheafOfModules.toSheaf O).obj I).obj)).homology p) := by
    have hcover : Presieve.ofArrows V f ∈ J U := hf
    obtain ⟨S⟩ := CategoryTheory.SiteCechComplex.exists_of_covering J hcover
    have hzero : IsZero ((S.cohomologyFunctor p).obj I.val.presheaf) := by
      have : Injective I.val := injective_module_sheaf_injective_presheaf O I
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
      change IsZero ((S.complex I.val.presheaf).homology (q + 1))
      apply HomologicalComplex.ExactAt.isZero_homology
      apply (HomologicalComplex.exactAt_iff' (S.complex I.val.presheaf)
        q (q + 1) (q + 2) (by simp) (by simp)).2
      rw [ShortComplex.ab_exact_iff]
      intro c hc
      change (CochainComplex.of.d (S.cochains I.val.presheaf)
        (S.differential I.val.presheaf) (q + 1) ((q + 1) + 1)) c = 0 at hc
      rw [CochainComplex.of_d] at hc
      obtain ⟨b, hb⟩ := injective_presheaf_module_cech_cocycle_lift_max.{u + 1, u, u + 1}
        O.obj I.val V f S q c hc
      refine ⟨b, ?_⟩
      change (CochainComplex.of.d (S.cochains I.val.presheaf)
        (S.differential I.val.presheaf) q (q + 1)) b = c
      rw [CochainComplex.of_d]
      exact hb
    obtain ⟨c⟩ := Scheme.nonempty_etale_siteCech_complex_iso X U V f S I.val.presheaf
    exact hzero.of_iso ((HomologicalComplex.homologyFunctor _ _ p).mapIso c.symm)
  have hvan := Scheme.isZero_rightDerived_etale_of_cech_vanishing X Set.univ
    (fun W _ V f ↦ Sieve.ofArrows V f ∈ X.smallEtaleTopology W)
    ((SheafOfModules.toSheaf O).obj I)
    (fun _ _ _ _ h ↦ h)
    (fun _ _ _ _ _ ↦ ⟨Set.mem_univ _, fun _ ↦ Set.mem_univ _,
      fun _ _ ↦ Set.mem_univ _⟩)
    (fun _ _ T V f hf ↦ ⟨T, V, f, hf, fun t ↦ ⟨t, 𝟙 _, by simp⟩⟩)
    hcech W (Set.mem_univ _) (n + 1) (Nat.zero_lt_succ n)
  exact hvan.of_iso
    (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (Opposite.op W)).rightDerived
        (n + 1)).mapIso (eAb.app G).symm)

/-- All three module/abelian cohomology conventions, with their canonical maps.
Source: blueprint main-20261015, sec-proper-base-change/sk-def-pbc-conventions,
module-cohomology detail; Stacks Project, Tags 03FD, 03F3 and 0D6J(3)
(blueprint: det-pbc-conventions-module-cohomology).

Proof:
1. The explicit constant-ring equivalence carries an injective ModuleCat-valued
   sheaf to an injective sheaf of modules and identifies the underlying abelian
   sheaves. Exact module sheafification makes its module presheaf injective.
2. For every covering family, the universe-compatible cocycle-lifting theorem
   supplies a primitive for every positive Cech cocycle. The comparison with
   the categorical Cech complex gives zero positive Cech cohomology. Apply the
   etale Cech vanishing criterion with all objects and all coverings, then
   transport through the underlying-abelian isomorphism. This proves clause (1).
3. Apply the canonical bounded-below derived base-change invertibility theorem
   to evaluation, using this acyclicity and the identity on section groups.
   Exactness of coefficient forgetting and sheaf forgetting supplies its other
   hypotheses. Unfolding rightDerivedBaseChange transports invertibility through
   the single-object and homology comparison isomorphisms, proving clause (2).
4. The existing canonical module/abelian derived direct-image comparison gives
   invertibility on D+. Applying degree-q homology at F[0], as encoded by
   rightDerivedBaseChange, proves the higher direct-image assertion for all q.
5. Evaluate that same natural isomorphism at K for the final assertion.
   Neither argument asserts preservation of injectives by forgetting. -/
theorem module_cohomology_conventions (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) :
    (∀ (I : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective I]
      (U : T.Etale) (q : ℕ), 0 < q →
      IsZero (((sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation _ _).obj (op U)).rightDerived q).obj
          ((moduleAbelianForget Λ T).obj I))) ∧
    (∀ (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (U : T.Etale) (q : ℕ),
      IsIso ((moduleEvaluationForgetComparison Λ T U q).app F)) ∧
    (∀ (S : Scheme.{u}) (f : S ⟶ T)
      (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ),
      IsIso ((Functor.rightDerivedBaseChange.{u + 1, u + 2, u + 1, u + 2,
        u + 1, u + 2, u + 1, u + 2, u + 1, u + 1, u + 1, u + 1}
        (B := Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (B' := Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
        (C := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (C' := Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
        (G := lowerStar (ModuleCat.{u + 1} Λ) f)
        (G' := lowerStar AddCommGrpCat.{u + 1} f)
        (β := moduleAbelianForget Λ S) (γ := moduleAbelianForget Λ T)
        (moduleAbelianLowerStarIso Λ f).hom q).app F)) ∧
    (∀ (S : Scheme.{u}) (f : S ⟶ T)
      (K : _root_.DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      IsIso ((moduleAbelianDerivedLowerStarComparison Λ f).app K)) := by
  have hacy (I : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective I]
      (U : T.Etale) :
      (sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation T.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op U)).rightAcyclic
          ((moduleAbelianForget Λ T).obj I) :=
    fun n ↦ moduleForget_injective_evaluation_isZero Λ T I U n
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro I hI U q hq
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
    exact hacy I U n
  · intro F U q
    let : PreservesColimitsOfSize.{u + 1, u + 1}
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
      ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1, u + 1} Λ
    have := Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
      (moduleEvaluationForgetIso Λ T U) (fun I hI ↦ hacy I U)
    unfold moduleEvaluationForgetComparison Functor.rightDerivedBaseChange
    infer_instance
  · intro S f F q
    have := isIso_moduleAbelianDerivedLowerStarComparison Λ f
    unfold moduleAbelianDerivedLowerStarComparison at this
    unfold Functor.rightDerivedBaseChange
    infer_instance
  · intro S f K
    infer_instance

end AlgebraicGeometry.Etale
