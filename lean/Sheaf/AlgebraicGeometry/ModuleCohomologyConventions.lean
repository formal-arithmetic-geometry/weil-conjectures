/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison
import Sheaf.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import Mathlib.CategoryTheory.Abelian.RightDerived

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

/-- All three module/abelian cohomology conventions, with their canonical maps.
Source: blueprint main-20261015, sec-proper-base-change/sk-def-pbc-conventions,
module-cohomology detail; Stacks Project, Tags 03FD, 03F3 and 0D6J(3)
(blueprint: det-pbc-conventions-module-cohomology).

Proof:
1. Enough injectives and exact forgetting are supplied by
   lem-weil-pbc-module-sheaves-enough-injectives and
   lem-weil-pbc-module-sheaves-colimits-forgetful. Exactness preserves kernels,
   images and cohomology, hence quasi-isomorphisms and the bounded-below condition.
2. lem-weil-pbc-cohomology-over-object-localization and
   lem-weil-pbc-etale-site-localization-open identify derived evaluation at U
   with cohomology of the restriction on U_et.
3. Apply lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison to the
   constant ring sheaf. On an injective module sheaf, the positive derived
   evaluation vanishes by lem-weil-pbc-derived-functor-injective-vanishing.
   This proves the first conjunct without claiming abelian injectivity.
4. For an arbitrary module sheaf the same evaluation comparison is the identity
   on sections in degree zero. Both forgotten module cohomology and derived
   abelian evaluation of a module resolution are the kernel modulo the image
   of the same section differential. The comparison is therefore precisely
   the canonical derived comparison of moduleEvaluationForgetIso.
5. lem-weil-pbc-module-abelian-derived-direct-image-comparison gives the fixed
   unit-compatible comparison on D+. The explicit constant-ring equivalence
   lem-weil-pbc-etale-constant-ring-module-equivalence keeps abelian presheaves
   unchanged and identifies direct image sectionwise, including its scalar
   action through the constant-ring map. It is exact and preserves injectives,
   so its termwise application identifies the direct-image resolution complexes.
6. Apply degree-q cohomology to the D+ comparison at F[0]. Exact forgetting
   commutes with this cohomology, giving the higher direct-image comparison,
   including q = 0. No preservation of injectives by forgetting is needed. -/
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
  sorry

end AlgebraicGeometry.Etale
