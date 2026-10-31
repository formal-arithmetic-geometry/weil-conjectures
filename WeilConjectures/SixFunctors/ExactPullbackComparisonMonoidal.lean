/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedPullbackTensorComparison
public import WeilConjectures.AlgebraicGeometry.ModuleDerivedFunctorCompositorShifts
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedExactComparison
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedTotalTensor
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.AlgebraicGeometry.IntegralResidueOrdinaryMonoidal
import WeilConjectures.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-! # Monoidality of the canonical exact pullback comparison

Source: latest blueprint, sec-six-functors/sk-thm-sf-identification/def-sf-cup.md,
final associativity and unit sentence, via the open factor of the compactification
projection; Stacks Tags 015F (dual) and 03EL
(blueprint: lem-sf-exact-pullback-comparison-monoidal).

The derived categories are unbounded categories of internal modules over the pulled-back
commutative condensed ring. All tensor products are the existing relative derived tensors.

## Main definitions and statements

* `supportPullbackExactComparison`: the canonical exact comparison followed by the
  localized inverse-coefficient identification.
* `supportPullbackDerivedUnitIso`: exact factorization followed by the ordinary unit
  comparison in degree zero.
* `exact_pullback_comparison_monoidal`: tensor and unit compatibility, and the resulting
  strong monoidal structure with the specified tensorator and unit.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The canonical exact comparison with inverse-coefficient termwise pullback. The second
factor localizes the inverse of the recorded identification `supportPullback ≅ upperStar`.
Source: Stacks Tag 015F (dual), and Tag 03EL for coefficient transport
(blueprint: lem-sf-exact-pullback-comparison-monoidal). -/
def supportPullbackExactComparison :
    moduleObjectDerivedPullback Λ f ≅ (supportPullback Λ f).mapDerivedCategory :=
  modulePullbackExactComparison Λ f ≪≫
    (Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ f)).symm

/-- The specified unit isomorphism of exact termwise pullback: the exact factorization
on the degree-zero unit complex, followed by localization of the ordinary unit map.
The ordinary map uses the canonical inverse-coefficient identification with upper star
and its published unit comparison. No derived monoidal structure is selected here.
Source: Stacks Tag 03EL and the exact-functor clause of the latest blueprint
`det-def-sfb-derived-categories.md`
(blueprint: lem-sf-exact-pullback-comparison-monoidal). -/
def supportPullbackDerivedUnitIso :
    (supportPullback Λ f).mapDerivedCategory.obj
      (𝟙_ (DerivedCategory (supportModules Λ Y))) ≅
        𝟙_ (DerivedCategory (supportModules Λ X)) :=
  (supportPullback Λ f).mapDerivedCategoryFactors.app (𝟙_ _) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (supportPullback Λ f)
          (ComplexShape.up ℤ) 0).app (𝟙_ _) ≪≫
        (HomologicalComplex.single _ _ 0).mapIso
          ((supportPullbackIsoUpperStar Λ f).app (𝟙_ _) ≪≫
            (Functor.Monoidal.εIso (upperStar Λ f)).symm))

/-- The canonical exact comparison respects the specified derived tensor and unit maps.
The inverse comparison family and inverse unit give a strong monoidal structure on the
termwise derived functor, and the canonical comparison is a monoidal natural isomorphism.
No boundedness, flatness or finiteness assumption is made.
Source: latest blueprint `def-sf-cup.md`, final associativity and unit sentence,
via Step 2 of `lem-sf-compact-projection-right-tensor-action`; Stacks Tags 015F and 03EL
(blueprint: lem-sf-exact-pullback-comparison-monoidal).

Proof:
1. By the universal left-derived property (`def-sfb-left-derived-functor`) and exact
factorization (`lem-weil-pbc-exact-functor-derived-factorization`), the specified exact
comparison is the unique counit-compatible isomorphism
(`lem-sfb-right-kan-extension-unique-iso`, `def-sfb-left-derived-exact`). Thus fac c = gamma.
2. The coefficient identification is monoidal: the ordinary structure is transported from
inverse-coefficient restriction (`new-integral-residue-ordinary-monoidal`), whose balanced
presentation determines the ordinary comparison in
`def-sfb-condensed-pullback-tensor-comparison`. The localization universal property
(`lem-weil-pbc-localization-universal-property`) makes its localization compatible with the
exact factorizations, so fac c = gamma still holds after this identification.
3. The summand normalization of `lem-sfb-termwise-strong-monoidal` identifies the ordinary
complex comparison with the inverse total tensorator. Pass to homotopy classes using
`lem-sfb-total-tensor-homotopy`. The two-counit equation of
`new-proetale-derived-module-pullback-monoidal`, postcomposed with that inverse, reads
mu (gamma tensor gamma) delta = Q(d) gamma E(mu).
4. Conjugate delta by c. Using fac c = gamma and naturality of c for mu, the conjugate
satisfies precisely the representative normalization of
`def-sfb-condensed-pullback-tensor-comparison`. Its uniqueness identifies it with the
specified derived comparison. Rearrangement gives the tensor equation on every pair.
5. The derived unit of `lem-sfb-derived-pullback-strong-monoidal` is Q(j) gamma on the
unit complex, while the specified termwise unit is Q(j) fac. The counit equation therefore
gives unit compatibility, with the actual degree-zero ordinary unit j.
6. Substitute the tensor and unit equations into the associativity and two unit laws
of `lem-sfb-derived-pullback-strong-monoidal`. Naturality of c, associators and unitors
cancels the inverse c pairs. This yields `def-sfb-strong-monoidal-functor` for the
prescribed inverse comparisons. The same equations give monoidality of c. All arguments
use arbitrary complexes and arbitrary scheme morphisms and condensed coefficients. -/
theorem exact_pullback_comparison_monoidal :
    (∀ M N : DerivedCategory (supportModules Λ Y),
      (supportPullbackExactComparison Λ f).hom.app (M ⊗ N) ≫
          (supportDerivedTensorComparison Λ f M N).hom =
        (((leftDerivedUpperStarTensorIso Λ f).app M).app N).hom ≫
          ((supportPullbackExactComparison Λ f).hom.app M ⊗ₘ
            (supportPullbackExactComparison Λ f).hom.app N)) ∧
    ((supportPullbackExactComparison Λ f).hom.app
        (𝟙_ (DerivedCategory (supportModules Λ Y))) ≫
      (supportPullbackDerivedUnitIso Λ f).hom = (leftDerivedUpperStarUnitIso Λ f).hom) ∧
    ∃ m : (supportPullback Λ f).mapDerivedCategory.CoreMonoidal,
      (∀ M N : DerivedCategory (supportModules Λ Y),
        m.μIso M N = (supportDerivedTensorComparison Λ f M N).symm) ∧
      m.εIso = (supportPullbackDerivedUnitIso Λ f).symm ∧
      @NatTrans.IsMonoidal _ _ _ _ _ _ _ _
        (supportPullbackExactComparison Λ f).hom
        (monoidal_leftDerivedUpperStar Λ f).toLaxMonoidal m.toLaxMonoidal := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
