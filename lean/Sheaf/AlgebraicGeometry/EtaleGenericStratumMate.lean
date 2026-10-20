/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q106
-/
module

public import Sheaf.AlgebraicGeometry.EtaleGenericImmersionProjection
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-! # The evaluation-normalized internal-Hom formula for an immersion

Source: Stacks Project, Tags 08J9, 07A6 and 08FJ; blueprint
sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation/lem-weil-stratum-ambient-hom
(blueprint: lem-sf-etale-generic-stratum-mate).

All categories below are ordinary unbounded derived categories of constant-coefficient
etale module sheaves. The internal Hom is the existing closed internal Hom `derivedHom`;
its tensor product is the existing K-flat derived tensor `derivedTensor`.
-/

@[expose] public section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The exceptional inverse image `Ri^! j^*` for the specified closed-then-open factorization.
Source: blueprint lem-weil-stratum-ambient-hom and Stacks Tag 08FJ
(blueprint: lem-sf-etale-generic-stratum-mate). -/
noncomputable def immersionUpperShriek
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} (i : S ⟶ U) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] :
    DerivedCategoryModule A X ⥤ DerivedCategoryModule A S :=
  D((j)^*[ModuleCat.{u + 1} A]) ⋙ (R((i)_*[ModuleCat.{u + 1} A])).rightAdjoint

/-- The composite closed/open adjunction, retaining its actual unit and counit.
Source: blueprint lem-weil-stratum-ambient-hom and Stacks Tags 07A6, 08FJ
(blueprint: lem-sf-etale-generic-stratum-mate). -/
noncomputable def immersionLowerUpperShriekAdjunction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} (i : S ⟶ U) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] :
    immersionLowerShriek A i j ⊣ immersionUpperShriek A i j :=
  (Adjunction.ofIsLeftAdjoint (R((i)_*[ModuleCat.{u + 1} A]))).comp
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)

/-- Right-ordered evaluation `RHom(P,M) ⊗ᴸ P ⟶ M`, obtained from the existing
left-tensor evaluation by the canonical signed symmetry. Source: Stacks Tag 08J9
(blueprint: lem-sf-etale-generic-stratum-mate). -/
noncomputable def immersionHomEvaluation
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (P M : DerivedCategoryModule A T) :
    ((derivedTensor (ModuleCat.{u + 1} A) T).obj
      (((derivedHom (ModuleCat.{u + 1} A) T).obj (op P)).obj M)).obj P ⟶ M :=
  ((derivedTensorSymmetry (ModuleCat.{u + 1} A) T).hom.app
      (((derivedHom (ModuleCat.{u + 1} A) T).obj (op P)).obj M)).app P ≫
    (derivedTensorHomAdjunction (ModuleCat.{u + 1} A) P).counit.app M

/-- There is a natural internal-Hom isomorphism for an immersion, characterized by
its tensor transpose for every test object and every map into ordinary direct image.
Source: Stacks Tags 08J9, 07A6, 08FJ and blueprint lem-weil-stratum-ambient-hom
(blueprint: lem-sf-etale-generic-stratum-mate).

Proof plan:
1. The exact constant-coefficient inverse image and ordinary derived direct image form
an adjunction, computed on K-injectives. Use prop-weil-pbc-inverse-image-modules-exact,
prop-weil-pbc-kinjective-resolutions-exist, lem-weil-pbc-right-adjoint-preserves-kinjective,
lem-weil-pbc-kinjective-hom-derived, lem-weil-pbc-kinjective-total-derived and
lem-weil-pbc-termwise-adjunction-homotopy. The exact open adjunction descends termwise;
compose it with lem-exc-closed-ambient to obtain the specified shriek adjunction.
2. For each C, tensor-Hom adjunction (lem-sf-ringed-derived-closed-symmetric-monoidal),
the canonical immersion projection (lem-sf-etale-generic-immersion-projection), the shriek
adjunction, tensor-Hom adjunction on S, and inverse/direct-image adjunction give a
bijection Hom(C,RHom(Rs!P,M)) = Hom(C,Rs*RHom(P,Rs!M)), natural in C, P and M.
3. Yoneda yields the natural isomorphism. Tracing the inverse bijection sends a map u
to projection, Rs! of its adjoint tensor identity, Rs! evaluation, then the shriek counit.
4. The closed adjunction's counit is evaluation. Moving its left tensor factor to the
right uses exactly the signed symmetry in immersionHomEvaluation. This gives the
stated equality. No boundedness or constructibility enters any of these steps. -/
theorem immersionInternalHomIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} (i : S ⟶ U) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] :
    ∃ θ : (immersionLowerShriek A i j).op.prod (𝟭 (DerivedCategoryModule A X)) ⋙
        Functor.uncurry.obj (derivedHom (ModuleCat.{u + 1} A) X) ≅
      (𝟭 (DerivedCategoryModule A S)ᵒᵖ).prod (immersionUpperShriek A i j) ⋙
        Functor.uncurry.obj (derivedHom (ModuleCat.{u + 1} A) S) ⋙
          R((i ≫ j)_*[ModuleCat.{u + 1} A]),
      ∀ (P : DerivedCategoryModule A S) (M C : DerivedCategoryModule A X)
        (f : C ⟶ (R((i ≫ j)_*[ModuleCat.{u + 1} A])).obj
          (((derivedHom (ModuleCat.{u + 1} A) S).obj (op P)).obj
            ((immersionUpperShriek A i j).obj M))),
        derivedTensorHom (ModuleCat.{u + 1} A) (f ≫ θ.inv.app (op P, M))
            (𝟙 ((immersionLowerShriek A i j).obj P)) ≫
          immersionHomEvaluation A X ((immersionLowerShriek A i j).obj P) M =
        immersionProjectionMap A i j C P ≫
          (immersionLowerShriek A i j).map
            (derivedTensorHom (ModuleCat.{u + 1} A)
              (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
                (i ≫ j)).homEquiv C
                  (((derivedHom (ModuleCat.{u + 1} A) S).obj (op P)).obj
                    ((immersionUpperShriek A i j).obj M))).symm f) (𝟙 P)) ≫
          (immersionLowerShriek A i j).map
            (immersionHomEvaluation A S P ((immersionUpperShriek A i j).obj M)) ≫
          (immersionLowerUpperShriekAdjunction A i j).counit.app M := by
  sorry

end AlgebraicGeometry.Etale
