/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueLiftComparisons
public import WeilConjectures.AlgebraicGeometry.AdicStratifiedPerfectData
public import WeilConjectures.CategoryTheory.ConstantScalarRestrictionTensor

/-! # Explicit etale residue transport through the equivalent small site

## References

* Stacks Project, Tags 03CY and 03A0
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Precomposition with AsSmall.down, with inverse AsSmall.up (Stacks, Tag 03A0). -/
def sfbImmersionEtaleModel (S : Scheme.{u}) (k : Type (u + 1)) [CommRing k] :
    Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} k) ≌
      Sheaf (smallModelComparisonEtaleTopology.{u, 0} S) (ModuleCat.{u + 1} k) :=
  let : (AsSmall.up : S.Etale ⥤ smallModelComparisonEtaleSite.{u, 0} S).IsContinuous
      S.smallEtaleTopology (smallModelComparisonEtaleTopology.{u, 0} S) :=
    inferInstanceAs ((AsSmall.equiv.{u, u + 1, u + 1} (C := S.Etale)).functor.IsContinuous
      S.smallEtaleTopology
      ((AsSmall.equiv.{u, u + 1, u + 1} (C := S.Etale)).inverse.inducedTopology
        S.smallEtaleTopology))
  CategoryTheory.Equivalence.mk
    ((AsSmall.down : smallModelComparisonEtaleSite.{u, 0} S ⥤ S.Etale).sheafPushforwardContinuous
      (ModuleCat.{u + 1} k) (smallModelComparisonEtaleTopology.{u, 0} S)
      S.smallEtaleTopology)
    ((AsSmall.up : S.Etale ⥤ smallModelComparisonEtaleSite.{u, 0} S).sheafPushforwardContinuous
      (ModuleCat.{u + 1} k) S.smallEtaleTopology
      (smallModelComparisonEtaleTopology.{u, 0} S))
    (Iso.refl _) (Iso.refl _)

/-- The inverse of the existing scalar-restriction equivalence, after AsSmall transport.
This is a genuine inverse equivalence, not an arbitrary object chosen from existence
(Stacks, Tags 03CY and 03A0). -/
def sfbEtaleResidueModel (S : Scheme.{u}) (k : Type (u + 1)) [CommRing k] :
    Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} k) ≌
      ConstantCompletion.Mod
        (ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, 0} S) k) :=
  (sfbImmersionEtaleModel S k).trans
    (ConstantScalarRestriction.restriction
      (smallModelComparisonEtaleTopology.{u, 0} S) k).asEquivalence.symm

/-- The exact residue transport before localization (Stacks, Tags 03CY and 03A0). -/
def sfbImmersionResidueFunctor {X S : Scheme.{u}} (i : S ⟶ X)
    (k : Type (u + 1)) [CommRing k] :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k) ⥤
      ConstantCompletion.Mod
        (ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, 0} S) k) :=
  Etale.upperStar.{u + 2, u} (ModuleCat.{u + 1} k) i ⋙
    (sfbEtaleResidueModel S k).functor

/-- The coefficient model equivalence is additive (Stacks, Tags 03CY and 03A0). -/
@[instance] theorem sfbEtaleResidueModel_additive (S : Scheme.{u})
    (k : Type (u + 1)) [CommRing k] : (sfbEtaleResidueModel S k).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Etale inverse image followed by coefficient transport is additive (Stacks, Tags 03CY and 03A0).
-/
@[instance] theorem sfbImmersionResidueFunctor_additive {X S : Scheme.{u}} (i : S ⟶ X)
    (k : Type (u + 1)) [CommRing k] : (sfbImmersionResidueFunctor i k).Additive := by
  unfold sfbImmersionResidueFunctor
  infer_instance

/-- The residue transport preserves finite limits (Stacks, Tags 03CY and 03A0). -/
@[instance] theorem sfbImmersionResidueFunctor_finiteLimits {X S : Scheme.{u}} (i : S ⟶ X)
    (k : Type (u + 1)) [CommRing k] :
    PreservesFiniteLimits (sfbImmersionResidueFunctor i k) := by
  unfold sfbImmersionResidueFunctor
  infer_instance

/-- The residue transport preserves finite colimits (Stacks, Tags 03CY and 03A0). -/
@[instance] theorem sfbImmersionResidueFunctor_finiteColimits {X S : Scheme.{u}} (i : S ⟶ X)
    (k : Type (u + 1)) [CommRing k] :
    PreservesFiniteColimits (sfbImmersionResidueFunctor i k) := by
  unfold sfbImmersionResidueFunctor
  infer_instance

/-- The fixed transported etale residue, using its displayed complex (Stacks, Tags 03CY and 03A0).
-/
def sfbImmersionResidue {X S : Scheme.{u}} (i : S ⟶ X)
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (C : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1)))) ℤ) :
    ConstantCompletion.D
      (ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, 0} S) A I 0) :=
  (ConstantCompletion.Q _).obj
    (((sfbImmersionResidueFunctor i (A ⧸ I ^ (0 + 1))).mapHomologicalComplex (.up ℤ)).obj C)

/-- Exact transport preserves cohomological bounds (Stacks, Tags 03A0 and 03CY). -/
theorem sfbImmersionResidue_bounded {X S : Scheme.{u}} (i : S ⟶ X)
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (C : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1)))) ℤ)
    (a b : ℤ) (h : ∀ q : ℤ, (q < a ∨ b < q) → IsZero (C.homology q)) :
    ∀ q : ℤ, q < a ∨ b < q → IsZero
      ((adicResidueCohomology.{u + 1}
        (ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, 0} S) A I 0)
        q).obj (sfbImmersionResidue i I C)) := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod
    (ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, 0} S) A I 0))
  intro q hq
  let F := sfbImmersionResidueFunctor i (A ⧸ I ^ (0 + 1))
  exact (F.map_isZero (h q hq)).of_iso
    ((DerivedCategory.homologyFunctorFactors _ q).app _ ≪≫
      ((F.mapHomologicalComplexHomologyIso (.up ℤ) q).app C))

end AlgebraicGeometry.Scheme
