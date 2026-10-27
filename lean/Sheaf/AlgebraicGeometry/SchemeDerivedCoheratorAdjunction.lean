/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.QuasiCoherentGrothendieckGenerators
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# The derived coherator on an arbitrary scheme

Source: Stacks Project, Properties, Tag 077P (2); Derived Categories of Schemes,
Tag 08D6, opening paragraphs (blueprint: lem-sfb-scheme-derived-coherator-adjunction).

The structure below packages the objects and all clauses of the existence theorem.
It uses the existing full quasi-coherent subcategory and the recorded total right
derived functor, rather than a new category or a second derived-functor construction.
Its shift comparison is normalized by the canonical derived unit: that unit must
commute with the termwise shifts. This characterizes the canonical comparison on
K-injective representatives, rather than choosing arbitrary adjoint-induced shifts.
-/

@[expose] public section

set_option autoImplicit false

universe u w uA vA uM vM

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The underived and unbounded derived coherator adjunctions, including the
canonical shift comparisons and their chain-map normalization.

Source: Stacks Project, Tags 077P (2), 08D6, 09T5 and 0A8D
(blueprint: lem-sfb-scheme-derived-coherator-adjunction).
The abelian and derived-category structures are conclusions in this package.
The ambient module category uses its existing Mathlib abelian structure. -/
structure DerivedCoheratorAdjunctionData
    {A : Type uA} [Category.{vA} A] {M : Type uM} [Category.{vM} M]
    [Abelian M] [HasDerivedCategory.{w} M] (i : A ⥤ M) where
  /-- The induced abelian structure on the domain of the inclusion. -/
  [abelian : Abelian A]
  /-- Its unbounded derived category, in the always available localization universe. -/
  [derivedCategory : HasDerivedCategory.{max uA vA} A]
  /-- The inclusion uses the inherited addition on morphisms. -/
  [inclusionAdditive : i.Additive]
  /-- Exactness of the inclusion, on the left. -/
  [inclusionFiniteLimits : PreservesFiniteLimits i]
  /-- Exactness of the inclusion, on the right. -/
  [inclusionFiniteColimits : PreservesFiniteColimits i]
  /-- Every ambient complex has an unbounded K-injective resolution. -/
  resolutions : ∀ K : CochainComplex M ℤ,
    ∃ (J : CochainComplex M ℤ) (s : K ⟶ J),
      J.IsKInjective ∧ QuasiIso s
  /-- The ordinary coherator. -/
  coherator : M ⥤ A
  /-- Additivity of the coherator. -/
  [additive : coherator.Additive]
  /-- Left exactness of the coherator. -/
  [leftExact : PreservesFiniteLimits coherator]
  /-- The ordinary inclusion-coherator adjunction. -/
  adjunction : i ⊣ coherator
  /-- Integer-shift comparisons for the recorded total right derived functor. -/
  [shift : (coherator.rightDerivedFunctorOfQuasiIsoResolutions resolutions).CommShift ℤ]
  /-- Canonical normalization of these comparisons by the right-derived unit. -/
  canonicalShift : NatTrans.CommShift
    (coherator.rightDerivedFunctorOfQuasiIsoResolutionsUnit resolutions) ℤ
  /-- The derived coherator is triangulated with those same comparisons. -/
  [triangulated :
    (coherator.rightDerivedFunctorOfQuasiIsoResolutions resolutions).IsTriangulated]
  /-- Its left adjoint is precisely the termwise derived inclusion. -/
  derivedAdjunction : i.mapDerivedCategory ⊣
    coherator.rightDerivedFunctorOfQuasiIsoResolutions resolutions
  /-- The actual unit and counit commute with the specified shift comparisons. -/
  compatible : derivedAdjunction.CommShift ℤ
  /-- On a chain map into a K-injective, the Hom bijection is its ordinary
  termwise adjunct, followed by the canonical K-injective comparison. -/
  normalization : ∀
    (B : CochainComplex A ℤ)
    (J : CochainComplex M ℤ) [J.IsKInjective]
    (f : (i.mapHomologicalComplex (ComplexShape.up ℤ)).obj B ⟶ J),
    derivedAdjunction.homEquiv (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj J)
      (i.mapDerivedCategoryFactors.hom.app B ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map
        ((adjunction.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv B J f) ≫
      (DerivedCategory.quotientCompQhIso _).inv.app
        ((coherator.mapHomologicalComplex (ComplexShape.up ℤ)).obj J) ≫
      DerivedCategory.Qh.map
        ((coherator.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app J) ≫
      (coherator.rightDerivedFunctorOfQuasiIsoResolutionsUnit resolutions).app
        ((HomotopyCategory.quotient M (ComplexShape.up ℤ)).obj J) ≫
      (coherator.rightDerivedFunctorOfQuasiIsoResolutions resolutions).map
        ((DerivedCategory.quotientCompQhIso M).hom.app J)

/-- Every scheme has the coherator and its normalized triangulated derived adjunction.

Source: Stacks Project, Tags 077P (2) and 08D6
(blueprint: lem-sfb-scheme-derived-coherator-adjunction).

Proof:
1. By `lem-sfb-qcoh-grothendieck-generators`, the full quasi-coherent category is
   Grothendieck abelian and its inclusion is exact and preserves small colimits.
   Apply `lem-sfb-grothendieck-colimit-functor-right-adjoint` to this inclusion,
   obtaining the underived coherator adjunction, without any finiteness hypothesis.
2. By `lem-weil-pbc-right-adjoint-preserves-limits`, the coherator is left exact.
   A right adjoint between additive categories preserves zero and finite products,
   hence biproducts, their diagonals and codiagonals, and therefore sums of maps.
3. The ambient module category is Grothendieck abelian by
   `lem-pc-scheme-modules-grothendieck-abelian`; `lem-sfb-grothendieck-k-injective`
   gives unbounded resolutions. Apply `lem-weil-pbc-kinjective-total-derived` to
   the coherator's homotopy functor followed by localization. It is triangulated by
   `lem-trf-additive-homotopy-triangulated` and
   `lem-pur-homotopy-category-triangulated`. The recorded
   `def-sfb-right-derived-functor` supplies the universal derived pair and its
   invertible comparison on K-injectives. The exact inclusion is derived termwise
   by `lem-weil-pbc-exact-functor-derived-factorization`.
4. The coherator preserves K-injectives by
   `lem-weil-pbc-right-adjoint-preserves-kinjective`. Apply
   `lem-weil-pbc-kinjective-hom-derived` on both sides of the termwise adjunction
   `lem-weil-pbc-termwise-adjunction-homotopy`. The resulting natural Hom bijections
   give the displayed derived adjunction and exactly its chain-map normalization.
5. On K-injectives the derived unit is invertible, so transporting the termwise
   shift comparison through it gives the canonical shift comparison; resolutions
   extend it to all objects. `lem-sp-canonical-right-derived-adjunction-shift`,
   transported along the unique unit-compatible isomorphism of right-derived pairs,
   gives compatibility of the actual adjunction unit and counit with these shifts.
   Finally `lem-sf-triangulated-right-adjoint` proves that the derived coherator is
   triangulated with these same comparisons. The derived inclusion is already
   triangulated by the exact-functor factorization. -/
theorem exists_schemeDerivedCoheratorAdjunction (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)] :
    Nonempty (DerivedCoheratorAdjunctionData
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
