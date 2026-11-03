/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonDerived
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

import WeilConjectures.AlgebraicGeometry.Finite.FiniteClassicalUnboundedComparison

set_option autoImplicit false

/-!
# The unbounded unit for finite coefficients

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-proetale-coefficients/sec-pe-unbounded/
`sk-prop-pe-unbounded-classical/sk-prop-pe-unbounded-classical-unit.md`
(blueprint: det-pe-unbounded-classical-unit).

The theorem states that the canonical unbounded derived adjunction between the
finite-coefficient étale and pro-étale module categories has invertible unit on
every object. Its consequences are full faithfulness of the comparison functor and
preservation of arbitrary direct sums.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- For a finite or algebraically closed field and a finite primary coefficient ring,
the unbounded derived unit from étale to pro-étale coefficients is invertible on every
complex. Consequently the comparison is fully faithful and preserves arbitrary direct
sums. Source: blueprint, `sk-prop-pe-unbounded-classical/sk-prop-pe-unbounded-classical-unit.md`
(blueprint: det-pe-unbounded-classical-unit).

Proof:
1. Apply the proved finite-coefficient unbounded classical comparison. Exact inverse
   image has classical cohomology, and the actual unbounded counit is invertible on
   these classical objects. That comparison includes the affine cohomological bound,
   fixed-degree truncation, and sheafification argument.
2. The left triangle identity identifies inverse image of the unit with the inverse
   of this counit. Exact inverse image commutes with cohomology, and its fully faithful
   functor on module sheaves reflects isomorphisms. Thus the unit is invertible.
3. The unit criterion gives full faithfulness for fixed-ring module sheaves. Compose
   with the exact coefficient-realization equivalence on derived categories to obtain
   full faithfulness in the displayed ringed-module encoding. Its canonical derived
   adjunction therefore also has invertible unit.
4. This canonical unbounded adjunction makes inverse image a left adjoint, so it
   preserves colimits of every discrete shape, including the empty one.
-/
theorem unboundedClassicalUnit
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : IsUnit (algebraMap ℤ k (ℓ : ℤ)))
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    (hA : ∃ n : ℕ, (ℓ : A) ^ n = 0)
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))] :
    (∀ K : FiniteCoefficientEtaleDerivedCategory X A,
      IsIso
        (((finiteCoefficientComparisonAdjunction X A).mapDerivedCategoryRightDerivedAdjunction
          |>.unit.app K))) ∧
      Nonempty (finiteCoefficientDerivedComparison X A).FullyFaithful ∧
      ∀ (I : Type v),
        Nonempty (PreservesColimitsOfShape (Discrete I)
          (finiteCoefficientDerivedComparison X A)) := by
  let L := comparisonUpperStar (ModuleCat.{u + 1} A) X
  let E := finiteCoefficientRealization X A
  let adj := (comparisonAdjunction (ModuleCat.{u + 1} A) X)
    |>.mapDerivedCategoryRightDerivedAdjunction
  obtain ⟨n, hn⟩ := hA
  have hA' : ∃ r : ℕ, 1 ≤ r ∧ (ℓ : A) ^ r = 0 :=
    ⟨n + 1, by omega, by rw [pow_succ, hn, zero_mul]⟩
  obtain ⟨himage, hcounit, _⟩ :=
    finiteClassicalUnboundedComparison k hbase ℓ hℓ A hA' X
  have hu (K : FiniteCoefficientEtaleDerivedCategory X A) :
      IsIso (adj.unit.app K) := by
    have : IsIso (adj.counit.app (L.mapDerivedCategory.obj K)) :=
      hcounit _ (himage K)
    have hm : IsIso (L.mapDerivedCategory.map (adj.unit.app K)) :=
      isIso_of_comp_hom_eq_id _ (adj.left_triangle_components K)
    rw [DerivedCategory.isIso_iff]
    intro q
    have hm' : IsIso ((DerivedCategory.homologyFunctor _ q).map
        (L.mapDerivedCategory.map (adj.unit.app K))) := inferInstance
    have : IsIso (L.map ((DerivedCategory.homologyFunctor _ q).map
        (adj.unit.app K))) :=
      (NatIso.isIso_map_iff (L.mapDerivedCategoryHomologyFunctorIso q) _).mpr hm'
    exact isIso_of_reflects_iso _ L
  have : IsIso adj.unit := NatIso.isIso_of_isIso_app _
  let fL := adj.fullyFaithfulLOfIsIsoUnit
  have : L.mapDerivedCategory.Full := fL.full
  have : L.mapDerivedCategory.Faithful := fL.faithful
  let f := (Functor.FullyFaithful.ofFullyFaithful
    (L.mapDerivedCategory ⋙ E.mapDerivedCategory)).ofIso
      (Functor.mapDerivedCategoryCompIso L E).symm
  have : (finiteCoefficientComparison X A).mapDerivedCategory.Full := f.full
  have : (finiteCoefficientComparison X A).mapDerivedCategory.Faithful := f.faithful
  let a := (finiteCoefficientComparisonAdjunction X A)
    |>.mapDerivedCategoryRightDerivedAdjunction
  refine ⟨fun K ↦ inferInstance, ⟨f⟩, fun I ↦ ?_⟩
  exact ⟨a.leftAdjoint_preservesColimits.preservesColimitsOfShape⟩

end AlgebraicGeometry.ProEtale
