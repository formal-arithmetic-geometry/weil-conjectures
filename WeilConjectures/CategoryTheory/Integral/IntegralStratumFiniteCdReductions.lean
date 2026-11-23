/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientCoefficients
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.CategoryTheory.Integral.IntegralStratumFiniteCdReductionsSupportWindow
import WeilConjectures.CategoryTheory.Integral.IntegralStratumFiniteCdReductionsAssembly
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import Mathlib.CategoryTheory.HomCongr

/-!
# Integral stratum finite-reduction bound

The bound is stated with explicit finite upper bounds on the two classical
cohomological dimensions. Positive quotient exponents are indexed by `n + 1`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace CategoryTheory

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory

private theorem stratum_hom_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Z S V : Scheme.{u}} (i : Z ⟶ X) (v : S ⟶ Z) (j : V ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion v] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (B : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (r : ℤ)
    (h : Subsingleton ((DerivedCategory.singleFunctor _ 0).obj L ⟶
      ((CondensedRing.upperStar Λ v).mapDerivedCategory.obj
        ((CondensedRing.closedSupport Λ i j).rightDerivedFunctor.obj B))⟦r⟧))
    (f : (DerivedCategory.singleFunctor _ 0).obj
      ((CondensedRing.lowerStar Λ i).obj
        ((CondensedRing.openImmersionLowerShriek Λ v).obj L)) ⟶ B⟦r⟧) :
    f = 0 := by
  let := CondensedRing.closedSupport_lowerStarExact Λ i j hij
  let R := (CondensedRing.closedSupport Λ i j).rightDerivedFunctor
  let U := (CondensedRing.upperStar Λ v).mapDerivedCategory
  let A := (CondensedRing.openImmersionLowerShriek Λ v).obj L
  let AZ := (DerivedCategory.singleFunctor _ 0).obj A
  let LS := (DerivedCategory.singleFunctor _ 0).obj L
  let eI := ((CondensedRing.lowerStar Λ i).mapDerivedCategorySingleFunctor 0).app A
  let eV := ((CondensedRing.openImmersionLowerShriek Λ v).mapDerivedCategorySingleFunctor 0).app L
  let ai := CondensedRing.closedSupportDerivedAdjunction Λ i j hij
  let av := Adjunction.mapDerivedCategoryAdjunction
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ v)
  let e₁ := Iso.homCongr eI.symm (Iso.refl (B⟦r⟧))
  let e₂ := ai.homEquiv AZ (B⟦r⟧)
  let e₃ := Iso.homCongr eV.symm ((R.commShiftIso r).app B)
  let e₄ := av.homEquiv LS ((R.obj B)⟦r⟧)
  let e₅ := Iso.homCongr (Iso.refl LS) ((U.commShiftIso r).app (R.obj B))
  let e := (((e₁.trans e₂).trans e₃).trans e₄).trans e₅
  exact e.injective (h.elim (e f) (e 0))

/-- The integral stratum finite-reduction bound, uniform in the constructible target
and in the positive quotient exponent. Both local scalar models allow torsion. -/
theorem integralStratumFiniteCdReductions
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Algebra E (PadicAlgCl l)] [IsScalarTower (Padic l) E (PadicAlgCl l)]
    (X Z S V : Scheme.{u}) [IsNoetherian X]
    (hl : IsUnit (l : Γ(X, ⊤)))
    (i : Z ⟶ X) (v : S ⟶ Z) (j : V ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion v] [IsOpenImmersion j] [QuasiCompact j]
    (hcomp : Set.range j.base = (Set.range i.base)ᶜ) :
    letI : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType i
    letI : IsNoetherian S := isNoetherian_of_locallyOfFiniteType v
    ∀ (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj (IntegralQuotient.integral l E) S)),
      HasFiniteConstantLocalModel (IntegralQuotient.integral l E) S L →
    ∀ (c s : ℕ),
      relativeCohomologicalDimension l (Fact.out : l.Prime) j ≤ c →
      cohomologicalDimension l (Fact.out : l.Prime) S ≤ s →
    ∀ (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (IntegralQuotient.integral l E) X)),
      IsConstantModelConstructible (IntegralQuotient.integral l E) X N →
    ∀ (n : ℕ) (r : ℤ), (c : ℤ) + (s : ℤ) + 2 < r →
      ∀ f : (DerivedCategory.singleFunctor _ 0).obj
          ((CondensedRing.lowerStar (IntegralQuotient.integral l E) i).obj
            ((CondensedRing.openImmersionLowerShriek (IntegralQuotient.integral l E) v).obj L)) ⟶
          ((IntegralQuotient.restrict l E X n).obj
            ((IntegralQuotient.scalar l E X n).obj
              ((DerivedCategory.singleFunctor _ 0).obj N)))⟦r⟧,
        f = 0 := by
  intro L hL c s hc hs N hN n r hr f
  let : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType i
  let : IsNoetherian S := isNoetherian_of_locallyOfFiniteType v
  have hij : Set.range i.base = (Set.range j.base)ᶜ := by
    rw [hcomp, compl_compl]
  have hK := integralStratumFiniteCdReductions_support_window l E X Z S V hl i v j
    hcomp c hc N hN n
  apply stratum_hom_zero (IntegralQuotient.integral l E) i v j hij L _ r _ f
  exact integralStratumFiniteCdReductions_assembly l E S L hL s hs _ (-1)
    ((c : ℤ) + 1) (by omega) hK.1 hK.2 r (by omega)

end CategoryTheory
