/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.CategoryTheory.SiteConstantModuleHomSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTowerSupplement
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModels
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.CompletedConstantSheafReductionSupplement

/-! # Finite derived reductions of a completed integral etale line

Source: Bhatt--Scholze, Proposition 6.8.4(1), Corollary 5.1.5, and Section 6.5
(blueprint: lem-fd-etale-integral-line-reductions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- All positive derived reductions of a completed etale integral rank-one local
system are constructible and have the common cohomological support interval [0,0].

Source: Bhatt--Scholze, Proposition 6.8.4(1), Corollary 5.1.5, and Section 6.5
(blueprint: lem-fd-etale-integral-line-reductions).

Proof: choose an etale cover on which H is the constant regular integral module.
Comparison inverse image and the fixed-ring/constant-ring equivalence preserve this
trivialization; completed scalar extension gives the completed regular module there.
Tensoring with this local rank-one module is exact, as can be checked on that cover.
It is therefore K-flat in degree zero. Derived reduction is ordinary quotient scalar
extension. Associativity of scalar extension and the projection from the completion
to its quotient identify this quotient with the pro-etale realization of the etale
local system H tensor O_E/(pi^(n+1)); these comparisons agree on overlaps because
they are induced by the original scalar maps. This finite-level system is locally
the regular quotient module, a finite set since O_E is a DVR with finite residue
field. Its pro-etale module sheaf is finite locally constant, hence constructible
on the single stratum X. Its single complex has zero homology outside degree zero
and that finite locally constant sheaf as H^0. The zero sheaves are constructible,
and the cohomological support is contained in {0} = [0,0], independently of n.
The empty scheme, arbitrary ramification, and the trivial local system are allowed. -/
theorem etaleIntegralLine_reductions
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (H : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))))
    (_hH : ∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage X, ∀ i : 𝒰.I₀,
      Nonempty ((Etale.upperStar (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) (𝒰.f i)).obj H ≅
        (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).obj
            (ModuleCat.of _ (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))))) :
    let M : scalarReductionSource l E X :=
      SheafOfModules.changeOfRingsOfUniverses
        (R₁ := (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj
          (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))))
        (R₂ := completedIntegralCommRingSheafUnrestricted l E X)
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).preimage
            (integralConstantToCompletionOfUniverses l E X))
        ((SheafOfModules.restrictScalars
          (constantModuleHomRingIso (ProEt.topology X)
            (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))).inv).obj
          ((PresheafOfModules.sheafification
            (toSheafify (ProEt.topology X)
              ((Functor.const X.ProEtᵒᵖ).obj
                (RingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))))).obj
            ((ProEtale.finiteCoefficientModulePresheaf X.ProEt
              (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))).obj
              ((ProEtale.comparisonUpperStar _ X).obj H).obj)))
    ∀ n : ℕ,
      intrinsicFiniteTorsionConstructible l E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) X
          ((scalarReductionDerivedExtension.{u, u} l E X n).obj
            ((DerivedCategory.singleFunctor _ 0).obj M)) ∧
        proEtaleCohomologicalSupport
          (Y := X) (A := Padic.coefficientExtensionRing l E (n + 1))
          ((scalarReductionDerivedExtension.{u, u} l E X n).obj
            ((DerivedCategory.singleFunctor _ 0).obj M)) ⊆ Set.Icc 0 0 := by
  sorry

end WeilConjectures
