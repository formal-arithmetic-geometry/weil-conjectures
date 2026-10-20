/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Sheaf.CategoryTheory.SiteConstantModuleHom
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.ConstructibleSheaf.Defs
public import Sheaf.Paper.SfDerivedComplete

/-! # Derived completeness of a completed integral etale line

Source: Bhatt--Scholze, Lemma 6.8.2(1), Proposition 6.8.4(1), and Section 3.5
(blueprint: lem-fd-etale-integral-line-derived-complete).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Completed scalar extension of an etale integral local system of rank one is
complete for its canonical derived quotient tower.

Source: Bhatt--Scholze, Lemma 6.8.2(1), Proposition 6.8.4(1), and Section 3.5
(blueprint: lem-fd-etale-integral-line-derived-complete).

Proof: choose an etale cover trivializing H as the constant free rank-one module.
The etale-to-pro-etale comparison and the equivalence between fixed-ring sheaves
and constant-ring module sheaves carry this to the constant regular module on the
same cover. Ordinary scalar extension takes that module to the completed regular
module. Slice restriction commutes with these operations and their canonical units.
On each chart the module is flat, so every derived quotient is the ordinary regular
quotient in degree zero. The quotient maps are locally surjective and their inverse
limit is the completed ring by Lemma 6.8.2(1). The surjective-tower derived-limit
lemma gives the augmented Roos triangle with the actual quotient projections.
These projections are the derived scalar-extension units under the tensor/restriction
adjunction. Restriction to a site slice is exact and preserves products, so the
comparison with this Roos triangle can be checked on the trivializing cover. Its
cone vanishes there and hence vanishes globally by the sheaf axiom. This gives the
required triangle with the canonical global units. The empty scheme and trivial
local system are included; no dimension or invertibility condition on X is needed. -/
theorem etaleIntegralLine_derivedComplete
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
    IsSfDerivedComplete l E X ((DerivedCategory.singleFunctor _ 0).obj M) := by
  sorry

end WeilConjectures
