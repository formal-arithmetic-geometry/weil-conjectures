/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientHomZeroClass
public import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
public import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteZerothHypercohomologyOfUniverses
import WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses

/-! # Cycle-normalized H-zero Hom identification equals the closed transpose

Source: Stacks Project, `sites-cohomology.tex`, Tag 08JA, lemma-section-RHom-over-U,
and the agent-derived compatibility with the normalized tensor-Hom model
(blueprint: lem-coef-hom-zero-closed-transpose-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v u w a b

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace WeilConjectures

/-- The unit-source internal Hom isomorphism `j_B`. Uniqueness of right adjoints
compares `H(1,-)` with the identity, both right adjoint to right tensor by the unit.
Its forward map is evaluation after the inverse right unitor; its inverse is the
closed transpose of the right unitor. This uses Mathlib's actual adjunction isomorphism.
Source: the unit-adjunction calculation in the statement of
lem-coef-hom-zero-closed-transpose-compatibility (blueprint:
lem-coef-hom-zero-closed-transpose-compatibility). -/
def coefficientClosedUnitHomIso {D : Type a} [Category.{b} D]
    {H : Dᵒᵖ × D ⥤ D} (S : CoefficientClosedStructure H) (B : D) :
    H.obj (op S.monoidal.tensorUnit, B) ≅ B :=
  letI := S.monoidal
  (Adjunction.rightAdjointUniq (S.adjunction (𝟙_ D))
    (Adjunction.id.ofNatIsoLeft (rightUnitorNatIso D).symm)).app B

/-- The additive unit-source identification `iota_B = theta_(1,B) ∘ h^0(j_B⁻¹)`.
Both factors are the existing fixed comparison or the functorial image of an actual
isomorphism; no section functor or comparison is reselected.
Source: the displayed definition of iota in
lem-coef-hom-zero-closed-transpose-compatibility
(blueprint: lem-coef-hom-zero-closed-transpose-compatibility). -/
def coefficientHomZeroUnitEquiv
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    (A : Sheaf J CommRingCat.{max c v u})
    [HasDerivedCategory.{w} (RingedDerivedNative.Modules.{c, v, u} J A)]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A))
    (B : DerivedCategory (RingedDerivedNative.Modules.{c, v, u} J A)) :
    (ringedSiteZerothHypercohomologyOfUniverses.{c, v, u, w} J A).obj B ≃+
      (S.monoidal.tensorUnit ⟶ B) :=
  ((ringedSiteZerothHypercohomologyOfUniverses.{c, v, u, w} J A).mapIso
    (coefficientClosedUnitHomIso S B).symm).addCommGroupIsoToAddEquiv.trans
      (coefficientHomZeroEquiv.{u, c, v, w} J A S.monoidal.tensorUnit B)

end WeilConjectures
