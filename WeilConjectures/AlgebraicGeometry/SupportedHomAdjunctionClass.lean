/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SupportedHomAdjunctionTranspose
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedHomPullback

/-! # The class of a supported morphism under the derived adjunction

Source: latest blueprint, `lem-pur-supported-hom.proof.md`, derived closed adjunction
(blueprint: lem-pur-supported-hom-adjunction-class).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

variable (A : Type (u + 1)) [CommRing A] [Finite A]
  {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]

/-- The source comparison in the shifted supported adjunction, with its direction fixed.
Source: the cochain convention in `lem-pur-supported-hom.proof.md`
(blueprint: lem-pur-supported-hom-adjunction-class). -/
def supportedHomAdjunctionSourceIso (a : ℤ) :
    (DerivedCategory.singleFunctor
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) 0).obj
        ((supportedCoefficients A i).obj (ModuleCat.of A A)) ≅
      ((supportedCoefficients A i).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) a).obj
          (ModuleCat.of A A)))⟦a⟧ :=
  ((DerivedCategory.singleFunctors
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))).shiftIso a 0 a
      (add_zero a)).symm.app _ ≪≫
    (shiftFunctor _ a).mapIso
      (((supportedCoefficients A i).mapDerivedCategorySingleFunctor a).symm.app _)

/-- Unshift a map from the supported coefficient object through the actual source
comparison. Fullness of the shift functor supplies its unique preimage.
Source: derived adjunction in `lem-pur-supported-hom.proof.md`
(blueprint: lem-pur-supported-hom-adjunction-class). -/
def supportedHomAdjunctionMorph
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) (a : ℤ)
    (f : (supportedHomMorphismFunctor A i a).obj K) :
    (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) a).obj (ModuleCat.of A A) ⟶
      (supportedSectionsDerived A i).obj K.obj :=
  (supportedCoefficientDerivedAdjunction A i).homEquiv _ _
    ((shiftFunctor _ a).preimage ((supportedHomAdjunctionSourceIso A i a).inv ≫ f))

/-- Transposing the adjunction class recovers the original supported morphism.
Source: the supported-Hom adjunction in `lem-pur-supported-hom.proof.md`
(blueprint: lem-pur-supported-hom-adjunction-class).

Proof: the inverse Hom equivalence cancels the forward derived adjunction. The shift
functor maps its chosen preimage to the specified map. The remaining source comparison
and its inverse cancel. No cohomology or injective-resolution comparison is involved. -/
theorem supportedHomAdjunctionMorph_transpose
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) (a : ℤ)
    (f : (supportedHomMorphismFunctor A i a).obj K) :
    supportedHomShiftedTranspose A i K a (supportedHomAdjunctionMorph A i K a f) = f := by
  change (DerivedCategory.singleFunctor
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) 0).obj
      ((supportedCoefficients A i).obj (ModuleCat.of A A)) ⟶ K.obj⟦a⟧ at f
  unfold supportedHomShiftedTranspose
  rw [← Category.assoc]
  change (supportedHomAdjunctionSourceIso A i a).hom ≫
    ((supportedCoefficientDerivedAdjunction A i).homEquiv _ K.obj).symm
      (((supportedCoefficientDerivedAdjunction A i).homEquiv _ K.obj)
        ((shiftFunctor _ a).preimage ((supportedHomAdjunctionSourceIso A i a).inv ≫ f)))⟦a⟧' = f
  rw [Equiv.symm_apply_apply, Functor.map_preimage]
  simp

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

/-- The actual supported constant object compared with the ordinary constant model.
Source: finite etale-origin coefficient transport in the zero-section purity proof
(blueprint: lem-pur-supported-hom-adjunction-class). -/
def supportedHomPairCoefficientIso (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (proEtaleSupportHomPair P i).supported ≅
      (ProEtale.supportedCoefficients P.Coefficient i).obj
        (ModuleCat.of P.Coefficient P.Coefficient) :=
  (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).mapIso
    (ProEtale.comparisonUpperStarUnitIso P.Coefficient Z)

/-- The class of a morphism from the actual supported coefficient object. First transport
its source to the ordinary constant model. The derived supported adjunction produces a
map from the free coefficient module in degree a; evaluation of its H^a map on one
is transported to the published bounded-below support functor.
Source: the supported-Hom identification in `lem-pur-gysin-structure.proof.md`
(blueprint: lem-pur-supported-hom-adjunction-class). -/
def supportedHomPairAdjunctionClass (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))) (a : ℤ)
    (f : (proEtaleSupportHomPair P i).derivedHom K a) :
    (proEtaleSupportHomPair P i).group K a :=
  let d := supportedHomPairCoefficientIso P i
  let f' := (DerivedCategory.singleFunctor
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) 0).map d.inv ≫ f
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) a).map
    ((ProEtale.supportSections i P.Coefficient).rightDerivedFunctorPlusCompatibility.inv.app K)
      (ProEtale.supportedHomClassOfMorphism P.Coefficient i K a
        (ProEtale.supportedHomAdjunctionMorph P.Coefficient i K a f'))

end AlgebraicGeometry
