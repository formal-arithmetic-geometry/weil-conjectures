/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X7
-/
module

public import Sheaf.Paper.PodReindexingSourceModelFactors

/-! # Left-route normalization of the source-shift square

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X and 08JA.
This computes the left composite on K-injective Hom models.
(blueprint: lem-pod-reindexing-source-left-normalization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReindexingCoherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The left route of the source-shift square on localized Hom models.

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X and 08JA.

Proof:

1. Write F for the derived reindexing, K for its complex functor, Q for localization, alpha for
sourceModelInput, beta for sourceModelOutput, and kappa for the recorded Hom model. Alpha is F of
kappa_(P[a],I)^(-1) followed by the Hom map of Q shift(a)^(-1) in the opposite source. Naturality
of c.derived along that source map reduces its component at ((QP)[a],QI) to its component at
(Q(P[a]),QI).

2. Apply Comparison.derived_model at (P[a],I). Cancel F(kappa_(P[a],I)^(-1)) against its
F(kappa_(P[a],I)) factor. The composite now starts with the localization factor at Hom(P[a],I),
followed by Q(c.chain(P[a],I)), then the target ordinary-to-derived Hom model and its
localization-factor transports.

3. Apply LeftNormalization on X to source F(QP), representative KP, and representative isomorphism
(localizationFactors(P)).symm. Use uniqueness of LeftFormula to identify its chain reindexing with
the given eX. Invert the normalization equation. Naturality in the target moves
localizationFactors(I) through sourceShift.inv. Naturality of the ordinary Hom comparison in the
source moves the map of (complexShift(a)).inv through the Hom model.

4. The shift compatibility of localizationFactors(P) identifies F(Q shift(a)) followed by F
shift(a) with localization of complexShift(a) followed by Q shift(a). Cancel the resulting inverse
pairs and beta. What remains, in order, is localizationFactors(Hom(P[a],I)), Q of c.chain(P[a],I)
followed by Hom((complexShift(a)).inv,id) followed by eX.inv, and Q shift(-a) at Hom(KP,KI). This
is the asserted left normal form.

This calculates one route, independently of the chain square and of the other route.
(blueprint: lem-pod-reindexing-source-left-normalization) -/
theorem source_left_normalization
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY) (P I : K l E Y s) (a : ℤ)
    [I.IsKInjective] [CochainComplex.IsKInjective ((podReindexingComplexFunctor l E g s).obj I)]
    (eX : (hom l E X s ((podReindexingComplexFunctor l E g s).obj P)
      ((podReindexingComplexFunctor l E g s).obj I))⟦-a⟧ ≅
      hom l E X s (((podReindexingComplexFunctor l E g s).obj P)⟦a⟧)
        ((podReindexingComplexFunctor l E g s).obj I))
    (hX : CategoryTheory.RingedHomUniverses.LeftFormula.{u + 1, u, u}
      (ProEt.topology X) (podReindexingRing l E X s)
      ((podReindexingComplexFunctor l E g s).obj P)
      ((podReindexingComplexFunctor l E g s).obj I) a eX) :
    (sourceModelInput l E g s P I a).hom ≫
      (c.derived.hom.app (op (((podReindexingQ l E Y s).obj P)⟦a⟧), ((podReindexingQ l E Y s).obj
          I)) ≫
      (podReindexingDerivedHom l E X s).map
        (Prod.mkHom (((podReindexingDerivedFunctor l E g s).commShiftIso a).inv.app
          ((podReindexingQ l E Y s).obj P)).op
          (𝟙 ((podReindexingDerivedFunctor l E g s).obj ((podReindexingQ l E Y s).obj I)))) ≫
      (CategoryTheory.RingedHomUniverses.sourceShift.{u + 1, u, u, u + 2}
        (ProEt.topology X) (podReindexingRing l E X s)
        ((podReindexingDerivedFunctor l E g s).obj ((podReindexingQ l E Y s).obj P)) a).inv.app
          ((podReindexingDerivedFunctor l E g s).obj ((podReindexingQ l E Y s).obj I))) ≫
      (sourceModelOutput l E g s P I a).hom =
    (podReindexingDerivedFactors l E g s).hom.app (hom l E Y s (P⟦a⟧) I) ≫
      (podReindexingQ l E X s).map
        ((c.chain (P⟦a⟧) I).hom ≫
          ((podReindexingHom l E X s).map
            ((complexShift l E g s a).inv.app P).op).app
              ((podReindexingComplexFunctor l E g s).obj I) ≫ eX.inv) ≫
      ((podReindexingQ l E X s).commShiftIso (-a)).hom.app
        (hom l E X s ((podReindexingComplexFunctor l E g s).obj P)
          ((podReindexingComplexFunctor l E g s).obj I)) := by sorry

end WeilConjectures.PodReindexingCoherence
