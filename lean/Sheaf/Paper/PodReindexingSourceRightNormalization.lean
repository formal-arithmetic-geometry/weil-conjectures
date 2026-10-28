/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X7
-/
module

public import Sheaf.Paper.PodReindexingSourceModelFactors

/-! # Right-route normalization of the source-shift square

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X and 08JA.
This computes the right composite on K-injective Hom models.
(blueprint: lem-pod-reindexing-source-right-normalization)
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

/-- The right route of the source-shift square on localized Hom models.

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X and 08JA.

Proof:

1. Write F,K,Q,alpha,beta,kappa as in the model-factor definitions. Apply the source-site
LeftNormalization at source QP with representative P and identity representative isomorphism.
Uniqueness of LeftFormula identifies the chosen chain isomorphism with eY. Invert the equation to
obtain kappa_(P[a],I)^(-1) followed by Hom(Q shift(a)^(-1),id) followed by sourceShift.inv =
Q(eY.inv) followed by Q shift(-a) followed by kappa_(P,I)^(-1)[-a].

2. Apply F to this equation. Naturality of F shift(-a) moves F of the shifted kappa inverse to the
shifted F(kappa inverse). Shifted functoriality groups it with c.derived and the first part of
beta. Comparison.derived_model at (P,I) identifies that grouped composite with
localizationFactors(Hom(P,I)) followed by Q(c.chain(P,I)); all kappa and Hom-factor inverses
cancel.

3. Use shift compatibility of localizationFactors at Hom(P,I), then naturality of that factor
along eY.inv. Finally naturality of Q shift(-a) along c.chain(P,I) moves Q shift to the far right.
The remaining composite is localizationFactors(Hom(P[a],I)), Q of K(eY.inv) followed by
complexShift(-a) followed by c.chain(P,I)[-a], and Q shift(-a) at Hom(KP,KI), as claimed.

This calculates one route, independently of the chain square and of the other route.
(blueprint: lem-pod-reindexing-source-right-normalization) -/
theorem source_right_normalization
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY) (P I : K l E Y s) (a : ℤ)
    [I.IsKInjective] [CochainComplex.IsKInjective ((podReindexingComplexFunctor l E g s).obj I)]
    (eY : (hom l E Y s P I)⟦-a⟧ ≅ hom l E Y s (P⟦a⟧) I)
    (hY : CategoryTheory.RingedHomUniverses.LeftFormula.{u + 1, u, u}
      (ProEt.topology Y) (podReindexingRing l E Y s) P I a eY) :
    (sourceModelInput l E g s P I a).hom ≫
      ((podReindexingDerivedFunctor l E g s).map
      ((CategoryTheory.RingedHomUniverses.sourceShift.{u + 1, u, u, u + 2}
        (ProEt.topology Y) (podReindexingRing l E Y s) ((podReindexingQ l E Y s).obj P)
          a).inv.app ((podReindexingQ l E Y s).obj I)) ≫
      ((podReindexingDerivedFunctor l E g s).commShiftIso (-a)).hom.app
        ((podReindexingDerivedHom l E Y s).obj (op ((podReindexingQ l E Y s).obj P),
          ((podReindexingQ l E Y s).obj I))) ≫
      (c.derived.hom.app (op ((podReindexingQ l E Y s).obj P), ((podReindexingQ l E Y s).obj
          I)))⟦-a⟧') ≫
      (sourceModelOutput l E g s P I a).hom =
    (podReindexingDerivedFactors l E g s).hom.app (hom l E Y s (P⟦a⟧) I) ≫
      (podReindexingQ l E X s).map
        ((podReindexingComplexFunctor l E g s).map eY.inv ≫
          (complexShift l E g s (-a)).hom.app (hom l E Y s P I) ≫
          ((c.chain P I).hom)⟦-a⟧') ≫
      ((podReindexingQ l E X s).commShiftIso (-a)).hom.app
        (hom l E X s ((podReindexingComplexFunctor l E g s).obj P)
          ((podReindexingComplexFunctor l E g s).obj I)) := by sorry

end WeilConjectures.PodReindexingCoherence
