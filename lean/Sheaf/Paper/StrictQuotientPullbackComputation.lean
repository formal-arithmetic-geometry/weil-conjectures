/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.Paper.CompletedTowerPullback
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Sheaf.Algebra.Homology.DiagramKFlatReplacements

/-! # Resolved strict quotient pullback with its specified augmentation

Source: blueprint sec-six-functors-basics/sk-prop-sf-cbc,
lem-cbc-completed-extension-zero-comparison.proof.md, completed-pullback invocation;
Stacks Tag 06XN, dual part (blueprint: lem-cbc-strict-quotient-pullback-computation).
The positive exponent n+1 is indexed by n : ℕ, as in the coefficient datum.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- A K-flat flat-term representative over the actual completed coefficient sheaf.
Flatness means exactness of tensoring, without identifying site universes.
Source: Stacks 06XN and 06YS (blueprint: lem-cbc-strict-quotient-pullback-computation). -/
structure CbcStrictKFlatRepresentative (T : Scheme.{u}) where
  complex : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ
  kflat : CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion T d) complex
  flat : ∀ q : ℤ, exactFunctor _ _
    (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory (pbcAdicCompletion T d))
      (complex.X q))

/-- The existing strict quotient complex, with its existing quotient transitions.
Source: blueprint CBC computation (blueprint: lem-cbc-strict-quotient-pullback-computation). -/
abbrev cbcStrictReduction (T : Scheme.{u}) := completedReductionComplexTowerFunctor T d

/-- The constant strict complex, with identity transitions.
Source: blueprint CBC computation (blueprint: lem-cbc-strict-quotient-pullback-computation). -/
abbrev cbcStrictDelta (T : Scheme.{u}) :=
  (completedTowerConstant d T).mapHomologicalComplex (.up ℤ)

/-- The original quotient augmentation, induced by the section map x ↦ 1 tensor x.
The coefficient-first convention is the scalar-extension presentation of x tensor 1.
Source: blueprint CBC computation (blueprint: lem-cbc-strict-quotient-pullback-computation). -/
def cbcStrictAugmentation (T : Scheme.{u})
    (P : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) :
    (cbcStrictDelta d T).obj P ⟶ (cbcStrictReduction d T).obj P :=
  letI := completedReductionModuleTowerFunctor_additive T d
  (NatTrans.mapHomologicalComplex (completedReductionModuleUnit d T) (.up ℤ)).app P

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Apply the projection-defined module pullback to a strict tower complex.
Source: Stacks 099N (blueprint: lem-cbc-strict-quotient-pullback-computation). -/
abbrev cbcStrictPull := (completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)

variable (LF : DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) ⥤
    DerivedCategory (pbcTowers X (pbcAdicCompletion X d)))
  (τ : DerivedCategory.Qh ⋙ LF ⟶
    (completedTowerModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)

/-- The specified universal counit on actual strict cochain representatives.
Source: Stacks 06XN (blueprint: lem-cbc-strict-quotient-pullback-computation). -/
abbrev cbcStrictCounit (H : CochainComplex (pbcTowers Y (pbcAdicCompletion Y d)) ℤ) :=
  Functor.leftDerivedCounitOnComplex (completedTowerModulePullback g d) LF τ H

/-- A strict quasi-isomorphic resolution with objectwise K-flat flat-term source.
No lift of the quotient augmentation is part of this data.
Source: Stacks 06XN, 06YS (blueprint: lem-cbc-strict-quotient-pullback-computation). -/
structure CbcStrictQuotientResolution (P : CbcStrictKFlatRepresentative d Y) where
  complex : CochainComplex (pbcTowers Y (pbcAdicCompletion Y d)) ℤ
  arrow : complex ⟶ (cbcStrictReduction d Y).obj P.complex
  quasiIso : QuasiIso arrow
  kflat : ∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients
    (R := pbcAdicCompletion Y d)
    ((((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj
      (op n)).mapHomologicalComplex (.up ℤ)).obj complex)
  flat : ∀ (n : ℕ) (q : ℤ), exactFunctor _ _
    (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory (pbcAdicCompletion Y d))
      (((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj
        (op n)).obj (complex.X q)))

/-- The counit formula chi_r = tau_H composed with L(Qr) inverse.
Its inverse of L(Qr) exists because r is a quasi-isomorphism, independently of G(r).
Source: Stacks 06XN (blueprint: lem-cbc-strict-quotient-pullback-computation). -/
def cbcStrictResolutionMap (P : CbcStrictKFlatRepresentative d Y)
    (r : CbcStrictQuotientResolution d P) :
    LF.obj (DerivedCategory.Q.obj ((cbcStrictReduction d Y).obj P.complex)) ⟶
      DerivedCategory.Q.obj ((cbcStrictPull d g).obj r.complex) :=
  letI := r.quasiIso
  inv (LF.map (DerivedCategory.Q.map r.arrow)) ≫ cbcStrictCounit d g LF τ r.complex

/-- The augmentation transported through the invertible counit on the constant complex.
Source: blueprint CBC computation (blueprint: lem-cbc-strict-quotient-pullback-computation). -/
def cbcStrictPulledAugmentation (P : CbcStrictKFlatRepresentative d Y)
    (δ : LF.obj (DerivedCategory.Q.obj ((cbcStrictDelta d Y).obj P.complex)) ≅
      DerivedCategory.Q.obj ((cbcStrictPull d g).obj ((cbcStrictDelta d Y).obj P.complex))) :
    DerivedCategory.Q.obj ((cbcStrictPull d g).obj ((cbcStrictDelta d Y).obj P.complex)) ⟶
      LF.obj (DerivedCategory.Q.obj ((cbcStrictReduction d Y).obj P.complex)) :=
  δ.inv ≫ LF.map (DerivedCategory.Q.map (cbcStrictAugmentation d Y P.complex))

/-- The representative map B(f) on pulled-back constant complexes.
Source: blueprint CBC computation (blueprint: lem-cbc-strict-quotient-pullback-computation). -/
def cbcStrictConstantMap {P P' : CbcStrictKFlatRepresentative d Y}
    (f : P.complex ⟶ P'.complex) :=
  DerivedCategory.Q.map ((cbcStrictPull d g).map ((cbcStrictDelta d Y).map f))

/-- The representative map D(f) on derived pulled-back quotient complexes.
Source: blueprint CBC computation (blueprint: lem-cbc-strict-quotient-pullback-computation). -/
def cbcStrictReductionMap {P P' : CbcStrictKFlatRepresentative d Y}
    (f : P.complex ⟶ P'.complex) :=
  LF.map (DerivedCategory.Q.map ((cbcStrictReduction d Y).map f))

/-- Computation on every strict resolution retains the actual quotient augmentation.
Source: blueprint CBC completed-pullback invocation; Stacks 06XN, dual part
(blueprint: lem-cbc-strict-quotient-pullback-computation).

Proof:
1. The existing quotient transitions preserve 1, so the augmentation is a strict chain
map and natural in P. Levelwise G takes Delta P to Delta G(P), with identity transitions.
2. The diagram K-flat replacement theorem supplies the resolving class and invariance
of quasi-isomorphisms on it. Additive G preserves shifts and cones. Apply the resolving-
class theorem. Uniqueness of universal pairs transfers its invertible counit components
at H and Delta P to the specified pair LF,tau.
3. Invert LF(Qr), compose with tau_H, and use counit naturality at r and at a_P.
This gives Q'G(r) chi_r w_P = Q'G(a_P), without inverting tau_R(P) or G(r).
4. The comparison from r to s is chi_r inverse followed by chi_s. Cancellation proves
its compatibility with the augmented maps, its identity and the three-resolution cocycle.
5. Counit naturality and R(f) a_P = a_P' Delta(f) give naturality of w.
6. Derived change of rings makes R(f) a quasi-isomorphism for quasi-isomorphic K-flat
representatives. Tower cohomology is levelwise. Diagram pullback invariance makes B(f)
invertible. Inverting the naturality square proves compatibility with localization and,
by conjugating with chi, with every resolved presentation. -/
theorem strictQuotientPullbackComputation
    (_hpair : LF.IsLeftDerivedFunctor τ
      (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ))) :
    ∃ (δ : ∀ P : CbcStrictKFlatRepresentative d Y,
        LF.obj (DerivedCategory.Q.obj ((cbcStrictDelta d Y).obj P.complex)) ≅
          DerivedCategory.Q.obj
            ((cbcStrictPull d g).obj ((cbcStrictDelta d Y).obj P.complex)))
      (χ : ∀ (P : CbcStrictKFlatRepresentative d Y) (r : CbcStrictQuotientResolution d P),
        LF.obj (DerivedCategory.Q.obj ((cbcStrictReduction d Y).obj P.complex)) ≅
          DerivedCategory.Q.obj ((cbcStrictPull d g).obj r.complex)),
      (∀ P : CbcStrictKFlatRepresentative d Y,
        (δ P).hom = cbcStrictCounit d g LF τ ((cbcStrictDelta d Y).obj P.complex)) ∧
      (∀ (P : CbcStrictKFlatRepresentative d Y) (r : CbcStrictQuotientResolution d P),
        (χ P r).hom = cbcStrictResolutionMap d g LF τ P r) ∧
      (∀ P : CbcStrictKFlatRepresentative d Y,
        ((completedTowerConstant d X).mapHomologicalComplex (.up ℤ)).obj
            (((completedModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P.complex) =
          (cbcStrictPull d g).obj ((cbcStrictDelta d Y).obj P.complex)) ∧
      (∀ (P : CbcStrictKFlatRepresentative d Y) (r : CbcStrictQuotientResolution d P),
        cbcStrictPulledAugmentation d g LF P (δ P) ≫ (χ P r).hom ≫
            DerivedCategory.Q.map ((cbcStrictPull d g).map r.arrow) =
          DerivedCategory.Q.map
            ((cbcStrictPull d g).map (cbcStrictAugmentation d Y P.complex))) ∧
      (∀ (P : CbcStrictKFlatRepresentative d Y) (r s : CbcStrictQuotientResolution d P),
        (cbcStrictPulledAugmentation d g LF P (δ P) ≫ (χ P r).hom) ≫
            ((χ P r).symm ≪≫ χ P s).hom =
          cbcStrictPulledAugmentation d g LF P (δ P) ≫ (χ P s).hom) ∧
      (∀ (P : CbcStrictKFlatRepresentative d Y) (r s t : CbcStrictQuotientResolution d P),
        ((χ P r).symm ≪≫ χ P s).hom ≫ ((χ P s).symm ≪≫ χ P t).hom =
          ((χ P r).symm ≪≫ χ P t).hom) ∧
      (∀ (P : CbcStrictKFlatRepresentative d Y) (r : CbcStrictQuotientResolution d P),
        ((χ P r).symm ≪≫ χ P r).hom = 𝟙 _) ∧
      (∀ (P P' : CbcStrictKFlatRepresentative d Y) (f : P.complex ⟶ P'.complex),
        cbcStrictPulledAugmentation d g LF P (δ P) ≫ cbcStrictReductionMap d LF f =
          cbcStrictConstantMap d g f ≫ cbcStrictPulledAugmentation d g LF P' (δ P')) ∧
      (∀ (P P' : CbcStrictKFlatRepresentative d Y) (f : P.complex ⟶ P'.complex),
        QuasiIso f →
        ∃ (b : DerivedCategory.Q.obj
              ((cbcStrictPull d g).obj ((cbcStrictDelta d Y).obj P.complex)) ≅
            DerivedCategory.Q.obj
              ((cbcStrictPull d g).obj ((cbcStrictDelta d Y).obj P'.complex)))
          (e : LF.obj (DerivedCategory.Q.obj ((cbcStrictReduction d Y).obj P.complex)) ≅
            LF.obj (DerivedCategory.Q.obj ((cbcStrictReduction d Y).obj P'.complex))),
          b.hom = cbcStrictConstantMap d g f ∧ e.hom = cbcStrictReductionMap d LF f ∧
          b.inv ≫ cbcStrictPulledAugmentation d g LF P (δ P) =
            cbcStrictPulledAugmentation d g LF P' (δ P') ≫ e.inv) := by
  sorry

end AlgebraicGeometry.Scheme
