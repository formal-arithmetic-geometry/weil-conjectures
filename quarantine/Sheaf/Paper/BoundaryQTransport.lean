/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.Paper.BoundaryQMaps
public import Sheaf.SixFunctors.FiniteDualitySiteComparison

/-! # Tensor-Hom transport of boundary pairings

Source: blueprint boundary-duality discharge, final paragraph
(blueprint: def-weil-boundary-q-pairing-transport).
Pairings use the evaluation counit. The Hom comparison is fixed by evaluation;
no arbitrary isomorphism with the same endpoints is admitted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale.BoundaryComparisonOfCoefficients
open BoundaryComparison

variable (C : Type (u + 2)) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [Etale.UpperStarPreservesFlat C] [ProEtale.UpperStarPreservesFlat C]
  [∀ W : Scheme.{u}, (comparisonUpperStar C W).PreservesFlat]

/-- Equality of the tensor-Hom transposes, with the actual monoidal comparison.
Source: blueprint boundary-duality discharge, tensor-Hom paragraph
(blueprint: def-weil-boundary-q-pairing-transport). -/
def PairingTransposeEquality (X : Scheme.{u})
    (V H W : DerivedCategory (Sheaf X.smallEtaleTopology C))
    (W' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) C))
    (χ : (comparison C X).obj (((Etale.derivedHom C X).obj (op V)).obj W) ≅
      ((ProEtale.derivedHom C X).obj (op ((comparison C X).obj V))).obj W')
    (f : ((Etale.derivedTensor C X).obj V).obj H ⟶ W)
    (f' : (comparison C X).obj (((Etale.derivedTensor C X).obj V).obj H) ⟶ W') : Prop :=
  (comparison C X).map ((Etale.derivedTensorHomAdjunction C V).homEquiv H W f) ≫ χ.hom =
    (ProEtale.derivedTensorHomAdjunction C ((comparison C X).obj V)).homEquiv
      ((comparison C X).obj H) W' ((tensorComparison C X V H).inv ≫ f')

/-- The evaluation-defined normalization of the dual internal-Hom comparison.
Source: blueprint finite-duality comparison, final paragraph
(blueprint: def-weil-boundary-q-pairing-transport). -/
def IsEvaluationComparison (X : Scheme.{u})
    (V W : DerivedCategory (Sheaf X.smallEtaleTopology C))
    (W' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) C))
    (w : (comparison C X).obj W ≅ W')
    (χ : (comparison C X).obj (((Etale.derivedHom C X).obj (op V)).obj W) ≅
      ((ProEtale.derivedHom C X).obj (op ((comparison C X).obj V))).obj W') : Prop :=
  χ.hom = siteComparisonEvaluationHom C X V W ≫
    ((ProEtale.derivedHom C X).obj (op ((comparison C X).obj V))).map w.hom

/-- The displayed etale boundary pairing: symmetry, q, exceptional image of evaluation,
then the supplied dualizing identification. The dual representative e is explicit.
Source: blueprint boundary-duality discharge, displayed pairing
(blueprint: def-weil-boundary-q-pairing-transport). -/
def etaleBoundaryPairing {Z T : Scheme.{u}} (i : Z ⟶ T)
    (σZ : EtaleSignedSymmetry C Z) (σT : EtaleSignedSymmetry C T)
    (G : DerivedCategory (Sheaf T.smallEtaleTopology C) ⥤
      DerivedCategory (Sheaf Z.smallEtaleTopology C))
    (K N W : DerivedCategory (Sheaf T.smallEtaleTopology C))
    (V : DerivedCategory (Sheaf Z.smallEtaleTopology C))
    (h : Etale.AmbientDualityPairing C T W)
    (e : N ≅ ((Etale.derivedHom C T).obj (op K)).obj W)
    (d : G.obj W ≅ V)
    (q : ((Etale.derivedTensor C Z).obj
      ((Etale.upperStar C i).leftDerivedFunctor.obj K)).obj (G.obj N) ⟶
        G.obj (((Etale.derivedTensor C T).obj K).obj N)) :
    ((Etale.derivedTensor C Z).obj (G.obj N)).obj
      ((Etale.upperStar C i).leftDerivedFunctor.obj K) ⟶ V :=
  (etaleSwap C Z σZ _ _).hom ≫ q ≫
    G.map (((Etale.derivedTensor C T).obj K).map e.hom ≫
      (etaleSwap C T σT K _).hom ≫ h.choose_spec.2.choose K) ≫ d.hom

/-- The identical pro-etale formula in comparison coordinates. It includes theta_N
inside Q, the Hom comparison χ on the dual representative, and the pro-etale evaluation.
Source: blueprint boundary-duality discharge, displayed pairing
(blueprint: def-weil-boundary-q-pairing-transport). -/
def proBoundaryPairingCoordinates {Z T : Scheme.{u}} (i : Z ⟶ T)
    (σZ : EtaleSignedSymmetry C Z) (σT : ProSignedSymmetry C T)
    (G : DerivedCategory (Sheaf (Scheme.ProEt.topology T) C) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Z) C))
    (K N : DerivedCategory (Sheaf T.smallEtaleTopology C))
    (B : DerivedCategory (Sheaf Z.smallEtaleTopology C))
    (W : DerivedCategory (Sheaf (Scheme.ProEt.topology T) C))
    (V : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) C))
    (h : ProEtale.AmbientDualityPairing C T W)
    (χ : (comparison C T).obj N ≅
      ((ProEtale.derivedHom C T).obj (op ((comparison C T).obj K))).obj W)
    (d : G.obj W ≅ V)
    (Q : (comparison C Z).obj
      (((Etale.derivedTensor C Z).obj
        ((Etale.upperStar C i).leftDerivedFunctor.obj K)).obj B) ⟶
        G.obj ((comparison C T).obj (((Etale.derivedTensor C T).obj K).obj N))) :
    (comparison C Z).obj (((Etale.derivedTensor C Z).obj B).obj
      ((Etale.upperStar C i).leftDerivedFunctor.obj K)) ⟶ V :=
  (comparison C Z).map (etaleSwap C Z σZ _ _).hom ≫ Q ≫
    G.map ((tensorComparison C T K N).hom ≫
      ((ProEtale.derivedTensor C T).obj ((comparison C T).obj K)).map χ.hom ≫
      (proSwap C T σT ((comparison C T).obj K) _).hom ≫
      h.choose_spec.2.choose ((comparison C T).obj K)) ≫ d.hom

/-- The duality assertion for fixed etale dualizing objects and their supplied
pro-etale comparisons. It includes the evaluation-defined general transpose identity
and the displayed q/evaluation composite. An isomorphic bounded-below representative
N of D_T K avoids imposing a new choice of complex on the dual.
Source: blueprint boundary-duality discharge, final paragraph
(blueprint: def-weil-boundary-q-pairing-transport). -/
def BoundaryDualityForFunctors {Z T : Scheme.{u}} (i : Z ⟶ T)
    (Ge : DerivedCategory (Sheaf T.smallEtaleTopology C) ⥤
      DerivedCategory (Sheaf Z.smallEtaleTopology C))
    (Gp : DerivedCategory (Sheaf (Scheme.ProEt.topology T) C) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Z) C))
    (adj : etaleImage C i ⊣ Ge)
    (tr : ∀ (H : DerivedCategory (Sheaf Z.smallEtaleTopology C))
      (L : DerivedCategory (Sheaf (Scheme.ProEt.topology T) C)),
      ((proetaleImage C i).obj ((comparison C Z).obj H) ⟶ L) →
        ((comparison C Z).obj H ⟶ Gp.obj L))
    (θ : ∀ N : DerivedCategory (Sheaf T.smallEtaleTopology C),
      (comparison C Z).obj (Ge.obj N) ⟶ Gp.obj ((comparison C T).obj N))
    (hcounit : DerivedCategory.Plus (Sheaf T.smallEtaleTopology C) → Prop)
    (μ : ∀ N : DerivedCategory.Plus (Sheaf T.smallEtaleTopology C), hcounit N →
      ((proetaleImage C i).obj (Gp.obj ((comparison C T).obj N.obj)) ⟶
        (comparison C T).obj N.obj))
    (PT : ObjectProperty (DerivedCategory (Sheaf T.smallEtaleTopology C)))
    (PZ : ObjectProperty (DerivedCategory (Sheaf Z.smallEtaleTopology C)))
    (ωT : DerivedCategory (Sheaf T.smallEtaleTopology C))
    (ωZ : DerivedCategory (Sheaf Z.smallEtaleTopology C)) : Prop :=
  ∀ (σeZ : EtaleSignedSymmetry C Z) (σeT : EtaleSignedSymmetry C T)
    (σpZ : ProSignedSymmetry C Z) (σpT : ProSignedSymmetry C T)
    (ωT' : DerivedCategory (Sheaf (Scheme.ProEt.topology T) C))
    (ωZ' : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) C))
    (wT : (comparison C T).obj ωT ≅ ωT')
    (wZ : (comparison C Z).obj ωZ ≅ ωZ')
    (hTe : Etale.AmbientDualityPairing C T ωT)
    (hTp : ProEtale.AmbientDualityPairing C T ωT')
    (hZe : Etale.AmbientDualityPairing C Z ωZ)
    (hZp : ProEtale.AmbientDualityPairing C Z ωZ')
    (de : Ge.obj ωT ≅ ωZ)
    (dp : Gp.obj ωT' ≅ ωZ'),
    (comparison C Z).map de.hom ≫ wZ.hom =
      θ ωT ≫ Gp.map wT.hom ≫ dp.hom →
    (∀ (V H : DerivedCategory (Sheaf Z.smallEtaleTopology C)),
      PZ V → PZ H →
      ∀ χ : (comparison C Z).obj
          (((Etale.derivedHom C Z).obj (op V)).obj ωZ) ≅
        ((ProEtale.derivedHom C Z).obj
          (op ((comparison C Z).obj V))).obj ωZ',
        IsEvaluationComparison C Z V ωZ ωZ' wZ χ →
        ∀ f : ((Etale.derivedTensor C Z).obj V).obj H ⟶ ωZ,
          PairingTransposeEquality C Z V H ωZ ωZ' χ f
            ((comparison C Z).map f ≫ wZ.hom)) ∧
    (∀ V : DerivedCategory (Sheaf Z.smallEtaleTopology C),
      PZ V → FiniteDualityCompatibility C Z ωZ ωZ' wZ hZe hZp V) ∧
    ∀ (K N : DerivedCategory.Plus (Sheaf T.smallEtaleTopology C))
      (e : N.obj ≅ ((Etale.derivedHom C T).obj (op K.obj)).obj ωT),
      PT K.obj → PT N.obj →
      PZ ((Etale.upperStar C i).leftDerivedFunctor.obj K.obj) →
      PZ (Ge.obj N.obj) →
      PT (((Etale.derivedHom C T).obj (op N.obj)).obj ωT) →
      PZ (((Etale.derivedHom C Z).obj
        (op ((Etale.upperStar C i).leftDerivedFunctor.obj K.obj))).obj ωZ) →
      PZ (((Etale.derivedHom C Z).obj
        (op (Ge.obj N.obj))).obj ωZ) →
      ∀ (hc : hcounit N),
        ProjectionComparison C i (Ge.obj N.obj) K.obj →
        ∀ (_he : IsIso (etaleProjection C i
            (Ge.obj N.obj) K.obj))
          (_hp : IsIso
            (((ProEtale.rightDerivedLowerStarProjectionMap C i).app
              (Gp.obj ((comparison C T).obj N.obj))).app
                ((comparison C T).obj K.obj)))
          (χT : (comparison C T).obj
              (((Etale.derivedHom C T).obj (op K.obj)).obj ωT) ≅
            ((ProEtale.derivedHom C T).obj
              (op ((comparison C T).obj K.obj))).obj ωT')
          (χZ : (comparison C Z).obj
              (((Etale.derivedHom C Z).obj
                (op ((Etale.upperStar C i).leftDerivedFunctor.obj K.obj))).obj ωZ) ≅
            ((ProEtale.derivedHom C Z).obj
              (op ((comparison C Z).obj
                ((Etale.upperStar C i).leftDerivedFunctor.obj K.obj)))).obj ωZ'),
          IsEvaluationComparison C T K.obj ωT ωT' wT χT →
          IsEvaluationComparison C Z
            ((Etale.upperStar C i).leftDerivedFunctor.obj K.obj)
            ωZ ωZ' wZ χZ →
          PairingTransposeEquality C Z
            ((Etale.upperStar C i).leftDerivedFunctor.obj K.obj)
            (Ge.obj N.obj) ωZ ωZ' χZ
            ((etaleSwap C Z
              σeZ _ _).hom ≫
              etaleBoundaryPairing C i
                σeZ σeT Ge
                K.obj N.obj ωT ωZ hTe e de
                (etaleQForAdjunction C i
                  σeZ
                  σeT Ge
                  adj K.obj N.obj))
            ((comparison C Z).map
                (etaleSwap C Z
              σeZ _ _).hom ≫
              proBoundaryPairingCoordinates C i
                σeZ σpT Gp
                K.obj N.obj (Ge.obj N.obj) ωT' ωZ' hTp
                ((comparison C T).mapIso e ≪≫ χT) dp
                (assembleProQ C i σpZ σpT Ge Gp tr
                  K.obj N.obj (θ N.obj) (μ N hc)))

/-- Specialize the pairing formulas to the actual finite exceptional functors, unit,
Hom transport and uniquely normalized counit. No free functor or transpose remains.
Source: blueprint boundary-duality discharge, final paragraph
(blueprint: def-weil-boundary-q-pairing-transport). -/
def BoundaryDualityCompatibility (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsProper i] [CompactSpace T]
    (PT : ObjectProperty (DerivedCategory (Sheaf T.smallEtaleTopology (coefficients A))))
    (PZ : ObjectProperty (DerivedCategory (Sheaf Z.smallEtaleTopology (coefficients A))))
    (ωT : DerivedCategory (Sheaf T.smallEtaleTopology (coefficients A)))
    (ωZ : DerivedCategory (Sheaf Z.smallEtaleTopology (coefficients A))) : Prop :=
  BoundaryDualityForFunctors (coefficients A) i (etaleExceptional A i)
    (proetaleExceptional A i) (exceptionalAdjunction A i)
    (rawHomTransport A i) (rawOriginMap A i) (CounitComparison A i)
    (proCounit A i) PT PZ ωT ωZ

end AlgebraicGeometry.ProEtale.BoundaryComparisonOfCoefficients
