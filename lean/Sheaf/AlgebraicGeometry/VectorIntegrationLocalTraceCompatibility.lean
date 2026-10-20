/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts
public import Sheaf.AlgebraicGeometry.EtaleDegreeZeroHom
import Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance
import Sheaf.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DatumUniqueness

/-! # Compatibility of vector-bundle local traces on overlaps

Source: blueprint sec-smooth-purity/sk-prop-an/def-amb-vector-integration,
overlap calculation and normalization paragraph.
(blueprint: lem-amb-vector-integration-local-trace-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The sheaf map corresponding to the prescribed derived trace on a frame open.
The identification of the source with a single sheaf is supplied explicitly; it is
not chosen by this definition. The local Hom correspondence has unique preimages.
Source: blueprint vector integration, degree-zero gluing paragraph.
(blueprint: lem-amb-vector-integration-local-trace-compatibility). -/
@[irreducible]
def vectorIntegrationLocalSheafTrace (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    {L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (α : vectorIntegrationSource A N hA S d F ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj L)
    (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V) :
    (localizationRestriction (ModuleCat.{u + 1} A) V.ι inferInstance).obj L ⟶
      (localizationRestriction (ModuleCat.{u + 1} A) V.ι inferInstance).obj
        (ordinaryFiniteConstant A S) :=
  etaleDegreeZeroHomEquiv A V.ι α
    (vectorIntegrationLocalTrace N hN A hA t D S hS d F V e ≫
      (ordinaryFiniteUnitPullback A V.ι).inv)

/-- The local sheaf trace has exactly the prescribed derived normalization.
Source: blueprint vector integration, degree-zero gluing.
(blueprint: lem-amb-vector-integration-local-trace-compatibility). -/
theorem vectorIntegrationLocalSheafTrace_normalization_iff (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    {L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (α : vectorIntegrationSource A N hA S d F ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj L)
    (ell : L ⟶ ordinaryFiniteConstant A S)
    (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V) :
    (ordinaryFinitePullback A V.ι).map
        (α.hom ≫ (_root_.DerivedCategory.singleFunctor _ 0).map ell) ≫
          (ordinaryFiniteUnitPullback A V.ι).hom =
      vectorIntegrationLocalTrace N hN A hA t D S hS d F V e ↔
    (localizationRestriction (ModuleCat.{u + 1} A) V.ι inferInstance).map ell =
      vectorIntegrationLocalSheafTrace N hN A hA t D S hS d F α V e := by
  unfold vectorIntegrationLocalSheafTrace
  exact etaleDegreeZeroHomEquiv_unit_normalization A V.ι α ell
    (vectorIntegrationLocalTrace N hN A hA t D S hS d F V e)

/-- On an étale object with lifts to two frame opens, the two traces from a fixed
normalized projective-line family with its base-change equations agree.
Source: blueprint vector integration, overlap calculation.
(blueprint: lem-amb-vector-integration-local-trace-compatibility).

Proof:
1. Restrict the frames to their intersection. Open inverse image is exact, so the
   degree-zero Hom correspondence commutes with restriction. Pasting of the actual
   compact-support exchanges and the normalized Tate composition equations express
   each restricted map as the prescribed affine counit for its restricted frame.
   The supplied base-change equation for the projective-line family passes to the
   ordered affine counit by composition of adjunctions.
2. Write the change of frames as e_j=e_i G. Their coordinate change is G transpose;
   consequently phi_i phi_j inverse is the substitution g=(G transpose) inverse.
   The inverse-coordinate squares paste to give B_j=rho_g B_i, with rho_g exactly
   affineLinearTraceAction. The intersection is Noetherian and N remains invertible.
3. Apply affineSpaceLinearTraceInvariance there: rho_g followed by the affine counit
   is that counit. Pull this equality back to the given étale object and evaluate
   its terminal section. Full faithfulness of singleFunctor gives equality of the
   sheaf maps, hence of the displayed descent components. The inserted alpha cancels
   on both sides. Rank zero and the empty intersection satisfy the same equations.
The separate uniqueness lemmas prove the base-change hypothesis from normalization,
and identify every other normalized family with the one used here. -/
theorem vectorIntegrationLocalSheafTrace_compatible_of_baseChange (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    {L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (α : vectorIntegrationSource A N hA S d F ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj L)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (hD : OrdinaryFiniteP1BaseChange A N hA t D)
    (V V' : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V)
    (e' : VectorBundleZeroSection.Trivialization S d F V')
    (W : S.Etale) (q : W ⟶ Scheme.Etale.mk V.ι) (q' : W ⟶ Scheme.Etale.mk V'.ι) :
    descentComponent V.ι
        (vectorIntegrationLocalSheafTrace N hN A hA t D S hS d F α V e) q =
      descentComponent V'.ι
        (vectorIntegrationLocalSheafTrace N hN A hA t D S hS d F α V' e') q' := by
  sorry

/-- The overlap equality also holds for separately supplied normalized Tate transports,
since the normalization determines both the Tate transport and the projective-line data.
Source: blueprint vector integration, overlap and canonical coefficient identifications.
(blueprint: lem-amb-vector-integration-local-trace-compatibility). -/
theorem vectorIntegrationLocalSheafTrace_compatible (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    {L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (α : vectorIntegrationSource A N hA S d F ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj L)
    (t t' : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (D' : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t' T hT)
    (V V' : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V)
    (e' : VectorBundleZeroSection.Trivialization S d F V')
    (W : S.Etale) (q : W ⟶ Scheme.Etale.mk V.ι) (q' : W ⟶ Scheme.Etale.mk V'.ι) :
    descentComponent V.ι
        (vectorIntegrationLocalSheafTrace N hN A hA t D S hS d F α V e) q =
      descentComponent V'.ι
        (vectorIntegrationLocalSheafTrace N hN A hA t' D' S hS d F α V' e') q' := by
  have ht : t' = t := ordinaryFiniteTwistTransport_unique A N hA t' t
  subst t'
  have hd : D' = D := by
    funext T inst hT
    exact ordinaryFiniteP1Datum_unique A N hA t T hT (D' T hT) (D T hT)
  subst D'
  exact vectorIntegrationLocalSheafTrace_compatible_of_baseChange N hN A hA
    S hS d F α t D (ordinaryFiniteP1BaseChange_of_normalization N hN A hA t D)
    V V' e e' W q q'

end AlgebraicGeometry.Etale
