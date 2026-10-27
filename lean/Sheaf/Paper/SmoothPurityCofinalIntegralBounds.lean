/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P9
-/
module

public import Sheaf.Paper.SmoothPurityTowerReconstructionData
public import Sheaf.Paper.CofinalFiniteReductionConstructibility

import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import all Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated

/-! # Integral reduction bounds from ell-power scalar extensions

Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower,
final integral-constructibility sentence.
(blueprint: lem-sp-cofinal-integral-reduction-bounds)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
attribute [local instance high] HasDerivedCategory.standard

namespace AlgebraicGeometry.ProEtale

attribute [-instance] spCoefficientModulesAbelian
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
  (D : SpCoefficientTowersAbelian l E T)

open SheafOfModules.SuccessiveDerivedQuotient

private noncomputable def cofinalPresentationIso
    (p : ∀ {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}}
      (a : R ⟶ S), spCofinalScalarPresentation T a)
    (n : Normalization.{u + 1, u, u + 1, u + 2}
      (C := T.ProEt) (J := Scheme.ProEt.topology T)
      (hD := fun R ↦ HasDerivedCategory.standard (Modules.{u + 1, u, u + 1} R)) p)
    {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    n.right (hD := fun R ↦ HasDerivedCategory.standard
      (Modules.{u + 1, u, u + 1} R)) a ≅
        @Functor.mapDerivedCategory (Modules.{u + 1, u, u + 1} S) _ _
          (HasDerivedCategory.standard _) (Modules.{u + 1, u, u + 1} R) _ _
          (HasDerivedCategory.standard _) (restriction.{u + 1, u, u + 1} a) _ _ _ := by
  let Q := @DerivedCategory.Qh (Modules.{u + 1, u, u + 1} S) _ _ (HasDerivedCategory.standard _)
  let W := HomotopyCategory.quasiIso (Modules.{u + 1, u, u + 1} S) (.up ℤ)
  let F := (restriction.{u + 1, u, u + 1} a).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let : Localization.Lifting Q W F
      (n.right (hD := fun R ↦ HasDerivedCategory.standard
        (Modules.{u + 1, u, u + 1} R)) a) :=
    ⟨n.right_factors (hD := fun R ↦ HasDerivedCategory.standard
      (Modules.{u + 1, u, u + 1} R)) a⟩
  let : Localization.Lifting Q W F (restriction.{u + 1, u, u + 1} a).mapDerivedCategory :=
    ⟨(restriction.{u + 1, u, u + 1} a).mapDerivedCategoryFactorsh⟩
  exact Localization.liftNatIso Q W F F
    (n.right (hD := fun R ↦ HasDerivedCategory.standard
      (Modules.{u + 1, u, u + 1} R)) a)
    (restriction.{u + 1, u, u + 1} a).mapDerivedCategory (Iso.refl F)

private theorem cofinalTor_of_iso (A : Type u) [CommRing A]
    {K L : Scheme.proEtaleDerivedCategory T A} (e : K ≅ L) {a b : ℤ}
    (h : Scheme.HasProEtaleTorAmplitude T A K a b) :
    Scheme.HasProEtaleTorAmplitude T A L a b := by
  refine ⟨h.1, ?_⟩
  intro Q P hQ f hf hP N i hi
  obtain ⟨eQ⟩ := hQ
  exact h.2 Q P ⟨eQ ≪≫ e.symm⟩ f hf hP N i hi

/-- Uniformizer reductions of a completed object inherit constructibility and the
common Tor interval from all its ell-power reductions. This is independent of any
coefficient tower or chosen Roos presentation.
Source: current blueprint, sk-lem-sp-tower.proof.md, final integral-category sentence;
lem-sp-cofinal-finite-reduction-constructibility
(blueprint: lem-sp-cofinal-integral-reduction-bounds).

Proof: factor ell = v*pi^e with e>=1 by the coefficient-fiber lemma. For every j
choose N=j, so j+1 <= e*(N+1). The canonical cofinal quotient B_N -> O/pi^(j+1)
composed with spCompletedEllCommProjection is the uniformizer projection, by the
normalization of the completed coefficient comparison. Present D.scalar and
scalarReductionDerivedExtension by their universal left-derived scalar-extension
counits. The successive-quotient normalization compares their composite with the
derived uniformizer reduction; its equation on flat-term K-flat representatives
makes the comparison independent of presentations. Apply the cofinal finite
reduction constructibility theorem with these normalized presentations. Scalar
extension between the finite quotients preserves constructibility and the stated
Tor interval, without assuming that the quotient map is flat. Test that interval
on the unit module in degree zero to get the displayed cohomological vanishing.
Transport through the normalized comparison to the recorded uniformizer functor.
Neither completeness nor boundedness of the original M is assumed. -/
theorem sp_cofinal_integral_reduction_bounds
    (M : DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))
    (a b : ℤ) (hab : a ≤ b)
    (hM : ∀ n : ℕ,
      (∀ i : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf T
        (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))
        ((DerivedCategory.homologyFunctor _ i).obj
          ((D.scalar (spCompletedEllCommProjection l E T n)).model.T.obj M))) ∧
      Scheme.HasProEtaleTorAmplitude T
        (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))
        ((D.scalar (spCompletedEllCommProjection l E T n)).model.T.obj M) a b) :
    ∀ j : ℕ,
      (∀ i : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf T
        (Padic.coefficientExtensionRing l E (j + 1))
        ((DerivedCategory.homologyFunctor _ i).obj
          ((WeilConjectures.scalarReductionDerivedExtension.{u, u} l E T j).obj M))) ∧
      ∀ i : ℤ, i < a ∨ b < i → IsZero
        ((DerivedCategory.homologyFunctor _ i).obj
          ((WeilConjectures.scalarReductionDerivedExtension.{u, u} l E T j).obj M)) := by
  classical
  obtain ⟨e, v, he, hfactor⟩ := (sp_completed_coefficients_regular l E T).1
  obtain ⟨p, ⟨n⟩⟩ := successive_derived_quotient_normalization
    (J := Scheme.ProEt.topology T)
    (hD := fun R ↦ HasDerivedCategory.standard
      (Modules.{u + 1, u, u + 1} R))
  have hi {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
      (p a).derived ≅ (D.scalar a).model.T :=
    ((n.adjunction (hD := fun R ↦ HasDerivedCategory.standard
      (Modules.{u + 1, u, u + 1} R)) a).ofNatIsoRight
        (cofinalPresentationIso T p n a)).leftAdjointUniq (D.scalar a).adjunction
  have hp (N : ℕ) :
      (sheafCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (spCompletedEllCommProjection l E T N) =
        (sp_completed_coefficient_limit l E T).exists.choose.hom ≫
          limit.π (spCoefficientRings l E T) (op N) := by
    exact Functor.map_preimage _ _
  have h := (sp_cofinal_finite_reduction_constructibility l E T e he v hfactor
    (spCompletedEllCommProjection l E T) hp p n).2.2 M a b hab
  have hell (N : ℕ) := (hi (spCompletedEllCommProjection l E T N)).app M
  have hinput := h (fun N ↦ ⟨fun i ↦
    Scheme.constructibleProEtale_of_iso T _
      ((DerivedCategory.homologyFunctor _ i).mapIso (hell N).symm) ((hM N).1 i),
    cofinalTor_of_iso T _ (hell N).symm (hM N).2⟩)
  intro j
  let adj := (WeilConjectures.derivedScalarExtensionRestrictionAdjunction l E T j).choose
  let e' : (p (WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E T j)).derived ≅
      WeilConjectures.scalarReductionDerivedExtension.{u, u} l E T j :=
    ((n.adjunction (hD := fun R ↦ HasDerivedCategory.standard
      (Modules.{u + 1, u, u + 1} R)) _).ofNatIsoRight
        (cofinalPresentationIso T p n _)).leftAdjointUniq adj
  refine ⟨fun i ↦ ?_, fun i hi ↦ ?_⟩
  · exact Scheme.constructibleProEtale_of_iso T _
      ((DerivedCategory.homologyFunctor _ i).mapIso (e'.app M)) ((hinput j).1 i)
  · exact ((hinput j).2.2 i hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso (e'.app M)).symm

end AlgebraicGeometry.ProEtale
