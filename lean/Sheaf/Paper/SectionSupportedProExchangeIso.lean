/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H7
-/
module

public import Sheaf.Paper.SectionCompactSourceMaps
import all Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization
import Sheaf.Paper.SectionSupportedComparisonIso
import WeilConjectures.SixFunctors.Finite.BaseChange
import WeilConjectures.SixFunctors.OpenClosed.Exact

/-! # Invertibility of a supported-constant comparison component

Source: blueprint rank-one Thom proof, Step 3; Stacks Tags 095L and 0F7F.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SectionCompactSource
variable (A : Type (u + 1)) [CommRing A]

/-- The actual pro-etale exchange on closed supported constants is invertible.
Source: blueprint rank-one Thom proof, Step 3; Stacks Tags 0F7F and 095L
(blueprint: lem-pur-section-supported-pro-exchange-iso).
Proof: restriction of the constant to a closed subscheme is an epimorphism on
the etale site by open/closed recollement. Cancel its inverse image under etale
pullback and comparison. The restriction normalization of exchange and gamma,
and coherence of the scalar units, then identify gamma_s' composed with the
etale exchange with the pro-etale exchange composed with pullback of gamma_s
and comparison-pullback. Etale finite base change makes its exchange invertible.
Both gamma maps are invertible by closed direct-image site comparison, as are
the pullback comparison and constant units. Cancel these factors to conclude.
No quasi-compactness of the open complement or finiteness of the base change
is needed; empty closed subschemes give the zero-object isomorphism. -/
theorem supported_pro_exchange_isIso [Finite A] {B' B X' X : Scheme.{u}}
    {g : B' ⟶ B} {s' : B' ⟶ X'} {s : B ⟶ X} {v : X' ⟶ X}
    [IsClosedImmersion s] [IsClosedImmersion s']
    (sq : ChosenCartesianSquare g s' s v) :
    IsIso (SupportedConstantNormalization.exchange A true sq) := by
  let R := SupportedConstantNormalization.restriction A false s
  have hR : Epi R := by
    let S := Etale.openClosedShortComplex (ModuleCat.{u + 1} A) s.openComplement.ι s
      (disjoint_range_of_range_eq_compl s.openComplement.ι s
        s.range_eq_compl_range_openComplement_ι)
      (SupportedConstantNormalization.constant A false X)
    have hs : S.ShortExact := Etale.shortExact_openClosedShortComplex
      (ModuleCat.{u + 1} A) s.openComplement.ι s
      (SupportedConstantNormalization.constant A false X)
      s.range_eq_compl_range_openComplement_ι
    have := hs.epi_g
    change Epi (S.g ≫ (SupportedConstantNormalization.push A false s).map
      (SupportedConstantNormalization.unitIso A false s).hom)
    infer_instance
  have hsq : IsPullback g s' s v := IsPullback.of_iso_pullback
    sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  have he : IsIso (SupportedConstantNormalization.exchange A false sq) := by
    have := Etale.isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} A) hsq
    unfold SupportedConstantNormalization.exchange
    infer_instance
  have hg := supported_comparison_isIso A s
  have hg' := supported_comparison_isIso A s'
  have hw :
      (SupportedConstantNormalization.compare A X').map
          (SupportedConstantNormalization.exchange A false sq) ≫
        SupportedConstantNormalization.gamma A s' =
      (SupportedConstantNormalization.comparePullback A v).hom.app
          (SupportedConstantNormalization.supported A false s) ≫
        (SupportedConstantNormalization.pull A true v).map
          (SupportedConstantNormalization.gamma A s) ≫
        SupportedConstantNormalization.exchange A true sq := by
    have hn :
        (SupportedConstantNormalization.compare A X').map
            ((SupportedConstantNormalization.pull A false v).map R) ≫
          (SupportedConstantNormalization.comparePullback A v).hom.app
            (SupportedConstantNormalization.supported A false s) =
        (SupportedConstantNormalization.comparePullback A v).hom.app
            (SupportedConstantNormalization.constant A false X) ≫
          (SupportedConstantNormalization.pull A true v).map
            ((SupportedConstantNormalization.compare A X).map R) :=
      (SupportedConstantNormalization.comparePullback A v).hom.naturality R
    have hk :
        (SupportedConstantNormalization.compare A X').map
            (SupportedConstantNormalization.unitIso A false v).hom ≫
          (SupportedConstantNormalization.compareUnit A X').hom =
        (SupportedConstantNormalization.comparePullback A v).hom.app
            (SupportedConstantNormalization.constant A false X) ≫
          (SupportedConstantNormalization.pull A true v).map
            (SupportedConstantNormalization.compareUnit A X).hom ≫
          (SupportedConstantNormalization.unitIso A true v).hom := by
      apply (cancel_epi ((SupportedConstantNormalization.comparePullback A v).inv.app
        (SupportedConstantNormalization.constant A false X))).mp
      simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using
        SupportedConstantNormalization.compare_constant_square A v
    apply (cancel_epi ((SupportedConstantNormalization.compare A X').map
      ((SupportedConstantNormalization.pull A false v).map R))).mp
    dsimp only [R] at hn ⊢
    rw [← Functor.map_comp_assoc, SupportedConstantNormalization.exchange_normalized,
      Functor.map_comp, Category.assoc, SupportedConstantNormalization.gamma_normalized]
    change _ = (SupportedConstantNormalization.compare A X').map
        ((SupportedConstantNormalization.pull A false v).map
          (SupportedConstantNormalization.restriction A false s)) ≫
      (SupportedConstantNormalization.comparePullback A v).hom.app
          (SupportedConstantNormalization.supported A false s) ≫
        (SupportedConstantNormalization.pull A true v).map
          (SupportedConstantNormalization.gamma A s) ≫
        SupportedConstantNormalization.exchange A true sq
    rw [reassoc_of% hn]
    rw [← Functor.map_comp_assoc, SupportedConstantNormalization.gamma_normalized,
      Functor.map_comp, Category.assoc, SupportedConstantNormalization.exchange_normalized]
    simpa only [Category.assoc] using congrArg
      (fun t ↦ t ≫ SupportedConstantNormalization.restriction A true s') hk
  have hcomp : IsIso
      ((SupportedConstantNormalization.comparePullback A v).hom.app
          (SupportedConstantNormalization.supported A false s) ≫
        (SupportedConstantNormalization.pull A true v).map
          (SupportedConstantNormalization.gamma A s) ≫
        SupportedConstantNormalization.exchange A true sq) := by
    rw [← hw]
    infer_instance
  have : IsIso ((SupportedConstantNormalization.pull A true v).map
      (SupportedConstantNormalization.gamma A s) ≫
        SupportedConstantNormalization.exchange A true sq) :=
    IsIso.of_isIso_comp_left
      ((SupportedConstantNormalization.comparePullback A v).hom.app
        (SupportedConstantNormalization.supported A false s)) _
  exact IsIso.of_isIso_comp_left
    ((SupportedConstantNormalization.pull A true v).map
      (SupportedConstantNormalization.gamma A s)) _

end AlgebraicGeometry.SectionCompactSource
