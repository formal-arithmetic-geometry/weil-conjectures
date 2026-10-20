/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.Paper.RingedEtaleOriginWitness
public import Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange
public import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.Paper.ProEtaleRealizedExchange
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange

/-!
# Finite-level pro-etale proper base change

Source: blueprint, proper base change, finite-level pro-etale theorem; Stacks Project
Tag 09C8, the finite-coefficient step in Tag 09C9
(blueprint: thm-weil-pbc-finite-level-proetale).

## Main statements

- `AlgebraicGeometry.Scheme.finiteLevelProEtaleBaseChange`:
  the recorded construction or statement of this node.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The canonical inverse image of the finite constant coefficient sheaf.
Source: Stacks Tag 098T (blueprint: thm-weil-pbc-finite-level-proetale). -/
noncomputable def finiteCoefficientRingIso {U V : Scheme.{u}} (h : U ⟶ V) :
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj (finiteOriginFunctionRing V Λ) ≅
      finiteOriginFunctionRing U Λ :=
  (proEtaleSheafInverseImage h CommRingCat.{u + 1}).mapIso
      (finiteOriginConstantIso V Λ).symm ≪≫
    (letI : ∀ n : ℕᵒᵖ,
        Finite (((Functor.const ℕᵒᵖ).obj (CommRingCat.of Λ)).obj n) :=
      fun _ ↦ inferInstanceAs (Finite Λ)
    @asIso _ _ _ _ ((proEtaleConstantComparison h).app (CommRingCat.of Λ))
      ((proEtale_profinite_coefficient_inverse_image
        ((Functor.const ℕᵒᵖ).obj (CommRingCat.of Λ))).1 U V h (Opposite.op 0))) ≪≫
    finiteOriginConstantIso U Λ

private theorem finiteCoefficientRingIso_eq_realized {U V : Scheme.{u}} (h : U ⟶ V) :
    finiteCoefficientRingIso Λ h =
      proEtaleRealizedCoefficientIso Λ h (finiteOriginConstantIso V Λ)
        (finiteOriginConstantIso U Λ) := by
  apply Iso.ext
  rfl

private theorem finiteCoefficientRingIso_comp {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (k : W ⟶ V) :
    proEtaleRingCompositeCoefficients h k (finiteOriginFunctionRing V Λ)
        (finiteOriginFunctionRing W Λ) (finiteOriginFunctionRing Z Λ)
        (finiteCoefficientRingIso Λ k) (finiteCoefficientRingIso Λ h) =
      finiteCoefficientRingIso Λ (h ≫ k) := by
  simpa only [finiteCoefficientRingIso_eq_realized] using
    proEtaleRealizedCoefficientIso_comp Λ h k (finiteOriginFunctionRing V Λ)
      (finiteOriginFunctionRing W Λ) (finiteOriginFunctionRing Z Λ)
      (finiteOriginConstantIso V Λ) (finiteOriginConstantIso W Λ)
      (finiteOriginConstantIso Z Λ)

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)

include sq in
/-- Finite coefficient identifications agree around the chosen square.
Source: Stacks Tags 098T and 07A7 (blueprint: thm-weil-pbc-finite-level-proetale).
Proof: finite constant comparisons commute with composition by the finite-level
coherence of profinite-coefficient-inverse-image. Apply it to both paths of sq and
identify their composite scheme maps by sq.w. -/
theorem finiteCoefficientRingIso_coherent :
    HEq (proEtaleRingCompositeCoefficients g' f (finiteOriginFunctionRing Y Λ)
      (finiteOriginFunctionRing X Λ) (finiteOriginFunctionRing X' Λ)
      (finiteCoefficientRingIso Λ f) (finiteCoefficientRingIso Λ g'))
    (proEtaleRingCompositeCoefficients f' g (finiteOriginFunctionRing Y Λ)
      (finiteOriginFunctionRing Y' Λ) (finiteOriginFunctionRing X' Λ)
      (finiteCoefficientRingIso Λ g) (finiteCoefficientRingIso Λ f')) := by
  rw [finiteCoefficientRingIso_comp, finiteCoefficientRingIso_comp]
  exact (show ∀ {a b : X' ⟶ Y}, a = b →
    HEq (finiteCoefficientRingIso Λ a) (finiteCoefficientRingIso Λ b) from
      fun w ↦ by cases w; rfl) sq.toCommSq.w

/-- The existing ambient exchange specialized to the canonical finite coefficients.
Source: Stacks Tag 07A7 (blueprint: thm-weil-pbc-finite-level-proetale). -/
noncomputable abbrev finiteCoefficientExchange :=
  proEtaleAmbientRingedExchange sq (finiteOriginFunctionRing X Λ) (finiteOriginFunctionRing Y Λ)
    (finiteOriginFunctionRing X' Λ) (finiteOriginFunctionRing Y' Λ)
    (finiteCoefficientRingIso Λ f) (finiteCoefficientRingIso Λ g)
    (finiteCoefficientRingIso Λ g') (finiteCoefficientRingIso Λ f')
    (finiteCoefficientRingIso_coherent Λ sq)

attribute [local irreducible] proEtaleAmbientRingedExchange
  proEtaleRingCompositeCoefficients
  finiteOriginConstantIso etaleOriginRealization finiteCoefficientRingIso
  proEtaleConstantSections

/-- Finite-coefficient proper exchange is invertible for an object with the retained
bounded-below etale-origin witness. The exchange itself is defined independently of
that witness, so replacing it by an isomorphic witness gives the same arrow.
Source: blueprint finite-level pro-etale theorem; Stacks Tags 09C8 and 09C9
(blueprint: thm-weil-pbc-finite-level-proetale).
Proof: pass to fixed-scalar coordinates by restriction along finiteOriginConstantIso
and the inverse of the exact realization equivalence. The equivalence unit and the
composition comparison turn the retained witness into an isomorphism from the
comparison inverse image of its etale complex to these coordinates. Finiteness of Λ
supplies additive torsion, so bounded-below etale proper base change applies. Properness
is stable under the cartesian base change, giving both direct-image comparison
isomorphisms. The source-library comparison_derivedBaseChangeMap identifies the
transported etale exchange with the fixed-scalar pro-etale exchange; conjugation by
the witness gives its invertibility at the coordinates of K. Finally use
lem-weil-pbc-realized-exchange-normalization with the four canonical coefficient
identifications and their already-proved coherence to recover the actual ambient
ringed exchange. This last normalization is a separate lemma, not a consequence of
the fixed-scalar site-comparison statement. The arrow is intrinsic, so it is unchanged
on replacing the witness. No uniform bound in a coefficient level is used. -/
theorem finiteLevelProEtaleBaseChange [IsProper f]
    (K : DerivedCategory (proEtaleRingModules X (finiteOriginFunctionRing X Λ)))
    (_W : FiniteEtaleOriginWitness X Λ K) :
    IsIso ((finiteCoefficientExchange Λ sq).app K) := by
  let R := (etaleOriginRealization X Λ).mapDerivedCategory.asEquivalence
  let N := (proEtaleRealizedCoordinates Λ X (finiteOriginFunctionRing X Λ)
    (finiteOriginConstantIso X Λ)).obj K
  let a : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
      _W.complex.obj ≅ N :=
    R.unitIso.app _ ≪≫ R.inverse.mapIso
      ((Functor.mapDerivedCategoryCompIso
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X)
        (etaleOriginRealization X Λ)).symm.app _W.complex.obj ≪≫ _W.iso) ≪≫
      (proEtaleConstantSectionsDerivedIsoInverse Λ X).symm.app _
  have hc := finiteCoefficientRingIso_coherent Λ sq
  suffices H : IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
      sq.toCommSq).app N) by
    exact (proEtaleRealizedExchange_isIso_iff Λ sq
      (finiteOriginFunctionRing X Λ) (finiteOriginFunctionRing Y Λ)
      (finiteOriginFunctionRing X' Λ) (finiteOriginFunctionRing Y' Λ)
      (finiteOriginConstantIso X Λ) (finiteOriginConstantIso Y Λ)
      (finiteOriginConstantIso X' Λ) (finiteOriginConstantIso Y' Λ)
      (finiteCoefficientRingIso Λ f) (finiteCoefficientRingIso Λ g)
      (finiteCoefficientRingIso Λ g') (finiteCoefficientRingIso Λ f')
      (finiteCoefficientRingIso_eq_realized Λ f) (finiteCoefficientRingIso_eq_realized Λ g)
      (finiteCoefficientRingIso_eq_realized Λ g') (finiteCoefficientRingIso_eq_realized Λ f')
      hc K).2 H
  rw [← NatTrans.isIso_app_iff_of_iso _ a]
  have hp : IsPullback g' f' f g :=
    IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  have : IsProper f' := MorphismProperty.of_isPullback hp inferInstance
  have := Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring Λ
    (isAddTorsion_of_finite (G := Λ)) hp
  have h := ProEtale.comparison_derivedBaseChangeMap Λ hp _W.complex
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (Arrow.isoMk ((ProEtale.baseChangeSourceComparisonIso f g Λ).app _W.complex)
      ((ProEtale.baseChangeTargetComparisonIso g' f' Λ).app _W.complex) h.symm)).1
        (by infer_instance)

end AlgebraicGeometry.Scheme
