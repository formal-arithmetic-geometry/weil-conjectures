/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Sheaf.AlgebraicGeometry.Morphisms.FieldTorsorGaloisComponents
import Sheaf.AlgebraicGeometry.Morphisms.FieldTorsorComponentGaloisGroup
import Sheaf.AlgebraicGeometry.Morphisms.NormalizationStalkBaseChange

/-! # Integral-closure product after localizing a Cartier torsor

Source: Stacks Project, Tags 0307 and 09EB, and the field-factor argument of
lem-sbc-cartier-generic-stalk-galois-model. -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- Product model of the entire normalization over the Cartier DVR stalk.

Source: Stacks Project, Tags 0307, 09EB, 03SF and 03QR; steps 1 and 2 of
lem-sbc-cartier-generic-stalk-galois-model-core.
(blueprint: lem-sbc-cartier-stalk-normalization-product)

Proof: Pull back the complement and its torsor to Spec R, where R is the displayed
DVR. The Cartier ideal at the generic point of the integral centre is the maximal
ideal of R: the quotient is the field stalk of the centre. Thus the pulled-back
complement is Spec K for K = Frac R. Base change the given pullback square and its
G-action to obtain a finite etale G-torsor over K. Apply field torsor components to
write it as a finite disjoint union of Spec E_i. The component Galois group theorem identifies
Aut_K(E_i) with a
subgroup T_i of G. Transport the canonical automorphism action through the inverse
of this equivalence, giving an action faithful with invariants K.
Normalize this disjoint union over Spec R. On the finite affine product of fields,
integrality is coordinatewise, so its integral closure is the product of the
integral closures of R in E_i. Normalization stalk base change identifies this
normalization with the pullback of the original normalization. All identifications
are over Spec R, giving the displayed structural-map equality. Finite normalization
is preserved by base change; each factor is a direct summand of its finite
coordinate algebra, hence module finite. An empty torsor gives the empty product;
no normalization point or selected prime is required in this assertion. -/
theorem cartier_stalk_normalization_product
    {N U P : Scheme.{u}} [IsLocallyNoetherian N]
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (V : N.Opens) (κ : V.toScheme ⟶ U) (p : P ⟶ V.toScheme) [IsFinite p]
    (r : P ⟶ W.P) (hpb : IsPullback r p W.π κ) :
    let a := p ≫ V.ι
    Etale p → IsFinite a.fromNormalization →
    ∀ (D : Scheme.{u}) (j : D ⟶ N),
      IsIntegral D → IsEffectiveCartierCenter j →
      (∀ z : N, z ∈ V ↔ z ∉ Set.range j) →
      ∀ (η : D), IsGenericPoint η Set.univ →
      ∀ (hdom : IsDomain (N.presheaf.stalk (j η))),
      letI := hdom
      IsDiscreteValuationRing (N.presheaf.stalk (j η)) →
      let R := N.presheaf.stalk (j η)
      ∃ (n : ℕ) (E : Fin n → Type u) (hE : ∀ i, Field (E i))
        (aE : ∀ i, Algebra (FractionRing R) (E i)),
        letI := hE
        letI := aE
        letI (i : Fin n) : Algebra R (E i) :=
          ((algebraMap (FractionRing R) (E i)).comp
            (algebraMap R (FractionRing R))).toAlgebra
        ∃ (T : Fin n → Subgroup G) (act : ∀ i, MulSemiringAction (T i) (E i)),
          letI := act
          (∀ i, IsGaloisGroup (T i) (FractionRing R) (E i)) ∧
          (∀ i, Module.Finite R (integralClosure R (E i))) ∧
          ∃ e : pullback a.fromNormalization (N.fromSpecStalk (j η)) ≅
              ∐ fun i : Fin n ↦ Spec (CommRingCat.of (integralClosure R (E i))),
            e.hom ≫ Sigma.desc (fun i : Fin n ↦
              Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R (E i))))) =
              pullback.snd a.fromNormalization (N.fromSpecStalk (j η)) := by sorry

end AlgebraicGeometry.Scheme
