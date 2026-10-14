/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
/-! # Geometric factor and residue square at a Cartier DVR stalk

Source: Stacks Project, Tags 0307 and 09EB, and the field-factor argument of
lem-sbc-cartier-generic-stalk-galois-model. -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- Geometric local model with compatible residue-field isomorphisms.
Source: Stacks Project, Tags 0307 and 09EB.
(blueprint: lem-sbc-cartier-generic-stalk-galois-model-core)
Proof: Localize at j(eta). The Cartier ideal becomes the maximal ideal because
D is integral and eta is generic; its complement is the fraction field of the DVR.
The pullback torsor there is a finite etale algebra, a product of separable fields.
Choose the factor containing a generization of x and take its stabilizer T. The
simply transitive torsor action identifies T with the Galois group of that factor.
Take its integral closure S over the DVR. Normalization commutes with localization
(Tag 0307), so S is a factor of the localized normalization and is module finite.
It embeds in the field factor, hence is a domain and the base map is injective.
The T-action preserves integral elements. Taking fractions recovers the selected
field factor (clear denominators in a monic equation over the DVR), and the lifted
T-action is its Galois action. Thus the assertion about the fraction fields follows.
The point x determines a prime q₀ of this selected factor. The
localization and factor maps respect the base maps, yielding the two displayed
residue-field isomorphisms and their commutative square. The dimension equality,
flatness, and ring-level Galois assertion follow from
the square, injectivity, and integrality over the integrally closed DVR.
The normalization fibre being empty is vacuous. For trivial G the factor is the
fraction field and S is the DVR. No arbitrary algebra model is substituted for
the factor that contains x. -/
theorem cartier_generic_stalk_galois_model_core
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
      ∀ (x : a.normalization), a.fromNormalization x = j η →
        ∃ (S : CommRingCat.{u}) (T : Subgroup G)
          (alg : Algebra (N.presheaf.stalk (j η)) S),
          letI := alg
          ∃ (act : MulSemiringAction T S),
          letI := act
          ∃ (hS : IsDomain S),
          letI := hS
          ∃ (hinj : Function.Injective (algebraMap (N.presheaf.stalk (j η)) S)),
          letI : Module.IsTorsionFree (N.presheaf.stalk (j η)) S :=
            Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
          letI := FractionRing.liftAlgebra (N.presheaf.stalk (j η)) (FractionRing S)
          letI := IsFractionRing.mulSemiringAction T S (FractionRing S)
          Module.Finite (N.presheaf.stalk (j η)) S ∧
          IsGaloisGroup T (FractionRing (N.presheaf.stalk (j η))) (FractionRing S) ∧
          ∃ (q₀ : Ideal S) (hq₀ : q₀.IsPrime),
            letI := hq₀
            letI := Localization.AtPrime.algebraOfLiesOver
              (q₀.under (N.presheaf.stalk (j η))) q₀
            letI := (a.fromNormalization.residueFieldMap x).hom.toAlgebra
            ∃ (e : N.residueField (a.fromNormalization x) ≃+*
                (q₀.under (N.presheaf.stalk (j η))).ResidueField)
              (f : a.normalization.residueField x ≃+* q₀.ResidueField),
              (algebraMap (q₀.under (N.presheaf.stalk (j η))).ResidueField
                q₀.ResidueField).comp e.toRingHom =
                f.toRingHom.comp (algebraMap (N.residueField (a.fromNormalization x))
                  (a.normalization.residueField x)) := by
  sorry
end AlgebraicGeometry.Scheme
