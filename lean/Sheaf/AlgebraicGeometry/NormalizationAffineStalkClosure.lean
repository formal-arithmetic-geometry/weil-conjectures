/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.AffinePushforwardStalkLocalization
import WeilConjectures.RingTheory.ReducedNoetherianTotalRingFractions
import WeilConjectures.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Affine and stalk integral-closure models of finite normalization

Source: Stacks Project, Morphisms, Tags 0C3B and 0CDV; Varieties, Tag 0BXR
(blueprint: lem-trf-normalization-affine-stalk-closure).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/--
For a reduced finite-type scheme over a field, the componentwise normalization is finite and
surjective, is an isomorphism over the dense normal locus, and has the affine and stalk models
by products of integral closures in total quotient rings described in the statement.

Source: Stacks Project, Morphisms, Tags 0C3B, 0CDV, and 035P; Varieties, Tag 0BXR.
Proof (blueprint: lem-trf-normalization-affine-stalk-closure):
1. Apply finite-type Noetherianity, finiteness of irreducible components, and Noetherianity
   of affine sections. Each reduced component is integral and finite type over the field;
   lem-sc-normalization-exists gives its finite surjective function-field normalization.
2. By lem-sc-components-open-injection and lem-sc-irreducible-components-cover the components
   of an open are precisely its nonempty intersections with components of X. Their function
   fields are unchanged, so the integral-closure construction in def-sc-normalization
   restricts to the open. Taking their coproduct gives the asserted map-compatible isomorphism.
3. Finite minimal primes and lem-weil-pbc-spec-irreducible-components-minimal-primes identify
   the affine component charts. The reduced-induced-closed-subscheme lemma identifies their
   rings with R/p_i. The finite affine coproduct spectrum gives the product normalization
   algebra, finite over R, and hence finiteness of the normalization morphism.
4. Componentwise generic properties give surjectivity. Finite-type algebra Noetherianity
   gives Noetherianity of the normalization. Apply lem-sfb-normalization-affine-total-fractions
   and lem-weil-pbc-reduced-noetherian-total-ring-fractions to identify T inside Q(R).
   A monic relation projects to every component; conversely multiplying lifted component
   monic relations proves integrality of a tuple. Thus T is the product of the B_i.
5. Affine-open stalk localization and lem-sc-affine-pushforward-stalk-localization identify
   A_x with R_p and C_x with S-inverse T via germs. Localization preserves reducedness and
   Noetherianity; the images of the finite generators of T generate C_x over A_x.
6. Localizing the finite product of fields kills exactly the factors with p_i not contained
   in p. The primes-of-localization and iterated-localization lemmas identify the survivors
   with the total fractions of A_x. Integral closure commutes with localization, giving the
   asserted structural embedding of C_x and its integral-closure image.
7. T/R is finite. Its localized quotient is C_x/A_x, and the reduced-normal characterization
   makes its vanishing equivalent to the local ring being an integrally closed domain.
   The finite-module support-annihilator theorem gives openness of the normal locus. The
   minimal-prime reduced localizations are fields, so it contains all generic points and is
   dense. Localizing away from the support makes R and T equal; these isomorphisms glue.
8. All maps are structural maps, germs, or their unique localization extensions. Their
   values on numerators and inverted denominators give the restriction and localization
   squares. For empty X the component coproduct is empty and all pointwise claims are vacuous.
-/
theorem normalization_affine_stalk_closure
    {k : Type u} [Field k]
    {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    IsNoetherian X ∧ IsNoetherian X.reducedNormalization ∧
    Finite (irreducibleComponents X) ∧
    IsFinite X.fromReducedNormalization ∧ Surjective X.fromReducedNormalization ∧
    (∃ N : X.Opens,
      (∀ x : X, x ∈ N ↔
        IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)) ∧
      Dense (N : Set X) ∧ IsIso (X.fromReducedNormalization ∣_ N)) ∧
    (∀ V : X.Opens,
      ∃ e : (X.fromReducedNormalization ⁻¹ᵁ V).toScheme ≅ V.toScheme.reducedNormalization,
        e.hom ≫ V.toScheme.fromReducedNormalization = (X.fromReducedNormalization ∣_ V)) ∧
    ∃ (jU : ∀ U : X.affineOpens,
        Γ(X.reducedNormalization, X.fromReducedNormalization ⁻¹ᵁ U.1) →+*
          FractionRing Γ(X, U.1))
      (jx : ∀ x : X,
        ((TopCat.Presheaf.pushforward CommRingCat X.fromReducedNormalization.base).obj
          X.reducedNormalization.presheaf).stalk x →+* FractionRing (X.presheaf.stalk x)),
      (∀ x : X,
        _root_.IsReduced (X.presheaf.stalk x) ∧ IsNoetherianRing (X.presheaf.stalk x) ∧
        Function.Injective
          ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
            X.fromReducedNormalization.c).hom ∧
        ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
          X.fromReducedNormalization.c).hom.Finite ∧
        Function.Injective (jx x) ∧
        (jx x).comp ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
          X.fromReducedNormalization.c).hom =
            algebraMap (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x)) ∧
        Set.range (jx x) =
          (integralClosure (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x)) :
            Set (FractionRing (X.presheaf.stalk x)))) ∧
      (∀ (U : X.affineOpens) (_ : (U.1 : Set X).Nonempty),
        Function.Injective (X.fromReducedNormalization.app U.1).hom ∧
        (X.fromReducedNormalization.app U.1).hom.Finite ∧
        Function.Injective (jU U) ∧
        (jU U).comp (X.fromReducedNormalization.app U.1).hom =
          algebraMap Γ(X, U.1) (FractionRing Γ(X, U.1)) ∧
        Set.range (jU U) =
          (integralClosure Γ(X, U.1) (FractionRing Γ(X, U.1)) :
            Set (FractionRing Γ(X, U.1))) ∧
        ∃ (t : ℕ) (p : Fin t ≃ {p : Ideal Γ(X, U.1) // p ∈ minimalPrimes Γ(X, U.1)})
          (q : FractionRing Γ(X, U.1) ≃+*
            (∀ i : Fin t, FractionRing (Γ(X, U.1) ⧸ (p i).1)))
          (b : Γ(X.reducedNormalization, X.fromReducedNormalization ⁻¹ᵁ U.1) ≃+*
            (∀ i : Fin t,
              integralClosure (Γ(X, U.1) ⧸ (p i).1)
                (FractionRing (Γ(X, U.1) ⧸ (p i).1)))),
          (∀ (r : Γ(X, U.1)) (i : Fin t),
            q (algebraMap Γ(X, U.1) (FractionRing Γ(X, U.1)) r) i =
              algebraMap (Γ(X, U.1) ⧸ (p i).1) (FractionRing (Γ(X, U.1) ⧸ (p i).1))
                (Ideal.Quotient.mk (p i).1 r)) ∧
          (∀ (s : Γ(X.reducedNormalization, X.fromReducedNormalization ⁻¹ᵁ U.1))
            (i : Fin t), (b s i).val = q (jU U s) i) ∧
          (∀ x : U.1,
            @IsLocalization _ _ (U.2.primeIdealOf x).asIdeal.primeCompl
              (X.presheaf.stalk x.1) _ (X.presheaf.germ U.1 x.1 x.2).hom.toAlgebra ∧
            @IsLocalization _ _ ((U.2.primeIdealOf x).asIdeal.primeCompl.map
                (X.fromReducedNormalization.app U.1).hom)
              (((TopCat.Presheaf.pushforward CommRingCat X.fromReducedNormalization.base).obj
                X.reducedNormalization.presheaf).stalk x.1) _
              (((TopCat.Presheaf.pushforward CommRingCat X.fromReducedNormalization.base).obj
                X.reducedNormalization.presheaf).germ U.1 x.1 x.2).hom.toAlgebra ∧
            ∃ (qx : FractionRing (X.presheaf.stalk x.1) ≃+*
                (∀ i : {i : Fin t // (p i).1 ≤ (U.2.primeIdealOf x).asIdeal},
                  FractionRing (Γ(X, U.1) ⧸ (p i.1).1)))
              (ρ : FractionRing Γ(X, U.1) →+* FractionRing (X.presheaf.stalk x.1)),
              ρ.comp (algebraMap Γ(X, U.1) (FractionRing Γ(X, U.1))) =
                (algebraMap (X.presheaf.stalk x.1) (FractionRing (X.presheaf.stalk x.1))).comp
                  (X.presheaf.germ U.1 x.1 x.2).hom ∧
              (∀ (z : FractionRing Γ(X, U.1))
                (i : {i : Fin t // (p i).1 ≤ (U.2.primeIdealOf x).asIdeal}),
                qx (ρ z) i = q z i.1) ∧
              (∀ s : Γ(X.reducedNormalization, X.fromReducedNormalization ⁻¹ᵁ U.1),
                ρ (jU U s) = jx x.1
                  (((TopCat.Presheaf.pushforward CommRingCat X.fromReducedNormalization.base).obj
                    X.reducedNormalization.presheaf).germ U.1 x.1 x.2 s)))) ∧
      (∀ (U V : X.affineOpens) (h : V.1 ≤ U.1),
        ∃ ρ : FractionRing Γ(X, U.1) →+* FractionRing Γ(X, V.1),
          ρ.comp (algebraMap Γ(X, U.1) (FractionRing Γ(X, U.1))) =
            (algebraMap Γ(X, V.1) (FractionRing Γ(X, V.1))).comp
              (X.presheaf.map (homOfLE h).op).hom ∧
          ∀ s : Γ(X.reducedNormalization, X.fromReducedNormalization ⁻¹ᵁ U.1),
            ρ (jU U s) = jU V
              (X.reducedNormalization.presheaf.map
                (homOfLE (X.fromReducedNormalization.preimage_mono h)).op s)) := by
  sorry

end AlgebraicGeometry
