/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.RingTheory.QuasiFiniteAtPrime

import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Lasker
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.Nakayama
import Sheaf.RingTheory.WeierstrassHenselianCylinder
import Sheaf.RingTheory.ElkikFiniteEtaleAwayCompletion
import Sheaf.RingTheory.FilteredColimitFiniteData
import Sheaf.RingTheory.GeneralizedHenselizationAtPrime
import Sheaf.AlgebraicGeometry.OrdinaryHenselianPointedNeighbourhoodLimit
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import WeilConjectures.RingTheory.FiniteModuleComplete
import Sheaf.RingTheory.CompletionFiniteExtension
import WeilConjectures.RingTheory.LocalCompletionQuotient
import WeilConjectures.RingTheory.FiniteMapColimitDescent
import Sheaf.AlgebraicGeometry.UnramifiedAlgebraOverFieldProduct
import Sheaf.RingTheory.ExcellentRing
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.RingTheory.TraceOneInvariantFiniteness

/-!
# Marked invariant algebras descend to a polynomial cylinder

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose V,
2.2.1--2.2.8 and 3.2.2--3.2.4, printed pp. 65--68
(blueprint: lem-per-equivariant-marked-cylinder-algebraization).

The positive number of variables is written `n + 1`. The parameters `Λ` and `A₀`,
identified by equalities with Mathlib's fixed subrings, name the actual fixed rings.
The equation for `d` specifies the invariant-coordinate inclusion. The equation for
`e` specifies its linearity over that inclusion without choosing auxiliary algebra
instances on the completion. The ring map `k` is characterized by its quotient square.
-/

@[expose] public section
set_option autoImplicit false

universe u v

namespace RingTheory

/-- Algebraize any finite family of ideals of the invariant ring over a polynomial cylinder.

Source: ILO, Expose V, 2.2.1--2.2.8 and 3.2.2--3.2.4, printed pp. 65--68
(blueprint: lem-per-equivariant-marked-cylinder-algebraization).

Proof:
1. Trace one makes V finite over its fixed ring and the fixed ring A₀ Noetherian
   (lem-per-trace-one-noetherian-invariant-finiteness). Invariant inverses make A₀ local;
   integral closure in the fraction field makes it normal. Finite coefficient extension,
   power-series Noetherianity and Noetherian submodule finiteness make A₀ finite over Λ[[t]].
2. Apply lem-per-noetherian-primary-decomposition to the markings, allowing the empty
   intersection for the unit ideal. Keep zero separately. The normal finite primary
   dichotomy gives scalar-annihilated components or vertical symbolic powers.
3. Multiply the norm of the etale denominator, all scalar annihilators and the last
   variable. This product has nonzero reduction. Apply
   lem-per-weierstrass-henselian-cylinder. The shears have coefficients in Λ and hence
   commute with H. In the new coordinates the product is a unit times a distinguished
   polynomial g over D = Λ[[u₁,...,uₙ]].
4. The finite coefficient henselian cylinder identifies the coefficient-extended
   henselization and its g-adic completion. Elkik's finite etale-away-completion
   equivalence algebraizes B to a finite algebra over that henselization.
5. Full faithfulness in Elkik's equivalence uniquely lifts each twisted action map.
   Faithfulness gives the action laws and equivariance of the completion isomorphism.
6. Take invariants. Flat tensor exactness commutes with their finite kernel description.
   Thus the completion of the invariant model is A₀. The finite-over-henselian-local
   product decomposition has exactly one factor, since its completion is nonzero local.
7. Excellence and faithful flatness of local completion show that this henselian model
   is a normal domain: contract principal ideals to descend integral elements.
8. For a scalar-annihilated primary component, the distinguished-polynomial quotient
   is finite over D. Nakayama shows that the henselian model surjects onto the quotient.
9. Cofinality of the D-adic and maximal-ideal filtrations makes this quotient complete.
   Local-completion-quotient identifies its kernel extension with the marked component.
10. For a vertical component apply lem-per-vertical-symbolic-powers-completion to the
    uniformizer. Its height-one prime and each symbolic power descend to the model.
11. Reassemble the markings by finite intersections; flat tensor exactness preserves
    these kernels. Zero and the empty intersection descend as zero and the unit ideal.
12. Use the ordinary henselian pointed-neighbourhood limit and its identification with
    the henselization. Filtered-colimit finite-data descent descends the finite algebra
    and the finitely many ideal generators to one pointed etale finite-presentation stage.
    Finite-map colimit descent makes the algebra finite at a later stage.
13. Contract the local maximal ideal to that stage. Its residue field is finite over
    D/m_D. The pointed etale neighbourhood has the same quotients by powers of the
    maximal ideal as its henselization. Finite-extension completion therefore identifies
    the local completion with A₀, preserving D and every marked ideal.
14. A finite algebra over an etale finite-presentation neighbourhood of D[T] is finite
    type and quasi-finite. Its fibres are finite spectra with finite residue extensions.
    The construction includes n = 0, no markings, and zero and unit markings. -/
theorem exists_equivariant_marked_cylinder_algebraization
    (V B : Type u) [CommRing V] [IsDomain V] [IsLocalRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsLocalRing B]
    [IsNoetherianRing B] [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (H : Type v) [Group H] [Finite H]
    [MulSemiringAction H V] [MulSemiringAction H B]
    (Λ : Subring V) (hΛ : Λ = FixedPoints.subring V H) [IsLocalRing Λ]
    [IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ]
    (hkind : (IsField V ∧ IsField Λ ∧ Subsingleton H) ∨
      (IsDiscreteValuationRing V ∧ IsDiscreteValuationRing Λ))
    (horder : IsUnit (Nat.card H : V))
    (n : ℕ) [Algebra (MvPowerSeries (Fin (n + 1)) V) B]
    [Module.Finite (MvPowerSeries (Fin (n + 1)) V) B]
    [IsLocalHom (algebraMap (MvPowerSeries (Fin (n + 1)) V) B)]
    (hinj : Function.Injective (algebraMap (MvPowerSeries (Fin (n + 1)) V) B))
    (hres : ∃ e : IsLocalRing.ResidueField V ≃+* IsLocalRing.ResidueField B,
      e.toRingHom.comp (IsLocalRing.residue V) = (IsLocalRing.residue B).comp
        ((algebraMap (MvPowerSeries (Fin (n + 1)) V) B).comp MvPowerSeries.C))
    (hequiv : ∀ (h : H) (x : MvPowerSeries (Fin (n + 1)) V),
      h • algebraMap (MvPowerSeries (Fin (n + 1)) V) B x =
        algebraMap (MvPowerSeries (Fin (n + 1)) V) B
          (MvPowerSeries.map (MulSemiringAction.toRingHom H V h) x))
    (f : MvPowerSeries (Fin (n + 1)) V)
    (hred : MvPowerSeries.map (IsLocalRing.residue V) f ≠ 0)
    (hetale : (IsLocalization.Away.map
      (Localization.Away f) (Localization.Away
        (algebraMap (MvPowerSeries (Fin (n + 1)) V) B f))
      (algebraMap (MvPowerSeries (Fin (n + 1)) V) B) f).Etale)
    (A₀ : Subring B) (hA₀ : A₀ = FixedPoints.subring B H)
    (s : ℕ) (I : Fin s → Ideal A₀) :
    ∃ (c : MvPowerSeries (Fin (n + 1)) V ≃ₐ[V] MvPowerSeries (Fin (n + 1)) V),
      (∀ (h : H) (x : MvPowerSeries (Fin (n + 1)) V),
        c (MvPowerSeries.map (MulSemiringAction.toRingHom H V h) x) =
          MvPowerSeries.map (MulSemiringAction.toRingHom H V h) (c x)) ∧
      ∃ (d : MvPowerSeries (Fin n) Λ →+* A₀),
        A₀.subtype.comp d = (algebraMap (MvPowerSeries (Fin (n + 1)) V) B).comp
          (c.toRingHom.comp ((MvPowerSeries.rename Fin.castSucc).toRingHom.comp
            (MvPowerSeries.map Λ.subtype))) ∧
        ∃ (C : Type u) (_ : CommRing C)
          (a : Polynomial (MvPowerSeries (Fin n) Λ) →+* C)
          (hft : a.FiniteType) (p : PrimeSpectrum C),
          p.asIdeal.IsMaximal ∧
          p.asIdeal.comap a = Ideal.comap Polynomial.constantCoeff
            (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) Λ)) ∧
          (∀ q : PrimeSpectrum C,
            @Algebra.IsQuasiFiniteAtPrime (Polynomial (MvPowerSeries (Fin n) Λ)) C
              _ _ a.toAlgebra hft q) ∧
          ∃ (k : (MvPowerSeries (Fin n) Λ ⧸
              IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) Λ)) →+* (C ⧸ p.asIdeal)),
            k.comp (Ideal.Quotient.mk _) =
              (Ideal.Quotient.mk p.asIdeal).comp (a.comp Polynomial.C) ∧
            k.Finite ∧
            ∃ (J : Fin s → Ideal C)
              (e : AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
                (Localization.AtPrime p.asIdeal) ≃+* A₀),
              (∀ x : MvPowerSeries (Fin n) Λ,
                e (algebraMap (Localization.AtPrime p.asIdeal) _
                  (algebraMap C (Localization.AtPrime p.asIdeal) (a (Polynomial.C x)))) = d x) ∧
              ∀ i : Fin s,
                Ideal.map (e.toRingHom.comp
                  ((algebraMap (Localization.AtPrime p.asIdeal) _).comp
                    (algebraMap C (Localization.AtPrime p.asIdeal)))) (J i) = I i := by
  sorry

end RingTheory
