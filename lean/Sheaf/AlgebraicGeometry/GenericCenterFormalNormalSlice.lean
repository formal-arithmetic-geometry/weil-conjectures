/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleCoordinateFlag
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.AlgebraicGeometry.AdaptedNormalCrossingsCenter
public import Sheaf.AlgebraicGeometry.MarkedIdealOrder
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.RingTheory.ParameterChartCompletionSubstitution
public import WeilConjectures.Blowup.Affine.ChartAlgebra
public import WeilConjectures.Blowup.Gluing

import Sheaf.RingTheory.GenericSmoothDomain
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.SmoothPairLocalCoordinates
import Sheaf.AlgebraicGeometry.EtaleLocalNormalForm
import Sheaf.AlgebraicGeometry.ConormalSequenceSmoothImmersion
import WeilConjectures.RingTheory.RegularSequenceConormal
import Sheaf.AlgebraicGeometry.EtaleAtPointFromDifferentials
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.CompletionRegularLocal
import WeilConjectures.RingTheory.CompletionDimension
import WeilConjectures.RingTheory.ExistsCoefficientSubring
import Sheaf.RingTheory.RegularCompleteCoefficientCoordinates
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import Sheaf.AlgebraicGeometry.BlowupChartRegularSequencePresentation
import Sheaf.AlgebraicGeometry.CoordinateSubspaceBlowupCharts
import WeilConjectures.Blowup.FiniteDegree.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Generic smooth centers and completed normal slices

Source: Stacks Project, Tags 0B8X, 0FUE, 0C0S and 00MC, with the explicit
simultaneous-normal-slice and parameter-chart calculation in the DAG proof
(blueprint: lem-trf-generic-center-formal-normal-slice).

The auxiliary predicates only expand the formal-coordinate clauses of this theorem.
All ideal sheaves, stalk ideals, flag coordinates and chart rings are the existing ones.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory TopologicalSpace IsLocalRing
namespace AlgebraicGeometry

/-- The reduced closure of a point, constructed by its vanishing ideal.
Source: Stacks Project, Tag 00ES, and the affine-prime calculation in step 1
(blueprint: lem-trf-generic-center-formal-normal-slice). -/
def genericCenterIdeal (X : Scheme.{u}) (x : X) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨closure ({x} : Set X), isClosed_closure⟩

/-- The residue map from the ambient point to a point on its closed support.
Source: Stacks Project, residue fields of closed immersions, and step 1
(blueprint: lem-trf-generic-center-formal-normal-slice). -/
def genericCenterResidueMap {X Z : Scheme.{u}} (i : X ⟶ Z) (y : X) (x : Z)
    (h : i y = x) : Z.residueField x →+* X.residueField y :=
  ((eqToHom (congrArg Z.residueField h.symm)) ≫ i.residueFieldMap y).hom

/-- The completed local chart at the generic coordinate section, with its actual
structural map, fixed coefficients, labelled ratio substitutions, and their extension
from polynomials to every power series. The final clause identifies the quotient
presentation with the actual fraction chart after localizing at the original point x.
These clauses concern charts over the local ring, without a global blowup comparison.
Source: Stacks Project, Tags 0804 and 0C0S; DAG proof steps 10--12
(blueprint: lem-trf-generic-center-formal-normal-slice). -/
def HasGenericCenterChartCoordinates
    (R F : Type u) [CommRing R] [IsLocalRing R] [Field F]
    {n r : ℕ} (v : Fin n → R)
    (c : F →+* AdicCompletion (maximalIdeal R) R)
    (J : Finset (Fin (n + r))) (a : Option (Fin (n + r))) : Prop :=
  (parameterChartOrigin v J a).IsMaximal ∧
  ∀ [(parameterChartOrigin v J a).IsPrime],
    ∃ (ε : ResidueField (ParameterChartLocalRing v J a) ≃+* F)
      (g : AdicCompletion (maximalIdeal R) R →+* ParameterChartCompletion v J a),
      (∀ (k : ℕ) (z : AdicCompletion (maximalIdeal R) R) (b : R),
        AdicCompletion.evalₐ (maximalIdeal R) k z =
          Ideal.Quotient.mk (maximalIdeal R ^ k) b →
        AdicCompletion.evalₐ (maximalIdeal (ParameterChartLocalRing v J a)) k (g z) =
          Ideal.Quotient.mk (maximalIdeal (ParameterChartLocalRing v J a) ^ k)
            (parameterChartStructuralMap v J a b)) ∧
      (∀ b : F, ε (AdicCompletion.evalOneₐ
        (maximalIdeal (ParameterChartLocalRing v J a)) (g (c b))) = b) ∧
      ∃ Θ : MvPowerSeries (Fin (n + r)) F ≃+* ParameterChartCompletion v J a,
        (∀ b : F, Θ (MvPowerSeries.C b) = g (c b)) ∧
        (∀ i : Fin (n + r), Θ (MvPowerSeries.X i) =
          parameterChartIntoCompletion v J a (parameterChartCoordinate v J a i)) ∧
        (∀ k : ℕ, Ideal.comap Θ.toRingHom (parameterChartCompletedIdeal v J a ^ k) =
          Ideal.span (Set.range (MvPowerSeries.X : Fin (n + r) →
            MvPowerSeries (Fin (n + r)) F)) ^ k) ∧
        (∀ i : Fin (n + r),
          Θ.symm (parameterChartIntoCompletion v J a
            (parameterChartPolynomialMap v J a (parameterChartBaseParameter v i))) =
              parameterChartSubstitutionVariable F J a i) ∧
        (∀ (ψ : MvPowerSeries (Fin n) F ≃+* AdicCompletion (maximalIdeal R) R),
          (∀ b : F, ψ (MvPowerSeries.C b) = c b) →
          (∀ i : Fin n, ψ (MvPowerSeries.X i) =
            algebraMap R (AdicCompletion (maximalIdeal R) R) (v i)) →
          ∀ (z : MvPowerSeries (Fin n) F) (k : ℕ),
            Θ.symm (g (ψ z)) - MvPolynomial.eval₂ MvPowerSeries.C
              (fun i : Fin n ↦ parameterChartSubstitutionVariable F J a (i.castAdd r))
              (MvPowerSeries.truncTotal k z) ∈
                Ideal.span (Set.range (MvPowerSeries.X : Fin (n + r) →
                  MvPowerSeries (Fin (n + r)) F)) ^ k) ∧
        (∀ b : Fin (n + r), a = some b →
          ∃ e : ParameterChartRing v J a ≃ₐ[MvPolynomial (Fin r) R]
            AffineBlowup.chartRing
              (Ideal.span (parameterChartBaseParameter v '' (J : Set (Fin (n + r)))))
              (parameterChartBaseParameter v b),
            ∀ i : (parameterChartCenter J).erase (parameterChartPivot a),
              ((e (Ideal.Quotient.mk _ (MvPolynomial.X i)) :
                AffineBlowup.chartRing
                  (Ideal.span (parameterChartBaseParameter v '' (J : Set (Fin (n + r)))))
                  (parameterChartBaseParameter v b)) :
                Localization.Away (parameterChartBaseParameter v b)) =
                AffineBlowup.chartFraction (parameterChartBaseParameter v b) 1
                  (Fin.snoc (α := fun _ : Fin (n + r + 1) ↦ MvPolynomial (Fin r) R)
                    (parameterChartBaseParameter v) 0 i.1))

/-- A coefficient section common to every prescribed regular parameter system, and
all coordinate-product and blowup-chart completions. Ideal extension preserves and
reflects ordinary order, boundary divisibility and zero.
Source: Stacks Project, Tags 0C0S and 00MC, DAG proof steps 7--12
(blueprint: lem-trf-generic-center-formal-normal-slice). -/
def HasGenericCenterFormalCoordinates
    (R F : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Field F]
    (ε : F →+* ResidueField R) : Prop :=
  Function.Bijective ε ∧
  (∃ (n : ℕ) (v : Fin n → R), IsRegularSystemOfParameters (List.ofFn v)) ∧
  ∃ c : F →+* AdicCompletion (maximalIdeal R) R,
    (∀ b : F, AdicCompletion.evalOneₐ (maximalIdeal R) (c b) = ε b) ∧
    (∀ (K : Ideal R) (q : ℕ),
      K.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) ≤
        ((maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R))) ^ q ↔
          K ≤ maximalIdeal R ^ q) ∧
    (∀ K : Ideal R,
      K.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) = ⊥ ↔ K = ⊥) ∧
    ∀ (n : ℕ) (v : Fin n → R), IsRegularSystemOfParameters (List.ofFn v) →
      (∃ ψ : MvPowerSeries (Fin n) F ≃+* AdicCompletion (maximalIdeal R) R,
        (∀ b : F, ψ (MvPowerSeries.C b) = c b) ∧
        (∀ i : Fin n, ψ (MvPowerSeries.X i) =
          algebraMap R (AdicCompletion (maximalIdeal R) R) (v i)) ∧
        (∀ q : ℕ, Ideal.comap ψ.toRingHom
          (((maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R))) ^ q) =
          Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) F)) ^ q)) ∧
      (∀ (i : Fin n) (K : Ideal R) (q : ℕ),
        K.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) ≤
          (Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) (v i)}) ^ q ↔
            K ≤ (Ideal.span {v i}) ^ q) ∧
      (∀ (r : ℕ) (J : Finset (Fin (n + r))) (a : Option (Fin (n + r))),
        (J = ∅ ∧ a = none) ∨ (∃ b ∈ J, a = some b) →
          HasGenericCenterChartCoordinates R F v c J a)

/-- Simultaneous generic smooth centers and formal normal coordinates.
Source: Stacks Project, Tags 0B8X, 0FUE, 0C0S and 00MC
(blueprint: lem-trf-generic-center-formal-normal-slice).

Proof:
1. Work on an affine neighbourhood Spec A of x, with prime p. The reduced closure
   is Spec(A/p); it lies in each support and in each boundary through x. Delete
   the finitely many boundary components missing x (lem-weil-pbc-spec-irreducible-
   closed-subsets-primes and lem-weil-pbc-affine-open-stalk-localization).
2. The finite-type domain A/p over Q is generically smooth: use characteristic-zero
   separability, lem-exc-generic-smooth-domain and the affine smoothness criterion.
   Localize at a lift of the resulting nonzero element of A/p. Smoothness gives
   regular local rings (lem-weil-pbc-smooth-scheme-over-field-regular).
3. Spread each ideal containment, and each zero germ, by expressing finitely many
   coherent generators in the center-ideal power at x and clearing denominators.
   Intersect the finitely many ambient opens.
4. For each support choose parameters beginning with the boundary equations.
   Represent them by sections of the center ideal and shrink so they generate it.
   Choose regular equations for the support in Z by lem-pur-smooth-pair-local-coordinates;
   lift these parameters and etale coordinates of the smooth center to Z.
5. The two smooth-immersion conormal sequences show that the differentials of this
   tuple are a residue-field basis (lem-pur-conormal-sequence-smooth-immersion,
   lem-weil-pbc-regular-sequence-conormal-free, lem-trf-etale-coordinate-derivations-jacobian).
   Apply lem-pur-etale-at-point-from-differentials. No rationality of x is assumed.
6. Intersect the finitely many opens. The support equations are a subset of the
   center equations; the boundary equations are distinct remaining coordinates.
   Outside the support or center use its complement. This is HasEtaleCoordinateFlag.
7. Complete each regular Noetherian local ring: the completion is Noetherian, local,
   regular, and of the same dimension (the recorded completion lemmas).
8. The characteristic-zero Cohen coefficient-ring theorem gives a section of the
   residue field. Lem-trf-regular-complete-coefficient-coordinates works for every
   prescribed parameter system with that same section, including dimension zero.
9. Faithful flatness of completion, applied to R/L, gives LH intersect R = L
   (lem-weil-pbc-faithfully-flat-universally-injective). Thus extension preserves
   and reflects maximal-ideal powers, parameter powers, and the zero ideal.
10. Identify the actual affine blowup charts A[P/a] using the finite generator cover.
    Localization gives R[m/a]. Regularity of every permutation of the parameters
    and lem-trf-blowup-chart-regular-sequence-presentation give the quotient chart.
11. Apply lem-trf-parameter-chart-completion-substitution: J empty gives a product,
    J nonempty gives the coordinate blowup with its pivot. The quotient-to-fraction
    equivalence pins these to the actual charts. Coefficients are transported by
    the completed structural map, so the substitutions fix the chosen field.
12. Repeating these constructions composes the actual structural maps and transports
    each coefficient section along the composite, retaining the same coefficients.
    The zero-dimensional blowup has no pivot; its zero-ideal Rees Proj is empty.
-/
theorem exists_genericCenter_formalNormalSlice
    {Z : Scheme.{u}} (p : Z ⟶ Spec (.of (ULift.{u} ℚ)))
    [Smooth p] [LocallyOfFiniteType p] [QuasiCompact p]
    (E : List Z.IdealSheafData) (hE : IsStrictNormalCrossingsBoundary E.prod)
    (hlabels : Function.Injective (fun j : Fin E.length ↦ (E.get j).support))
    (hcomponents : ∀ j : Fin E.length, IsIntegral (E.get j).subscheme)
    (s : ℕ) (hs : 1 ≤ s) (N : Fin s → Scheme.{u}) (i : ∀ j : Fin s, N j ⟶ Z)
    [∀ j : Fin s, IsClosedImmersion (i j)] [∀ j : Fin s, Smooth (i j ≫ p)]
    (htransverse : ∀ j : Fin s, HasAdaptedNormalCrossingsCenter
      (⊥ : (N j).IdealSheafData) (fun k : Fin E.length ↦ (E.get k).comap (i j)))
    (x : Z) (y : ∀ j : Fin s, N j) (hy : ∀ j : Fin s, i j (y j) = x)
    (I : ∀ j : Fin s, (N j).IdealSheafData)
    (hI : ∀ j : Fin s, RingedSpace.IsCoherent (N j).toRingedSpace (I j).toModules)
    (d : Fin s → ℕ) (hd : ∀ j : Fin s, 1 ≤ d j)
    (horder : ∀ j : Fin s, HilbertSamuel.stalkIdeal (I j) (y j) ≤
      maximalIdeal ((N j).presheaf.stalk (y j)) ^ d j) :
    (∃ (U : Z.Opens) (hx : x ∈ U) (T : U.toScheme.IdealSheafData),
      T = genericCenterIdeal U.toScheme ⟨x, hx⟩ ∧
      Smooth (T.subschemeι ≫ U.ι ≫ p) ∧
      (∀ k : Fin E.length,
        (x ∈ (E.get k).support → (E.get k).comap U.ι ≤ T) ∧
        (x ∉ (E.get k).support → (E.get k).comap U.ι = ⊤)) ∧
      ∀ j : Fin s,
        (i j).ker.comap U.ι ≤ T ∧
        HasEtaleCoordinateFlag (U.ι ≫ p) ((i j).ker.comap U.ι) T
          (E.map (fun D ↦ D.comap U.ι)) ∧
        Smooth ((T.comap ((i j) ∣_ U)).subschemeι ≫ (i j ⁻¹ᵁ U).ι ≫ i j ≫ p) ∧
        (I j).comap (i j ⁻¹ᵁ U).ι ≤ (T.comap ((i j) ∣_ U)) ^ d j ∧
        (HilbertSamuel.stalkIdeal (I j) (y j) = ⊥ →
          (I j).comap (i j ⁻¹ᵁ U).ι = ⊥)) ∧
    (∀ j : Fin s, ∃ hR : IsNoetherianRing ((N j).presheaf.stalk (y j)),
      @HasGenericCenterFormalCoordinates ((N j).presheaf.stalk (y j))
        (Z.residueField x) _ _ hR _ (genericCenterResidueMap (i j) (y j) x (hy j))) := by
  sorry

end AlgebraicGeometry
