module

public import Sheaf.RingTheory.ChartCoordinateNonzerodivisors
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import Sheaf.RingTheory.RegularLocalLiftRegularSequenceQuotient
import Sheaf.AlgebraicGeometry.BlowupChartRegularSequencePresentation
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.RingTheory.LocalizationOfRegularRing
import WeilConjectures.Blowup.Affine.ChartAlgebra
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Regularity of a parameter blowup algebra

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose VIII, Lemma 4.2.9,
printed p. 121, the regularity part of the local computation with charts
(blueprint: lem-trf-parameter-blowup-algebra-regular).

The quotient chart and its coordinates are the existing `traceChartRing` and
`traceChartCoordinate`. The exceptional quotient A/(t_j) is written out
as the quotient of `traceChartRing` by the span of the image of `t j`.
The two equivalences preserve the coefficient maps; their
values on the ratio variables specify the canonical identifications.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace RingTheory

/-- The parameter chart is Noetherian and regular, its exceptional quotient and
complement have the displayed canonical descriptions, and its exceptional parameter
is a nonzerodivisor. All prime localizations are regular local.

Source: ILO, Travaux de Gabber, Expose VIII, Lemma 4.2.9, printed p. 121
(blueprint: lem-trf-parameter-blowup-algebra-regular).

Proof, following the six steps of the node:
1. Order J with j first and extend to all parameters. The regular-generator theorem
   (lem-weil-pbc-regular-local-generators-regular-sequence) makes this list and its
   initial segment regular. Its parameter quotient C = R/(t_i : i in J) is regular
   local of dimension d - |J|. The prefix quotient is nonzero, since it surjects onto
   the nonzero full quotient. By lem-weil-pbc-regular-local-localization, R and C
   are regular rings.
2. By lem-trf-polynomial-ring-regular-base, the polynomial rings over R and C are
   regular. The chart is a quotient of the former, hence Noetherian by
   lem-weil-pbc-surjective-image-noetherian.
3. Modulo t_j the relations kill all t_i for i in J, and leave the variables free.
   The coefficient quotient and the variable classes define mutually inverse maps
   between A/(t_j) and C[u_i]. After inverting t_j, evaluation at t_i/t_j kills all
   relations and gives A[1/t_j] to R[1/t_j]. The coefficient map gives the inverse.
   Both composites fix coefficients, variables and the inverted parameter, hence
   are identities by the polynomial and localization universal properties
   (def-weil-pbc-mv-polynomial-ring). This also proves the asserted variable images.
4. The regular-prefix chart presentation
   (lem-trf-blowup-chart-regular-sequence-presentation), with signs of relations
   reversed, identifies A with the subalgebra R[I/t_j] of R[1/t_j]
   (def-nagata-blowup-chart-ring). Multiplication by t_j is injective there because
   t_j is a unit in the ambient localization and the subalgebra inclusion is injective.
5. If t_j belongs to a prime P of A, localization preserves Noetherianity
   (lem-weil-pbc-localization-noetherian) and makes its one-element weakly regular
   sequence regular (lem-weil-pbc-weakly-regular-sequence-localization-prime).
   The quotient of A_P by t_j/1 is the corresponding prime localization of A/(t_j)
   (lem-weil-pbc-localization-at-prime-of-quotient), hence regular local by steps
   1--3. Lift regularity across this regular element by
   lem-exc-regular-local-lift-regular-sequence-quotient.
6. If t_j is outside P, A_P is a localization of A[1/t_j]
   (lem-weil-pbc-localization-of-localization). Step 3 identifies this with
   R[1/t_j], and repeated use of lem-weil-pbc-localization-of-regular-ring gives
   regularity of A_P. Since A_P is local it is regular local. The two cases cover
   every prime and prove regularity of A by def-weil-regular-scheme, along with
   the Noetherianity already proved in step 2.
-/
theorem parameterBlowupAlgebra_regular
    {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (d : ℕ) (hd : 1 ≤ d) (hdim : ringKrullDim R = (d : WithBot ℕ∞))
    (t : Fin d → R) (ht : IsLocalRing.IsRegularSystemOfParameters (List.ofFn t))
    (J : Finset (Fin d)) (hJ : J.Nonempty) (j : Fin d) (hj : j ∈ J) :
    IsNoetherianRing (traceChartRing t J j) ∧
    IsRegularRing (traceChartRing t J j) ∧
    (∃ e : (traceChartRing t J j ⧸ Ideal.span
        ({algebraMap R (traceChartRing t J j) (t j)} : Set (traceChartRing t J j))) ≃ₐ[R]
        MvPolynomial (J.erase j) (R ⧸ Ideal.span (t '' (J : Set (Fin d)))),
      ∀ i : J.erase j,
        e (Ideal.Quotient.mk _ (traceChartCoordinate t J j i.val i.property)) =
          MvPolynomial.X i) ∧
    (∃ e : Localization.Away (algebraMap R (traceChartRing t J j) (t j)) ≃ₐ[R]
        Localization.Away (t j),
      ∀ i : J.erase j,
        e (algebraMap (traceChartRing t J j) _
          (traceChartCoordinate t J j i.val i.property)) =
            algebraMap R (Localization.Away (t j)) (t i.val) *
              IsLocalization.Away.invSelf (t j)) ∧
    Function.Injective (fun x : traceChartRing t J j ↦
      algebraMap R (traceChartRing t J j) (t j) * x) ∧
    (∀ (P : Ideal (traceChartRing t J j)) [P.IsPrime],
      IsRegularLocalRing (Localization.AtPrime P)) := by
  sorry

end RingTheory
