/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import WeilConjectures.RingTheory.GRing

import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.AdicCompletion.LocalRing
import WeilConjectures.RingTheory.FlatLocalCompletionIso
import WeilConjectures.RingTheory.LocalCompletionQuotient
import Sheaf.TraceFormula.CompletedStalkIsomorphismEtale
import Sheaf.TraceFormula.LocalMapCompletionApproximation

/-! # Approximation of completed local-ring isomorphisms

Source: literature/stacks-project/more-morphisms.tex, Tag 0CAV,
lemma-isomorphism-approximation (proof after lemma-map-approximation).
(blueprint: lem-trf-isomorphism-completion-approximation)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- An isomorphism of completed local rings is approximated by common pointed étale
neighbourhoods, with the induced maps agreeing to any prescribed order.

The equation `hφ` says that the given ring isomorphism is over the base stalk.
The completion maps `ψY` and `ψX` are characterized at every finite quotient level
by the transported stalk maps. Their restriction equations are also displayed.
Source: Stacks Project, Tag 0CAV, `lemma-isomorphism-approximation`.

Proof:
1. Restrict φ to the Y stalk and apply `lem-trf-local-map-completion-approximation`
   (Tag 0CAU). This gives an elementary étale map p to X and an S-map q to Y,
   with the required congruence on the original Y stalk.
2. Finite-type affine charts and localization make the X, Y and U stalks
   Noetherian (`lem-weil-pbc-finite-type-over-noetherian`,
   `lem-weil-pbc-flat-local-ring-maps`). Etaleness makes the p stalk map flat
   (`def-weil-flat-morphism`) and its extended maximal ideal equal to that of U
   (`lem-weil-pbc-etale-prime-generates-maximal`). The unchanged residue field
   lets `lem-weil-pbc-flat-local-completion-iso` identify their completions.
   Compose that isomorphism with φ to obtain α; write g for q's completed map.
3. By `lem-weil-pbc-local-completion-local-ring` the extended maximal ideals
   are the maximal ideals in the completions. By
   `lem-weil-pbc-local-completion-quotient`, every element of the Y completion
   is congruent modulo its N-th maximal-ideal power to an original stalk element.
   Locality of g and α extends the congruence from step 1 to all completed elements.
4. Identify the source completion with the U completion using α. The resulting
   endomorphism h differs from the identity by the square of the maximal ideal,
   since N ≥ 2. In a product of r elements of the maximal ideal, the difference
   has one factor in its square and r - 1 factors in the ideal. Thus h is the
   identity on each graded piece; its residue-field map is also the identity.
5. Induct on r to prove bijectivity modulo the r-th maximal-ideal power.
   Injectivity follows by reducing to the preceding quotient and then to the
   graded piece. For surjectivity, lift in the preceding quotient and correct
   the error by an element of the r-th power, on which h is the identity modulo
   the next power.
6. The maximal ideal is finitely generated. By
   `lem-weil-pbc-adic-completion-mod-ideal` its completion is complete for the
   extended maximal ideal. The inverses of the quotient maps from step 5 commute
   with transition maps; apply them coordinatewise to obtain an inverse of h
   (`def-weil-pbc-adic-completion`). Consequently g is an isomorphism.
7. Composition and cancellation of locally finite type maps
   (`lem-weil-pbc-proper-fp-permanence`) show q is locally finite type.
   Apply `lem-trf-completed-stalk-isomorphism-etale` to g and shrink U so q is
   étale with unchanged residue field. The p leg stays étale by
   `lem-weil-pbc-etale-composition-cancellation`. Open restriction preserves
   the marked stalks, the completion maps and the congruence from step 3.
(blueprint: lem-trf-isomorphism-completion-approximation) -/
theorem isomorphism_completion_approximation
    {S X Y : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType fX] [LocallyOfFiniteType fY]
    (x : X) (y : Y) (s : S) (hx : fX x = s) (hy : fY y = s)
    (hGRing : IsGRing (S.presheaf.stalk s))
    (φ :
      AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
          (Y.presheaf.stalk y) ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x))
    (hφ :
      φ.toRingHom.comp
          ((algebraMap (Y.presheaf.stalk y)
            (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
              (Y.presheaf.stalk y))).comp
            ((fY.stalkMap y).hom.comp
              (S.presheaf.stalkCongr (.of_eq hy)).inv.hom)) =
        (algebraMap (X.presheaf.stalk x)
            (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
              (X.presheaf.stalk x))).comp
          ((fX.stalkMap x).hom.comp
            (S.presheaf.stalkCongr (.of_eq hx)).inv.hom)) :
    ∀ N : ℕ, 2 ≤ N →
      ∃ (U : Scheme.{u}) (u : U) (p : U ⟶ X) (q : U ⟶ Y),
        ∃ (hp : p u = x) (hq : q u = y),
        p ≫ fX = q ≫ fY ∧
        ∃ (ψY :
          AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
              (Y.presheaf.stalk y) →+*
            AdicCompletion (IsLocalRing.maximalIdeal (U.presheaf.stalk u))
              (U.presheaf.stalk u))
        (ψX :
          AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
              (X.presheaf.stalk x) →+*
            AdicCompletion (IsLocalRing.maximalIdeal (U.presheaf.stalk u))
              (U.presheaf.stalk u)),
        Etale p ∧ Etale q ∧
        IsIso (p.residueFieldMap u) ∧ IsIso (q.residueFieldMap u) ∧
        ψY.comp (algebraMap (Y.presheaf.stalk y)
          (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
            (Y.presheaf.stalk y))) =
          (algebraMap (U.presheaf.stalk u)
            (AdicCompletion (IsLocalRing.maximalIdeal (U.presheaf.stalk u))
              (U.presheaf.stalk u))).comp ((q.stalkMap u).hom.comp
            (Y.presheaf.stalkCongr (.of_eq hq)).inv.hom) ∧
        ψX.comp (algebraMap (X.presheaf.stalk x)
          (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
            (X.presheaf.stalk x))) =
          (algebraMap (U.presheaf.stalk u)
            (AdicCompletion (IsLocalRing.maximalIdeal (U.presheaf.stalk u))
              (U.presheaf.stalk u))).comp ((p.stalkMap u).hom.comp
            (X.presheaf.stalkCongr (.of_eq hp)).inv.hom) ∧
        (∀ n : ℕ, ∀ z : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
            (Y.presheaf.stalk y), ∀ a : Y.presheaf.stalk y,
          AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) n z =
              Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) ^ n) a →
            AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (U.presheaf.stalk u)) n (ψY z) =
              Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (U.presheaf.stalk u)) ^ n)
                ((q.stalkMap u).hom ((Y.presheaf.stalkCongr (.of_eq hq)).inv.hom a))) ∧
        (∀ n : ℕ, ∀ z : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
            (X.presheaf.stalk x), ∀ a : X.presheaf.stalk x,
          AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) n z =
              Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ^ n) a →
            AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (U.presheaf.stalk u)) n (ψX z) =
              Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (U.presheaf.stalk u)) ^ n)
                ((p.stalkMap u).hom ((X.presheaf.stalkCongr (.of_eq hp)).inv.hom a))) ∧
        ∀ a : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
            (Y.presheaf.stalk y),
          Ideal.Quotient.mk
              ((Ideal.map (algebraMap (U.presheaf.stalk u)
                (AdicCompletion (IsLocalRing.maximalIdeal (U.presheaf.stalk u))
                  (U.presheaf.stalk u)))
                (IsLocalRing.maximalIdeal (U.presheaf.stalk u))) ^ N)
              (ψY a) =
            Ideal.Quotient.mk
              ((Ideal.map (algebraMap (U.presheaf.stalk u)
                (AdicCompletion (IsLocalRing.maximalIdeal (U.presheaf.stalk u))
                  (U.presheaf.stalk u)))
                (IsLocalRing.maximalIdeal (U.presheaf.stalk u))) ^ N)
              (ψX (φ a)) := by
  sorry

end AlgebraicGeometry
