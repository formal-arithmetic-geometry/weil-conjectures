/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sheaf.RingTheory.JapaneseDomain
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Tate's criterion for an N-2 complete principal domain

Source: Stacks Project, Algebra, Lemma Tag 032P (lemma-tate-japanese),
lines 45534--45589 (blueprint: lem-weil-pbc-tate-n2-complete-principal).
-/

universe u v

set_option autoImplicit false

/-- A Noetherian normal domain complete along a principal ideal whose quotient is N-2
is itself N-2. Source: Stacks Project, Algebra, Lemma Tag 032P (blueprint:
lem-weil-pbc-tate-n2-complete-principal).

Proof (the twelve steps in the node):
1. If x = 0, identify R with its quotient and use the N-2 hypothesis.
2. In characteristic zero, finite field extensions are separable; apply
   `lem-weil-pbc-noetherian-normal-separable-integral-closure-finite`.
3. In positive characteristic use
   `lem-weil-pbc-n2-char-p-purely-inseparable-criterion` to reduce to purely
   inseparable finite extensions L/K.
4. Choose a common Frobenius exponent q. Enlarge L to contain y with y^q = x,
   retaining finiteness and L^q contained in K. Finiteness of the larger closure
   implies finiteness of the original one by the Noetherian submodule lemma.
5. For S the integral closure, normality gives S^q contained in R and
   xS intersect R = xR; also y belongs to S and is nonzero.
6. The equivalence f in yS iff f^q in xR shows yS is prime over xR.
7. The principal-ideal height bound and localization dimension lemma show
   R localized at xR is a one-dimensional Noetherian local domain.
8. Apply `lem-weil-pbc-dim-one-residue-field-extensions-finite` to obtain
   finiteness of the corresponding residue-field extension.
9. N-2 of R/xR makes its integral closure in that residue field finite.
   S/yS embeds in it, hence is finite by the Noetherian submodule lemma.
10. The filtration by powers of y and
    `lem-weil-pbc-module-finite-extension-of-finite` give finiteness of S/xS.
11. Completeness makes the intersection of x^n R zero. Taking q-th powers
    then makes the intersection of x^n S zero as well.
12. Apply `lem-weil-pbc-finite-over-complete-ring` to S. Undo the enlargement
    and the purely inseparable reduction to conclude N-2.
(blueprint: lem-weil-pbc-tate-n2-complete-principal). -/
theorem tate_n2_complete_principal (R : Type u) (K : Type v) [CommRing R]
    [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [IsNoetherianRing R] (x : R) (hnormal : IsIntegrallyClosed R)
    [IsAdicComplete (Ideal.span ({x} : Set R)) R]
    [IsDomain (R ⧸ Ideal.span ({x} : Set R))]
    (hquot : IsN2 (R ⧸ Ideal.span ({x} : Set R))
      (FractionRing (R ⧸ Ideal.span ({x} : Set R)))) :
    IsN2 R K := by
  sorry
