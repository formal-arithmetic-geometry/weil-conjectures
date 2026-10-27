## Worker report

The delivery states `RestrictedSeries.affinoid_jacobian_certificate_regular` in
`Sheaf.RingTheory.AffinoidJacobianCertificateRegular`, using the published `RestrictedSeries.jacobianIdeal`. Its only declaration is the
theorem, whose proof is `sorry`, as required for stage 2.
The statement, source, and seven proof steps of the original node are unchanged.

Hypothesis and clause correspondence:

- The complete real-valued nonarchimedean field is `(F : Type u) [NormedField F]
  [IsUltrametricDist F] [CompleteSpace F]`. Nontriviality of its absolute value is
  `hF : ∃ a : F, a ≠ 0 ∧ ‖a‖ ≠ 1`, matching the existing affinoid comparison interface.
- Arbitrary nonnegative numbers of variables and equations are `(r s : ℕ)`.
  The field universe `u` is explicit and unrestricted. Auto-implicit binders are disabled.
- The ring T is precisely `MvPowerSeries.IsRestricted.subring` at constant polyradius one,
  with the inherited coefficientwise addition and finite Cauchy multiplication. Its cofinite
  coefficient-norm decay is equivalent to the stated finiteness for every positive ε.
- The equations are `f : Fin s → T`, I is `RestrictedSeries.relationIdeal f = Ideal.span (Set.range f)`, and B is the actual
  quotient `T ⧸ Ideal.span (Set.range f)`. All bars are `Ideal.Quotient.mk` for this ideal.
- Subsets are `E : Finset (Fin s)` and `U : Finset (Fin r)` with `h : U.card = E.card`.
  Indices `Fin E.card` enumerate both subsets increasingly by `Finset.orderEmbOfFin`.
  Rows use U and columns use E. `jacobianMinor` applies the recorded `Matrix.det` to
  `pderiv r (U.orderEmbOfFin h i) (f (E.orderEmbOfFin rfl j))`.
  This is the imported `RestrictedSeries.jacobianMinor`, not a local definition.
- I_E is `Ideal.span (f '' (E : Set (Fin s)))`. `Submodule.colon` applied to I_E and the
  underlying set of I is exactly `{a | a I ⊆ I_E}`, since scalar multiplication is ring
  multiplication. Its `.map (Ideal.Quotient.mk I)` is the image ideal in B.
- The imported `jacobianIdeal f` is the indexed supremum over E, U and h of that image ideal times
  `Ideal.span {Ideal.Quotient.mk I (jacobianMinor ...)}`. A supremum of ideals is their
  sum, so this is precisely H, including the principal B-factor in every summand.
- The sole certificate hypothesis is `hH : jacobianIdeal f = ⊤`.
  The conclusion is `IsRegularRing B`: by the recorded Mathlib ring clause of
  `def-weil-regular-scheme`, this includes `IsNoetherianRing B` and regularity of every
  prime localization. No reducedness, regularity, residue-separability, characteristic,
  perfectness or discrete-valuation hypothesis has been added.

Dependency declarations read and used:

- `def-weil-regular-scheme`: its scheme module
  `Sheaf.AlgebraicGeometry.IsRegularScheme` is imported publicly; the node's unchanged
  ring clause is `IsRegularRing` in `Mathlib.RingTheory.RegularLocalRing.Defs`, whose
  full class signature includes Noetherianity and regular local prime localizations.
  The scheme predicate itself is not substituted for this ring predicate.
- `def-weil-pbc-matrix-determinant`: `Matrix.det`, module
  `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`, with its finite-index Leibniz formula.
- Published dependency `def-per-restricted-series-jacobian`: public import
  `Sheaf.RingTheory.RestrictedSeriesJacobian`, declarations `RestrictedSeries.pderiv`,
  `RestrictedSeries.pderiv_isRestricted`, `RestrictedSeries.relationIdeal`,
  `RestrictedSeries.jacobianMinor`, and `RestrictedSeries.jacobianIdeal`. The complete live
  source and dependency node were read. This supplies all certificate data as real definitions.
- The published modules of all recorded proof dependencies are plain imports:
  `RestrictedSeries.affinoid_polynomial_closed_point_comparison`,
  `IsLocalization.isNoetherianRing`, polynomial-ring regularity,
  `AdicCompletion.isRegularLocalRing_iff`, `IsRegularLocalRing.of_ringEquiv`,
  `Matrix.adjugate_mul`/`mul_adjugate`, `IsRegularLocalRing.quotient_span_singleton`,
  the quotient-localization interfaces, `Ideal.exists_le_maximal`,
  `IsRegularLocalRing.localization_at_prime_and_isRegularRing`, and the successive
  localization interfaces. Localization and Noetherian definitions are also supplied by
  these modules. All seven proof steps, including these node identifiers and the residue
  derivation argument, appear in the main theorem's docstring.

Edge cases checked before writing:

- E = U = empty: `Fin 0` indexes the empty determinant, which is 1. The image of the empty
  subset under f is empty, hence I_E = 0; the colon is (0 : I), not silently omitted.
- s = 0: I = 0, E is empty, (0 : 0) is the unit ideal, so H is the unit ideal and the
  conclusion is regularity of the Tate algebra. Empty variables and relations are allowed.
- r = 0: only the empty U and empty E can have equal cardinalities; the algebra is a
  quotient of F, hence F or the zero ring. No nonempty finite-type instance is required.
- B = 0: no `Nontrivial B` binder is present. Its ideal lattice has top = bottom and its
  regularity class asks for no prime-local claims because there are no primes.
- Positive characteristic: the explicit formal derivative uses natural-number casts in F;
  the bound on integer norms and derivative coefficient decay require no characteristic zero.

Searches: the original prescribed msearch leanfinder query about a unit Tate-algebra
Jacobian colon certificate found ordinary polynomial submersive/standard-smooth
presentations, not this analytic criterion. Loogle `MvPowerSeries.pderiv, IsRegularRing`
returned no hits. msearch grep `IsRestricted|pderiv` in RingTheory/MvPowerSeries found
formal derivatives and the restricted subring. Those original searches predated publication
of `Sheaf.RingTheory.RestrictedSeriesJacobian`. On repair, the prescribed live-source lookup
now succeeds. Reading that full source shows exact existing constructions of the derivative,
minor, relation ideal and colon-minor sum, which are reused. The local source and DAG were
also searched with rg for `RestrictedSeriesJacobian|def jacobianMinor`. The old missing
notion and its extra definition node are no longer part of this delivery.

Source check: read Temkin Proposition 3.3.2 and the preceding definition of the colon-minor
Jacobian ideal online at the node's URL. The statement here follows the node's expressly
specified general analytic specialization; its coefficientwise regularity proof is retained.
There is no statement correction, known false edge case, or STATEMENT-DISPUTED flag.

Validation: the prescribed scompile.py compiles the only delivered module in both sandbox
and library mode against the live published dependencies, with no errors or warnings.
deliver2.py --no-push printed OK: the packet passes preflight and compiles
(dry-run commit 8ae1ffdf6ad); nothing was pushed by that dry run.

## Returned-delivery repair

Return L at immutable head a3a60566a4ee identified the duplicate
`RestrictedSeries.jacobianMinor`. This repair removes that declaration and imports
`Sheaf.RingTheory.RestrictedSeriesJacobian`. It also removes the duplicate certificate and
derivative constructions, including the previously proposed
`def-per-restricted-series-partial-derivative` node and its module. The theorem uses the
existing `jacobianIdeal f` directly, and cites `def-per-restricted-series-jacobian` in
stmt_deps. There is no renamed copy, alias or second proof of the same fact.

The current live item's non-Lean fields were compared with the returned sandbox packet:
the difference was only the old extra stmt_dep. The record was rebased onto that current
node before adding the published Jacobian dependency. The statement, source and seven
proof steps remain unchanged; the node's lean.declarations now contains only the theorem.
The new Lean signature is recorded verbatim, with the current UTC date.

The existing minor uses the equality `U.card = E.card`, opposite to the removed copy's
binder; the indexed pairs are the same and both enumerate rows U and columns E in
increasing order. Both termwise derivatives have exactly `MvPowerSeries.pderiv` as their
underlying series. The published `relationIdeal` is definitionally `Ideal.span (Set.range f)`,
so the quotient in the hypothesis is the quotient in the conclusion. The colon, image,
principal-ideal product, indexed sum, empty pair and zero quotient all match unchanged.

## Second reading by NW

A fresh author rereading checked every binder, the increasing row/column order, the colon
orientation and the quotient against the item and the full published dependency source.
No independent worker reading is claimed: the dispatcher prohibits starting other agents;
the maintainer's independent review reads this delivery.
