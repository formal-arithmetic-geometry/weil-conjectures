## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.integralLocalizing_properBaseChange`
in `lean/Sheaf/Paper/IntegralLocalizingProperBaseChange.lean`, preserving its full
signature and all public imports. The two endpoints are obtained by composing
localizing preservation for proper direct image and inverse image. The specified
canonical exchange is invertible on admissible Dctf generators, and the existing
unbounded extension proof extends this to the closure. The extension module already proves triangulatedness of the actual exchange
isomorphism locus and preservation of sums by its two functors. Its proved core
`extend_iso` applies directly to this map, so no termwise change of presentation
is needed.

Two proved private coefficient helpers identify an arbitrary embedded finite extension with
its finite field-range representative, including the induced topology on its
integer ring and the actual continuous-function condensed ring object. Their
code follows the private helpers of
`Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded`; that module cannot
be imported because it already depends on this item. No data is obtained from an
unproved existence theorem. The main theorem uses a local
400000-heartbeat elaboration budget for the inherited derived structures; the
compile-time limit is unchanged. The exchange and derived-functor definitions
are locally irreducible to prevent incidental expansion of their large bodies.

Proof-only `import all` accesses the already proved coefficient-isomorphism
transport, the coefficient-independent inverse-image preservation construction,
and the proved core of the existing conditional localizing-extension argument. The declaration
`properBaseChange_admissible_generators` is an existing named theorem with a
DAG node; it supplies only the bounded-generator case, strictly below this item's
localizing assertion. Its coefficient-isomorphism clause handles the arbitrary
embedded E in the unchanged statement. The generic extension and preservation
proofs already establish shift compatibility and coproduct preservation.

Updated only this item's DAG proof, proof dependencies, proof origin and obsolete
top-level tool approvals. No other existing module or node is changed.

## Proved and sorry left

Closed one of one holes:
`AlgebraicGeometry.ProEtale.CondensedRing.integralLocalizing_properBaseChange`
(node `det-thm-sf-pf-adic-base-change`). No `sorry` remains in the item. No holes
were added and no statements were split off.

The proof uses the existing, still unproved
`AlgebraicGeometry.ProEtale.CondensedRing.properBaseChange_admissible_generators`
(node `lem-sfb-proper-base-change-admissible-generators`); that theorem is not
changed or duplicated. This delivery proves the item from the stated library
dependencies, and does not claim their transitive axiom closure is complete.

Validation: the final clean compile passed in 28.9 seconds with no warnings
(`lcompile.py`, profiling options removed). The earlier profiled compile passed
in 22.7 seconds. The source signature is unchanged
byte for byte, all delivered Lean lines are at most 100 characters, and the
coefficient helpers construct their data explicitly. The proof covers zero
complexes, empty schemes, arbitrary non-flat g, and sums without a completeness
assumption: all preservation and extension results apply to the ordinary
unbounded category and exactly the source localizing property.

## No longer needed

Removed these unused proof-only imports (including the duplicate finite-coefficient
import):

- `Mathlib.CategoryTheory.Adjunction.Mates`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `Sheaf.Paper.IntegralFinitePullbackComposition`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`
- `Sheaf.Paper.CartesianCoefficients`
- `Sheaf.Paper.CondensedModuleDerivedPushpull`
- `Sheaf.Paper.IntegralProperBaseChange`
- `Sheaf.Paper.LocalizingAdmissibleCoefficients`
- `Sheaf.Paper.IntegralModels`

The proof imports of `UnboundedBaseChangeExtension`, `UnboundedLocalizingPullback`
and `ProperImageLocalizingProper` are retained as `import all` to access their
proved generic constructions. All public imports are preserved.

The following nodes are no longer direct proof dependencies:

- `def-sfb-finite-lower-star-comp`
- `def-sfb-module-lower-star-comp`
- `def-sfb-module-upper-lower-adjunction`
- `def-sfb-module-upper-star`
- `def-sfb-module-upper-star-comp`
- `def-weil-pbc-adjunction-conjugate`
- `def-weil-pbc-ambient-ringed-exchange`
- `det-thm-sfb-proper-base-change-integral`
- `lem-weil-pbc-proetale-derived-pullback-composition`
- `sk-def-sfb-dc-setting`
- `sk-def-sfb-derived-categories`
- `sk-def-sfb-module-derived-pushpull`
- `sk-lem-integral-models`
- `sk-prop-sfb-cartesian-coefficients`

The explicit underived and derived composition comparison checks are handled by
the actual-exchange isomorphism-locus and composite-coproduct lemmas of the
extension module. `LocalizingClosureCtfEqualsBc` supplies exactly the closure
equality, so the much larger `IntegralModels` theorem and its extra clauses are
not directly needed. The existing admissible-generator theorem supplies the
bounded exchange rather than restating the coefficient-transport glue. These
are removals from this item's direct route, not claims that the corresponding
modules have no consumers elsewhere. No module is withdrawn.

Removed the obsolete top-level tool approvals for:

- `sk-lem-integral-models`
- `det-thm-sfb-proper-base-change-integral`
- `sk-prop-sfb-cartesian-coefficients`
- `sk-def-sfb-derived-categories`
- `lem-weil-pbc-proetale-derived-pullback-composition`

## Where the brief, the DAG or earlier work was wrong

The original plan did not explicitly bridge the arbitrary embedded coefficient
field in this item's Lean signature to the finite-intermediate-field arguments
of the unbounded extension theorem. The field-range isomorphism is now constructed
and its continuous integer-ring map is checked directly.

The current extension module already proves that the actual ambient exchange
has triangulated isomorphism locus and that its two functors preserve the needed
sums. Using its proved `extend_iso` core directly avoids a redundant change to
the termwise presentation; the old separate Hom-comparison steps are unnecessary
at this call site.

`lem-sfb-proper-base-change-admissible-generators` is used as a tool for precisely
the bounded-generator case; `det-def-localizing-closure-ctf-equals-bc` is used for
its coefficient-isomorphism-invariant closure equality.
`det-def-localizing-closure-existence` supplies the actual localizing-subcategory
structure required by the generic extension core. Their existing statements
avoid new helper sorries. These replace lower-level glue, while preserving the
blueprint's bounded integral base case, proper coproduct estimates and localizing
determination route. The unit record `dag/units/sk-thm-sf-pf-adic.json` is the stale
old projection-formula unit already noted in this item's independent review; it
has no realized nodes. It is not changed.

The rework record mentions the now-unused source projection-formula import through
older dependencies. The current item source was present, and its declaration and
Lean attachment are preserved. No quarantine file is removed.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
