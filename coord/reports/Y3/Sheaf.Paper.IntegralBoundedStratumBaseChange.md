## What changed

Proved both theorems in `Sheaf.Paper.IntegralBoundedStratumBaseChange`, keeping all
public signatures, definitions and public imports unchanged. Added proved private helpers
for the actual mate equations, open essential-image base change, closed support detection,
and complementary base-change geometry. The locally closed comparison is the specified
open mate followed by the inverse closed mate, with its cancellation equation.

The proof uses existing arbitrary condensed-coefficient module APIs: open extension full
faithfulness and sheaf base change, the profinite-point forgetful pullback comparison,
condensed open/closed recollement for exact closed direct image, and the source library's
joint restriction detection. All bounds follow from exact derived functor cohomology.
The node's proof and dependencies now follow this route. No new nodes or holes were added.

Validation: both complete theorem proofs compiled through `lcompile.py` in 43.8 seconds.
The single style warning in that compile was repaired before delivery; unused private
instances were removed. The delivery command runs the final compile, axiom probe and
preflight.

## Proved and sorry left

Closed the two existing holes:

- `AlgebraicGeometry.ProEtale.IntegralBoundedStratumBaseChange.integral_bounded_open_closed_base_change`.
- `AlgebraicGeometry.ProEtale.IntegralBoundedStratumBaseChange.integral_bounded_locally_closed_base_change`.

Both belong to `lem-sfb-integral-bounded-stratum-base-change`. Holes added: zero.
Holes left in the delivered module: zero. Theorems use the library's existing
intermediate results, as required by stage 3.

## No longer needed

Removed the following private proof imports and their planned direct node dependencies:

- `Sheaf.AlgebraicGeometry.FiniteTypeNoetherianSpectrum`
  (`lem-sfb-finite-type-noetherian-spectrum`): quasi-compactness of the supplied opens
  follows from their structure maps; Mathlib's locally Noetherian finite-type theorem
  supplies quasi-compactness for the constructed complement.
- `Sheaf.Paper.CartesianCoefficients` (`sk-prop-sfb-cartesian-coefficients`): the
  source module pullback API already provides exactness for arbitrary condensed rings.
- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`
  (`lem-sfb-internal-module-operations-transport`): work directly with module objects.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
  (`lem-weil-pbc-proetale-ringed-open-closed`): direct condensed module recollement
  supplies the closed exactness and full faithfulness needed here.
- `Sheaf.CategoryTheory.ExactOpenClosedUnboundedCalculus`
  (`lem-sfb-exact-open-closed-unbounded-calculus`): use the existing exact-derived
  adjunction and joint-reflection APIs, without a new localization-sequence argument.
- `Sheaf.CategoryTheory.ExactDerivedComposition`
  (`lem-sfb-exact-derived-composition`): the source library already proves the canonical
  composition isomorphism used by the fixed definitions.
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`: available through the
  retained exact derived functor API.
- `Mathlib.CategoryTheory.Localization.Predicate`
  (`lem-sfb-exact-derived-natural-iso` as a separate planned dependency): use the source
  library's canonical proved `mapDerivedCategoryNatIso` directly.

Also removed the direct plan edges `lem-weil-pbc-open-immersion-base-change` and
`lem-weil-pbc-closed-immersion-base-change`: the square hypotheses already supply the
primed immersion instances, and Mathlib supplies those on the constructed complement.
The base-change image lemma is retained. Pruned the obsolete top-level `tool_uses`
approvals for the finite-type Noetherian spectrum lemma, internal-module transport,
ringed open/closed calculus, exact unbounded open/closed calculus, exact derived
composition, and exact derived natural isomorphism, in the original order. These are dependencies unused directly by this
proof, not assertions that their modules are globally unreachable. In particular,
transitive users in the retained library have not been changed or withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original seven-step plan was mathematically sufficient but required unnecessary
section-ring transport and a second derivation of open/closed calculus. Existing module
support and essential-image results yield the same actual mates on all unbounded inputs,
then restrict to bounded inputs. The unit's open/closed route and all target meanings
are preserved. The abelian base-change isomorphism in the source API permits arbitrary abelian
sheaves; the distinct DAG wrapper `lem-cbc-proetale-extension-zero-base-change`
has a finite-ring interface and is not imported or used here. Similarly, source module
joint reflection is used directly, not the separately stated ringed-module detection
interface. No statement or definition repair was needed.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
