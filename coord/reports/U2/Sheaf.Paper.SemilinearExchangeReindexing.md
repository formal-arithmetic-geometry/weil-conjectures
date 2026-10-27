## What changed

Filled `WeilConjectures.semilinearExchangeReindexing` by assembling the existing finite
mate normalization, finite coherence, strict integral normalization and scalar/refinement
descent declarations. The finite normalization, agreement, identity, horizontal and
vertical composition, invertible composition, and finite-coefficient clauses specialize
those declarations with no extra hypotheses. The six strict integral clauses are the
six conjuncts of `purStrictIntegralExchangeNormalization`.

The completed-reindexing clause and proper square use the new coefficient-presentation
specialization `purCompletedReductionReindexingLifted`. For the integral exchange, the proof
uses the proper and open completion-unit invertibility supplied by the strict
normalization. The ordinary reindexing exchange is invertible as the composite of the
proper mate and the proper image of the open isomorphism. The normalized total equation
and cancellation of the source completion unit then prove invertibility of the actual
completed compact-support exchange. The scalar theorem takes precisely the already
established finite and strict integral clauses; direct projections of its six outputs
finish the conjunction.

Moved six existing descent predicates to
`Sheaf.Paper.SemilinearExchangeDescentData`, publicly re-exported by the item. Changed
`Sheaf.Paper.IsomorphismExchangeScalarRefinementDescent` to import this definition module
in place of the assembly. This removes its import cycle with the assembly, with no changed
statement. The composition-isomorphism predicate in
`SemilinearExchangeReindexingData` now names a one-field Prop structure. Its field
has precisely the type of the existing `FiniteExchangeCoherence.compositionIsIso`
declaration, obtained by `type_of%`. This retains the entire quantified assertion
and avoids nested proof extraction inside its large derived-category types.
Its separate change record is
`coord/changes/U2-semilinear-finite-composition-predicate.md`.
Four moved predicates and the two retained integral predicates share the
coefficient datum by a local let; zeta reduction gives their original bodies. This avoids
repeated elaboration of large coefficient and derived-functor terms. Change record:
`coord/changes/U2-semilinear-exchange-descent-predicate-module.md`.

## Proved and sorry left

Closed the one original hole: `WeilConjectures.semilinearExchangeReindexing`
(`lem-pur-weil-semilinear-exchange-reindexing`). The item's final proof has no `sorry`.

Added and proved the smaller specialization
`AlgebraicGeometry.Scheme.purCompletedReductionReindexingLifted`
(`lem-pur-completed-reindexing-lifted-coefficients`). The existing completed-reindexing
proof has coefficient-independent helpers `reindexingAt` and `reindexingSquare`.
Reusing their proofs from the public module, limit and mate declarations closes both
the lifted pointwise clause and every supplied Cartesian square clause directly.
There are zero holes added and no split-off holes left.

Validation: `lcompile.py` accepts the assembly, both definition modules and the
adapted scalar-descent module together. The fully proved lifted specialization
also passed its separate file check and its delivery compile. The complete-packet
compile is blocked by the stale-parent/new-owner mismatch described below; nothing
was pushed.

The adapted scalar-descent module has three pre-existing holes, unchanged:
`WeilConjectures.isomorphismExchangeScalarRefinementDescent`,
`WeilConjectures.isomorphismExchangeScalarComparison`, and
`WeilConjectures.isomorphismExchangeCommonStage`, all attached to
`lem-pur-isomorphism-exchange-scalar-refinement-descent`. These are not new holes.
The other five declarations were proved by a concurrent delivery; this packet preserves
those proofs and changes only the module's import.
Both definition modules have zero holes. The expensive finite composition, coefficient datum
and derived-functor constructions are kept locally irreducible during elaboration. A private
coefficient-independent cancellation lemma checks the proper/open composition and
completion-unit cancellation directly. Large integral normalization predicates are
opened explicitly only when their functions or conjunctions are used; this prevents checking the assembly from expanding their construction bodies.

## No longer needed

No module is withdrawn. All five planned argument blocks remain.
The canonical composition predicate reuses the type of the already needed finite
coherence theorem; it adds no mathematical dependency.
The original scalar-descent import of `Sheaf.Paper.SemilinearExchangeReindexing` is replaced
by the definition-only `Sheaf.Paper.SemilinearExchangeDescentData`; it never used the
assembly theorem. The new specialization uses the original completed-reindexing proof’s module,
limit and mate dependencies directly. Its public imports name their definition owners. No source-library declaration is removed or weakened.

The unlifted theorem of `lem-pur-isomorphism-completed-reduction-reindexing` is not
applied directly: its coefficient universe does not fit. The lifted specialization
reuses that theorem's coefficient-independent module, limit and mate proof route.
The original module remains publicly imported, and no withdrawal is requested.

The assembly removes eight redundant direct public imports, all still re-exported
by the new data module: `PurityFiniteSetting`, `ChosenCartesianSquare`,
`RefinementCategory`, `ExchangeProjectionSuppliedDomains`,
`IsoSectionwiseInverseImage`, `CompletedCompactSupportExchange`,
`ExchangeFunctoriality`, and `SemilinearExchangeReindexingData` (with their existing
namespace prefixes). This changes no public import closure and prunes no module.

## Where the brief, the DAG or earlier work was wrong

Resumed check, 2026-10-25 23:45 UTC: the required initial delivery check again
exited 1, with nothing pushed. Its assembly import failed on the same duplicate
`AlgebraicGeometry.Scheme.PurCompletedReindexingSquare`, attributed to the old
`PurCompletedReductionReindexing` artifact while importing the unpublished
`PurCompletedReindexingData` artifact. All five unpublished dependencies still
report source revision `7326d1e715f8f7001c779911c62864a6ba0053d3`.
The current parent source publicly imports the data owner at line 17 and does
not define the predicate; the current data source defines it at line 400.
This confirms the inconsistent compiled dependency environment remains.
The retained Lean proofs and nodes are preserved without changes; the only
three textual holes in the packet remain the pre-existing scalar-descent holes
listed above. A consistent published dependency build is still required.

Resumed check, 2026-10-25 23:43 UTC: the required initial `deliver3.py U2
Sheaf.Paper.SemilinearExchangeReindexing` check exited 1 without pushing. It again
accepted the lifted specialization, both data modules and scalar-descent module,
then failed at line 1 of the assembly on the duplicate declaration import quoted
below. The five unpublished dependencies again came from
`7326d1e715f8f7001c779911c62864a6ba0053d3`. Current source inspection verifies
`PurCompletedReductionReindexing.lean:17` publicly imports
`PurCompletedReindexingData`, whose line 400 defines the square predicate;
the parent no longer defines it. The landed change record
`coord/changes/pur-completed-reindexing-data-relocation.md` confirms this ownership
relocation. The compiled parent still owning that same declaration is inconsistent
with these sources. The retained proof packet is unchanged; no tools, dependency
sources or compiled artifacts were modified to bypass the failure. Validation
requires the launcher/maintainer to publish a consistent dependency build.

Resumed check, 2026-10-25 23:42 UTC: the required initial delivery check again
exited 1 without pushing. It accepted the lifted specialization, reindexing data,
descent data and scalar-descent module, then rejected the assembly's imports with
the same duplicate `AlgebraicGeometry.Scheme.PurCompletedReindexingSquare` error.
Its log again compiled the five unpublished dependencies from
`7326d1e715f8f7001c779911c62864a6ba0053d3`. Current source inspection confirms
`PurCompletedReductionReindexing` publicly imports the definition owner at line 17;
the definition itself is only in `PurCompletedReindexingData`, at line 400.
The old parent artifact and new definition-owner artifact therefore remain
inconsistent. No Lean source, tool or artifact was changed to force a rebuild or
work around this environment failure; all retained proof work is preserved.

Resumed check, 2026-10-25 23:40 UTC: the required initial `deliver3.py` invocation
returned the same compile-environment failure below (exit 1, nothing pushed).
The current shared sources still confirm the ownership mismatch: line 17 of
`PurCompletedReductionReindexing.lean` publicly imports `PurCompletedReindexingData`,
and only the latter defines `PurCompletedReindexingSquare` (line 400).
The import error nevertheless attributes that declaration to the former compiled
module. The retained Lean packet was not changed merely to invalidate the compile
cache or force a dependency rebuild. Fixing or republishing the inconsistent
dependency artifacts belongs to the launcher/maintainer; the worker brief forbids
patching the tools or working around their compile environment.

The delivery tool has a compile-environment failure. `deliver3.py U2
Sheaf.Paper.SemilinearExchangeReindexing` compiled all four dependency files,
including the fully proved lifted specialization, but rejected the assembly import:

```text
import Sheaf.Paper.PurCompletedReindexingData failed, environment already contains
'AlgebraicGeometry.Scheme.PurCompletedReindexingSquare' from
Sheaf.Paper.PurCompletedReductionReindexing
```

The tool compiled unpublished `PurCompletedReindexingData` and four leaf modules
from source revision `7326d1e715f8f7001c779911c62864a6ba0053d3` in its private overlay,
but retained the published parent artifact that still owns these definitions.
The current parent source instead publicly imports the definition owner and contains
no definition of `PurCompletedReindexingSquare`; the only current source definition
is in `PurCompletedReindexingData`. The published build stamp is
`2026-10-25T20:08:51Z`. This mixes two definition-ownership layouts. The assembly and
its repaired data/consumer set compile against the old published layout; the lifted
specialization compiles against the new definition owner. The tools need a consistent
parent/child environment to validate the whole packet. No tool, published artifact,
or unchanged dependency source was patched to bypass this failure.

The original finite-composition predicate stored its large law in a definition body.
Lean extracted new nested proof constants in its derived-category input type, making
kernel comparison with the existing coherence theorem expand the category construction.
The one-field Prop representation keeps the canonical law as a constructor argument type;
its isolated proof checks in 6.1 seconds under the diagnostic budget.

The scalar-descent dependency owned its output predicates in its consumer module, creating
an import cycle when one tries to follow the assembly plan. The existing definition-owner
node is now attached to the separate module containing exactly its six definitions.

The stated completed-reindexing theorem uses the unlifted valuation ring in universe
u+1, whereas the assigned theorem uses the lifted valuation ring of an extension in
universe u. Its square clause also produces some chosen Cartesian identification,
whereas the assembly needs every supplied one. Its newly proved helpers, however,
are coefficient-independent and apply to each supplied square.
The new module reuses the generic helper proofs through their published module,
limit and mate declarations, and then specializes them. No private declaration names
or source-library changes are needed. No equality of coefficient presentations or
arbitrary choice of Cartesian identification is needed.
Identity maps, zero objects and unchanged quotient indices are included.

## New nodes

`lem-pur-completed-reindexing-lifted-coefficients` states precisely completed reindexing
and the normalized direct-image square for the lifted datum. Its proof specializes the
existing coefficient-independent completed-reindexing helpers.
The existing reindexing-definition node also owns the new one-field representation.
The existing descent-definition node moves its Lean attachment, and the assembly node's
proof now names this specialization explicitly. The unit route is retained.
Change records: `coord/changes/U2-semilinear-exchange-descent-predicate-module.md`
and `coord/changes/U2-semilinear-finite-composition-predicate.md`.

## Forced adaptations

### Sheaf.Paper.IsomorphismExchangeScalarRefinementDescent
Forced (import cycle; reviewer correction of the tool line "NOT FORCED"): the original publicly imports Sheaf.Paper.SemilinearExchangeReindexing, which now imports this module for isomorphismExchangeScalarRefinementDescent, so the original cannot be compiled with the assembly. Changed line: `public import Sheaf.Paper.SemilinearExchangeReindexing` → `public import Sheaf.Paper.SemilinearExchangeDescentData` (the six predicates it uses, moved verbatim). Every declaration and signature unchanged; holder unclaimed.

### Sheaf.Paper.SemilinearExchangeReindexingData
Unclaimed data module of def-pur-semilinear-exchange-reindexing-data (created for this item). PurSemilinearFiniteCompositionIsIso now names the one-field Prop structure PurSemilinearFiniteCompositionLaw, whose field type is that of FiniteExchangeCoherence.compositionIsIso, the same quantified law as the old body; see coord/changes/U2-semilinear-finite-composition-predicate.md. Its only user is the item.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Reviewer corrections

The assembly node keeps its base stmt_deps (a stage-3 stmt_deps change without a statement correction is refused by the merge check); def-pur-semilinear-exchange-descent-data is recorded in its proof_deps and step 5 uses instead. The two definition nodes keep `proof_origin: null`. The new node cites def-weil-pbc-cartesian-square for ChosenCartesianSquare. `#print axioms` of both proved theorems shows sorryAx only through the still-sorried upstream statements (scalar-refinement descent; the module, limit and mate leaf lemmas).
