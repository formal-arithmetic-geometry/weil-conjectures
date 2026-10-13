## What changed

Completed boundary_cech_local_lifts by choosing the canonical injective comparison
from cechH1_injective, then specializing boundary_cech_compatibility to the underlying
short exact module sequence. The same comparison works for every section and choice
of lifts. No data definition is introduced and no new theorem is left with sorry.

Corrected the displayed overlap differences from t₀ - t₁ to t₁ - t₀ to agree with
the existing module boundary compatibility interface. This is a recorded statement
correction, not a proof of the old signature. See
coord/changes/boundary-cech-local-lifts-sign.md for exact old/new signatures, all users,
and the convention issue requiring independent review. No target or definition changes.

Updated the node's statement, Lean record, proof route and dependencies. All public
imports remain; the unused proof-only SiteCechComplex import is removed.

Validation: the corrected item compiles without warnings (25.4 seconds in the set
check). The original BoundaryDerivationAlgebraicData and BoundaryDerivationSquareZero
modules compile unchanged against it (6.2 and 19.5 seconds). These checks were run
on scratchpad copies; neither downstream file is delivered. deliver3.py --no-push
printed OK and passed preflight except for the intentionally pending second reading.
Nothing was pushed.

## Proved and sorry left

The sole hole in AlgebraicGeometry.Scheme.Modules.boundary_cech_local_lifts
(lem-sc-boundary-cech-local-lifts) is closed for the corrected sign convention.
The original sign assertion is not claimed proved unchanged. Source-text holes removed: 1;
holes added: 0. This is an interface correction with a proof of the corrected statement,
not a proof of the original holed signature; it must receive CODEX review, not AUTO landing. No sorry remains in the item or is added by this delivery.

This is a proof from existing named statements, not an axiom-free end-to-end proof:
AlgebraicGeometry.Scheme.Modules.cechH1_injective and
AlgebraicGeometry.Scheme.Modules.boundary_cech_compatibility still have existing sorries
in their own modules. They are the required next items, not new holes or new nodes.

## No longer needed

Removed the proof-only import Sheaf.CategoryTheory.SiteCechComplex. The direct proof
no longer uses def-weil-pbc-site-cech-complex: the compatibility theorem already
provides both the cocycle and its boundary equality. Its indirect use below that
compatibility theorem is retained, so no claim of whole-closure pruning is made.

Removed lem-sc-cech-h1-map-natural from the item's proof_deps: injectivity already
supplies a comparison certified by IsModuleCechComparison, and naturality is not
needed for the local-lift existence statement. The public import
Sheaf.AlgebraicGeometry.CechH1MapNatural remains as an existing statement/interface
import; its export scope is unchanged. No unit realization is bypassed: the item's
unit realizes only thm-sc-proper-cohomology, not this lower local-lift lemma.

## Where the brief, the DAG or earlier work was wrong

The original statement's sign is incompatible with its named lower compatibility
statement: one asks for t₀ - t₁ and the other gives t₁ - t₀ for the same canonical
map and boundary. [Stacks 0B8S](https://stacks.math.columbia.edu/tag/0B8S) explicitly writes t₀ - t₁,
so this is a library
convention/interface issue, not a claim that the Stacks formula is a typo. The
correction uses the lower theorem's documented convention; the second reader should
check it against ModuleCohomologyBoundary and BoundaryCechInjectiveMiddle.

The only DAG citer is lem-sc-boundary-derivation-square-zero-algebraic-data. Its
Leibniz statement is unaffected by simultaneous reversal of the three cocycles.
No existing Lean caller mentions the changed theorem, hence no forced adaptation.

Shorter-route searches: leanfinder found group-cohomology results, not this statement;
loogle ShortComplex.ShortExact returned no match; msearch grep found no replacement.
Repository searches found the existing general boundary compatibility and injectivity
statements, which suffice. No new theory or decomposition was needed.

Edge cases: for I=0 the cocycle and boundary are zero. For a one-open cover with
global lifts the boundary class is zero; an empty covering can only cover the empty
scheme and is still admitted. No nonempty-index or characteristic hypothesis was added.
The square-zero assumption is unused by this description, but is retained verbatim.

## Second reading by F2

1. **Interface comparison — recorded correction, no accidental change.** Read the full
repository and delivered module and their diff. The only signature edit reverses the two
restricted lifts; every binder, universe, hypothesis (including square-zero), comparison
predicate, injectivity clause and boundary formula is otherwise byte-for-byte identical.
The Old/New blocks of coord/changes/boundary-cech-local-lifts-sign.md match those signatures.
No definition or target changes. Re-ran downstream.py and searched all Lean sources:
only the two BoundaryDerivation modules import this item, and neither calls its theorem.
The sole logical DAG citer is lem-sc-boundary-derivation-square-zero-algebraic-data;
simultaneously negating alpha, beta and gamma preserves its Leibniz identity. Verdict:
acceptable as an explicitly recorded intermediate statement correction, not as an
unchanged-statement proof. The original signature remains unproved by this delivery.

Read [Stacks 0B8S](https://stacks.math.columbia.edu/tag/0B8S), its local-lift paragraph,
and [01EQ](https://stacks.math.columbia.edu/tag/01EQ), its alpha/beta construction.
0B8S indeed displays t0-t1. Independently inspected ModuleCechComparison,
ModuleCohomologyBoundary, BoundaryCechCompatibility and BoundaryCechInjectiveMiddle.
The comparison is constrained by H(beta) and H(alpha), not an arbitrary injective map;
the boundary is the image of singleTrianglePlus, not a chosen homomorphism.
For the lower theorem's resolution J with J0=I and quotient section qtilde in J1,
its split resolution of the middle term has differential (da-b,-db) and augmentation
b -> (b,db). A lift (0,qtilde) has differential (-qtilde,0), so the snake boundary is
-[qtilde]. The total differential of the local lifts is beta(z)+alpha(qtilde),
so c[z]=-[qtilde] when z has differences t1-t0. This checks the signs in words;
it does not close the existing lower proof obligations. The correction changes the
local representative convention and introduces no extra geometric assumption.

2. **Proof and axioms — pass with existing dependencies open.** Compiled the item locally
without errors or warnings through lcompile.py. A scratch copy with #print axioms for
AlgebraicGeometry.Scheme.Modules.boundary_cech_local_lifts reports exactly propext,
Classical.choice, Quot.sound and sorryAx. Scanned the delivered Lean: no sorry, axiom,
unsafe, opaque, implemented_by or extern, and no new data definition. The existential
comparison is eliminated inside a proof of an existential proposition; no definition
chooses data from mere unproved existence. The two dependencies remain existing sorries,
not newly split holes. Original downstream copies are checked against the corrected
scratch module; no adaptations are delivered.

3. **Split statements — none.** No theorem or node was added, and no new sorry was
introduced. Reviewed the actual two cited statements: cechH1_injective supplies a family
of comparisons certified by IsModuleCechComparison and injective on every module;
boundary_cech_compatibility supplies both the ideal-valued cocycle and the boundary
identity for any fixed certified comparison. Specializing its short complex to j and
map p gives the same section carriers and restrictions definitionally. The zero kernel,
one-open cover, empty scheme/empty cover and characteristic two introduce no missing
hypothesis. No relabelled obligation or arbitrary comparison has replaced the item.

4. **Route and pruning — pass.** The proof fixes c I before introducing f and t, which
checks the uniformity quantifier. It then applies the general module theorem directly;
the algebra/square-zero special case needs no independent construction of a cocycle.
Independent search used msearch grep with connecting/Cech/boundary/lift phrases and rg
on both Lean roots; no shorter established boundary theorem was found. Proof-only
imports CechH1Injective and BoundaryCechCompatibility are plain imports. The removed
SiteCechComplex import is unused; No longer needed lists both old proof dependencies
not directly used: def-weil-pbc-site-cech-complex and lem-sc-cech-h1-map-natural.
The pre-existing public imports retain the existing exported interface and supply the
statement vocabulary. Read dag/units/sk-thm-curveestimate.json: its realized statement
is thm-sc-proper-cohomology and its realized steps are empty, so this lower specialization
bypasses no realized unit. No module is claimed pruned from the targets' whole closure.

5. **Nodes — repaired, then pass.** The two proof steps match the two applications in
Lean; their uses union is exactly proof_deps. proof_origin accurately labels this
specialization as the agent's route, with the Stacks source retained. statement_change
quotes the original statement and names the only logical citer with its preserved
Leibniz identity. Found literal backslash-u escape sequences inside lean.statement;
replaced that value with the verbatim normalized Lean signature. The preflight schema requires statement_change.by to have the form "<G> stage 2",
even for stage-3 corrections, so that existing schema label is retained. The report
and proof_origin identify this delivery as stage 3. No unrelated node fields changed.

Second reading changed only the node's recorded signature encoding, replaced the stale 164-importer Users table with the current two importers,
and clarified the report's corrected-sign proof accounting. The compiled proof was
already correct for its explicitly corrected signature and was left unchanged.
