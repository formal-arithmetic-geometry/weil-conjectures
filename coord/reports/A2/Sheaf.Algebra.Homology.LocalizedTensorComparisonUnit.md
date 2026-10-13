## What changed

Closed `ModuleCat.localizedTensorComparisonProperty_unit` without changing its statement,
visibility, options, or public import. Added proof imports of
`Sheaf.Algebra.Homology.BaseDerivedTensorModelQuasiIsoComparison` and the new
`Sheaf.Algebra.Homology.LocalizedTensorComparisonRepresentativeSquare`.

The canonical unit calculation is written in Lean: the right unitor proves K-flatness,
ULift.moduleEquiv identifies the specified generator, the left unitor gives the model
comparison, and monoidal naturality gives its comparison square. Cancellation proves
invertibility. A refined K-flat roof and two explicit comparison squares then transport
this result to every K-flat representative and every supplied model.

The new representative-square theorem is also fully proved. Its three private helpers
convert the two K-flat predicates and preserve quasi-isomorphisms under scalar extension.
The first and third follow the existing private implementations in
`KFlatScalarExtensionDerivedIso`; that module's public theorem forgets the naturality
square, so it cannot replace the needed argument. The proofs reuse the same existing
mixed-tensor theorem and source-library resolution construction.

Both delivered modules compile cleanly through lcompile.py. No global build was run.
The node records now follow the formal proof.

## Proved and sorry left

Closed: `ModuleCat.localizedTensorComparisonProperty_unit`
(node `lem-pc-localized-tensor-comparison-unit`), the sole original hole.

Added and proved: `ModuleCat.exists_localizedTensorComparison_representative_square`
(node `lem-pc-localized-tensor-comparison-representative-square`) and all three private
helpers. There is no sorry in either delivered module, and no hole was added or split off.
This is a proof from existing library declarations, not a claim that their entire
transitive dependency closure has been proved in this delivery.

## No longer needed

None. The original public import supplies the statement's predicate and remains needed.
The DAG previously named only the predicate and model definitions; neither can be pruned.
No other planned proof module was imported, and no unit route was bypassed.

## Where the brief, the DAG or earlier work was wrong

The original prose plan is sound but its proof dependencies list only definitions, so it
does not supply declarations for representative transport. Existing model quasi-isomorphism
comparison, mixed K-flat tensor invariance and scalar-extension K-flatness provide the
missing ingredients. The new square records their composition and is proved here.

Edge cases checked against the argument: zero coefficient rings, zero complexes, arbitrary
unbounded complexes, identity derived isomorphisms, and nonflat C or N. The proof uses only
K-flat roof legs for tensoring with arbitrary N; it never assumes ordinary extension of an
arbitrary quasi-isomorphism preserves cohomology. Model and flat-resolution witnesses occur
only locally in proofs of propositions; no public data is chosen from an unproved existence
statement. All original signatures and public imports remain unchanged; no adaptations are
needed.

The local literature tex files were absent. Read the official Stacks pages for
[0DJA](https://stacks.math.columbia.edu/tag/0DJA),
[064L](https://stacks.math.columbia.edu/tag/064L), and
[06Y1](https://stacks.math.columbia.edu/tag/06Y1), and the existing model-comparison declarations.
The ordinary-module resolution uses the proved source-library implementation, not the
sheaf-only KFlatResolution statement.

## New nodes

`lem-pc-localized-tensor-comparison-representative-square` states the comparison square for
any two K-flat A-complexes isomorphic in D(A), with arbitrary N and models. It assumes no
invertibility of the comparison, hence is a part of the original argument rather than a
restatement. Its entire proof is supplied in the new module. Sources are Tags 064L, 06Y1,
06Y6 and the representative-independence step of 0DJA(1). Logged LeanFinder, Loogle and grep
searches found ingredients; LeanSearch returned HTTP 500 and is recorded unavailable.
Blueprint search found no matching statement. The new node keeps the item's chapter, unit
and blueprint ancestor. There are no change records because no existing interface changed.

## Second reading by A2

1. **Statements and interfaces.** Compared the delivered item module with the repository
version. `ModuleCat.localizedTensorComparisonProperty_unit` has the identical signature,
visibility, and public import. The added representative-square declaration is a new
strictly intermediate result and does not alter an existing declaration.

2. **Proof and kernel checks.** Compiled both delivered modules with `lcompile.py --all`.
There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`
declarations in either file. The proofs use existing comparison, K-flat, resolution, and
monoidal naturality results; no data is defined from an undetermined existence witness.

3. **New statement.** Checked the representative-square theorem in the zero-complex and
identity-isomorphism cases, and against arbitrary `N` and nonflat `C`. It asserts exactly
the transport square needed by the unit proof and does not assume either comparison is an
isomorphism. Its node contains the source, proof steps, dependencies, searches, and exact
Lean statement.

4. **Pruning and dependencies.** The two proof-only imports in the item are necessary;
the predicate remains a public import. The representative module's imports are used by
its proof. No old proof dependency is unused, and the unit's realized route through the
unit comparison and representative transport is preserved.

5. **DAG agreement.** Updated node proof steps and dependencies match the declarations
actually used. The item node still records the original target statement and the new node
records the intermediate theorem; no target or existing public signature was changed.

Changed during this second reading: added this required review section only. No Lean code,
statement, definition, or DAG content was changed.
