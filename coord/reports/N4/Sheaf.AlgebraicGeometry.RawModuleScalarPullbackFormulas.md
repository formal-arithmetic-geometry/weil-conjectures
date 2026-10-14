## What changed

Deliver the assigned `Sheaf.AlgebraicGeometry.RawModuleScalarPullbackFormulas`
statement with its original sandbox signature unchanged. Its proof constructs a
conjunction from two independent components in new modules:
`Sheaf.AlgebraicGeometry.RawModuleScalarPullbackModuleFormula` and
`Sheaf.AlgebraicGeometry.RawModuleScalarPullbackAbelianFormula`. The abelian
component is proved by symmetric `Category.assoc`; the module component is a
named, documented hole. Both component imports in the assigned module are
private; all public imports provide names in the statements.

The assigned source and its node are absent from the repository snapshot.
The source-factor and coefficient-factor modules now exist in the repository;
this delivery restores neither prerequisite. The sandbox coefficient-square
file was byte-for-byte identical to the repository and was removed from the
set. No existing definition, statement, or target is changed. The public
interface addition is recorded in `coord/changes/pullback-formula-split.md`.

## Proved and sorry left

The assigned declaration
`AlgebraicGeometry.Etale.rawModuleScalar_pullback_formulas`
(node `lem-sbc-raw-scalar-pullback-formulas`) has a complete conjunction proof.
Its intended upper hole is replaced by one strictly smaller lower hole:
`AlgebraicGeometry.Etale.rawModuleScalar_pullback_module_formula`
(node `lem-sbc-raw-scalar-pullback-module-formula`). This is a decomposition,
not a net decrease in holes. Since the assigned source is absent from the
current source snapshot, no source-baseline hole closure is claimed.

`AlgebraicGeometry.Etale.rawModuleScalar_pullback_abelian_formula`
(node `lem-sbc-raw-scalar-pullback-abelian-formula`) is proved independently of
any module class. It has no hole. The module component is the only `sorry`
in the delivered sources; no hole is inside a definition or private helper.
Upstream holes remain in the import closure and no sorry-free closure is claimed.

## No longer needed

No existing node or module is claimed pruned globally. There is no existing
assigned source or proof-dependency list in this snapshot to remove from.
The source-square and coefficient-square coherence theorems are not used by
this formula expansion. `RawModuleScalarSourceFactors` supplies the source
factor definitions; `RawModuleScalarCoefficientSquare` remains necessary for
the coefficient definitions. New nodes cite `def-sbc-raw-scalar-source-factors`
rather than the source-square theorem for their source definitions.

The module component does not import `RawModuleAbelianHomMap`, since its
statement uses no abelian class. The component proofs use the definitions
and associativity, and the conjunction uses precisely the two components.
The redundant sandbox coefficient-square file and generated probe are not
part of the delivery. No experimental dependency definitions are delivered.

## Where the brief, the DAG or earlier work was wrong

The previous report described restoring two missing prerequisites and their
nodes, but the current snapshot contains both prerequisites and this sandbox
contains neither restored node. Those obsolete restoration claims are removed.
The assigned source and node remain absent, so comparison with an existing
repository signature is impossible. All three delivered signatures match
their node records verbatim and were preserved during this reading.

The sandbox had stale compiled artifacts for modules outside the delivery,
including experimental raw-triangle and abelian-comparison dependencies.
The entire sandbox `.lbuild` was cleared before validating the delivery
against the published library. Scratch sources stay outside the delivered set.

Direct module expansion was attempted during this reading: the generic
associativity application needed the bundled functor map and class type
expanded first, and the explicit expansion then exceeded the 60-second
single-file limit. The original documented module component is retained,
without experimental proof options or definition changes.

The new statements are exactly the two independent conjuncts, with the
abelian statement omitting the unrelated module-class parameter. Their
calculations work for degree zero, zero classes, and identity arrows: they
only evaluate fixed maps and regroup composition, with no nonvanishing,
affineness, invertibility, or relation between the classes assumed.

## New nodes

`lem-sbc-raw-scalar-pullback-module-formula` gives only the module factorization.
Its docstring and node describe evaluation of the raw Over functor, expansion
of raw triangle pullback and coefficient comparison, then associativity.
It is the only split hole, in its own new module.

`lem-sbc-raw-scalar-pullback-abelian-formula` gives only the arbitrary abelian
factorization, independently of a module class. Symmetric `Category.assoc`
proves it from the concrete source and coefficient definitions.

`lem-sbc-raw-scalar-pullback-formulas` records the assigned conjunction and its
proof from the two independent components. The statement is unchanged from
the supplied sandbox. The change record is
`coord/changes/pullback-formula-split.md`.

## Second reading by N4

1. Compared every delivered source with the repository paths. All three
formula modules are absent from the snapshot, so no existing signature can
be compared byte-for-byte there. Each delivered signature matches its node's
`lean.statement` byte-for-byte and the supplied sandbox signature is unchanged.
The coefficient-square source was identical and is excluded. No existing
statement, definition, or target is modified. Verdict: no accidental interface
change; the declared additions have their change record.

2. Read all delivered sources and their factor definitions. The only hole is
`rawModuleScalar_pullback_module_formula`, a named public theorem with a full
source and natural-language proof and matching node. No forbidden declaration
or hollow definition occurs. Validation uses a clean sandbox build against
the published library, then the delivery tool's declaration-wide axiom probe.
Verdict: the abelian proof is real associativity, and the upper proof is a
real conjunction reduction, with the one documented lower hole.

3. The module component is exactly the first conjunct; the abelian component
is the second conjunct and does not assume the module class exists. Both are
strict parts of the argument, not restatements of the conjunction. Read
`higherDirectImageRawOverFunctor`, `higherDirectImageRawOverPullbackHom_apply`,
`higherDirectImageRawOverPullback`, `rawTriangleMap`, the raw Over coefficient,
and the abelian raw pullback. Their fixed factors match the formulas; degree
zero, zero classes, and identity arrows require no extra hypotheses. Repeated
Loogle, LeanFinder and grep searches with different wording; the generic
match is `Category.assoc`. Local `rg` found the evaluation lemma and concrete
maps, but no existing complete factorization. LeanSearch returned an Internal
Server Error and is recorded as unavailable, without a negative verdict.
Verdict: true, independently necessary components, with no duplicate found.

4. Read the unit `sk-lem-failure-field` and its `realized` field (empty statement
and step lists). This calculation realizes a lower-level explicit map expansion
and bypasses no realized unit step. Public imports supply statement definitions;
only the two component imports in the upper module serve its proof and are
private. No coherence theorem is used in the factorization. The report claims
no global pruning and makes no net progress claim for the decomposition.
Verdict: route preserved and dependency accounting explicit.

5. Checked each node's Lean declaration, module, exact signature, chapter,
unit, source, docstring, proof steps, origin, and union of `uses` as `proof_deps`.
The upper proof depends on exactly the two component nodes; the abelian proof
is elementary expansion and associativity; the module plan evaluates the raw
diagram. Corrected the definition citation from the source-square theorem to
`def-sbc-raw-scalar-source-factors`. Verdict: DAG and delivered Lean agree.

Changed the inaccurate report and change record, corrected new-node definition
citations, removed the redundant coefficient-square delivery and stale probe,
and cleared stale compiled dependencies. Tried closing the module component
within a few minutes, then restored its original hole after the compile limit.
No theorem signature or definition was changed.

Explicit `#print axioms` validation of the compiled declarations succeeded:
`rawModuleScalar_pullback_abelian_formula` uses only `propext`,
`Classical.choice`, and `Quot.sound`. The upper conjunction and the module
component use those axioms and `sorryAx`, exactly as expected from the named
module-component hole. No other axiom was reported. The scratch copy with
appended commands exceeded 60 seconds; the successful check imported the
same locally compiled declarations into a small scratch module instead.
All three delivered files compiled in the delivery dry run.
