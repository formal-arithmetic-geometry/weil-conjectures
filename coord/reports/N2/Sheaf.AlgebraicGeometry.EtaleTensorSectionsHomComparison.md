## What changed

Reduced `AlgebraicGeometry.Scheme.Modules.nonempty_etaleTensorSectionsHomIso` to the
naturality of one explicit evaluation map. The pointwise bijection is proved in the item's
module using `unit_hom_ext`, `homOfGlobalSection_app_one`, and cancellation of the pullback
comparison isomorphisms. `NatIso.ofComponents` assembles the equivalences using the remaining
naturality theorem. The theorem signature and both existing public imports are unchanged;
one proof-only import of `Sheaf.AlgebraicGeometry.EtaleTensorHomEvaluationNaturality` was added.
The new module defines the actual comparison and evaluation map, with no postponed data.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.Modules.nonempty_etaleTensorSectionsHomIso`
(blueprint: `lem-sc-etale-tensor-sections-hom-comparison`) from the pointwise bijection and
restriction compatibility. No sorry remains in the item's module. One original hole is
closed and one lower hole is added: this is a decomposition, with net zero holes closed, not a complete proof of all
transitive dependencies.

One new sorry remains: `AlgebraicGeometry.Scheme.Modules.etaleTensorHomEvaluation_naturality`
in `Sheaf.AlgebraicGeometry.EtaleTensorHomEvaluationNaturality`, node
`lem-sc-etale-tensor-sections-evaluation-naturality`. This asserts only naturality of a fixed
explicit function, not its bijectivity or existence of a presheaf isomorphism.

## No longer needed

`import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction` was removed from the item as
redundant: `EtaleTensorSections` publicly imports that module, so its adjunction interface
remains available and used. No proof-dependency node or module is pruned from the import
closure. The separate `tensorPullbackObjUnitToUnit_isIso` interface, already excluded by the original node,
stays unnecessary: the proof uses the proved abstract `pullbackObjUnitIso`.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The unit `sk-prop-h2` has no realized nodes for this
auxiliary comparison, and its route is kept. The saved full compatibility attempt contains the generic
composition argument by conjugation, the unit equation on sections, and the scheme-level
restriction argument. Compiling the full and scheme-level attempts both hit the
single-file time limit in this session; changing transparency options in a scratch copy
also did not resolve it. These saved attempts are not verified full proofs. This delivery
keeps the restriction-compatibility step as a
named theorem with a complete natural-language proof rather than leaving an unfinished
proof in the item's module. The full Lean attempt is in sandbox scratchpad/FullAttempt.lean
for the second reader; scratch files are not part of the delivery.

## New nodes

`lem-sc-etale-tensor-sections-evaluation-naturality` records the restriction-compatibility
step of the original plan, in the original chapter and unit. The explicit evaluation is
well-defined without quasi-coherence. Identity arrows and empty schemes require no extra
hypothesis: adjunction identities, module linearity and restriction naturality cover both.
Searches found the upstream homSection and Mathlib conjugation interfaces but no complete
comparison for tensor pullback. No definition or existing statement changes. Both delivery
modules compile cleanly;
`deliver3.py --no-push` reports OK, deferring only the independent second reading. The new
definitions use the comparison uniquely determined by the adjunction units, and evaluate
a specified map; no arbitrary witness of mere existence supplies data.

## Second reading by N2

1. PASS: diffed both delivery modules against the read-only repository. The only existing
   declaration, `nonempty_etaleTensorSectionsHomIso`, retains its signature byte for byte.
   Its public imports and docstring are unchanged. The other module is new; there are no
   changed definitions or statements needing a change record.
2. PASS: independently compiled both modules in import order with `lcompile.py --all`
   (3.5 and 3.4 seconds), with no errors or warnings. Scratch copies with `#print axioms`
   confirm that both new definitions use only `propext`, `Classical.choice`, and
   `Quot.sound`; the naturality theorem and the assembled isomorphism also use `sorryAx`.
   The only delivered sorry is the named naturality theorem. No forbidden declaration
   or postponed data occurs. `exists_tensorPullbackAdjunction` is already proved and
   prescribes the unit on every section, determining the adjunction and its comparison.
3. PASS: the new naturality theorem is strictly the restriction-compatibility part of the
   argument; it does not assert bijectivity or existence of an isomorphism. Its docstring
   gives the conjugation, unit, section, and equality-transport argument, and its node
   matches it. Checked identity arrows, the zero module, and the empty scheme: evaluation
   and restriction remain defined, with the same adjunction equations and no nonempty
   hypothesis. Independent Lean Finder, Loogle, and grep searches used different queries;
   they found no exact duplicate. Mathlib's `pushforwardSections_unitHomEquiv` concerns
   pushforward sections, not compatibility of these two pullback comparisons. Upstream
   `homSection_comp` supplies the abstract restriction step, but does not compare it with
   `tensorSectionsComp`. No split-off statement could be closed by a short direct
   application of these existing results.
4. PASS: reviewed the pointwise injection and explicit surjection before the naturality
   step. Both use already proved library interfaces, and `NatIso.ofComponents` combines
   them with the remaining compatibility statement. All delivered imports support
   signatures, definitions, or the proof; the new module's public imports support its
   public evaluation signature. The removed direct adjunction import is redundant via
   `EtaleTensorSections`. Both old proof dependencies remain used, so no dependency node
   or module is pruned. Read `dag/units/sk-prop-h2.json`: its `realized` fields are empty,
   and this auxiliary decomposition does not change its Kummer route.
5. PASS: checked both node records against the definitions, theorem signatures, and
   proof as written. The existing node changes only `proof`, `proof_deps`, and
   `proof_origin`; its new dependency is the naturality node. The new node has its
   statement dependencies, source, complete proof plan, search evidence, creation,
   blueprint, chapter, unit, and verbatim Lean signature. Its proof dependencies are the
   union of its steps' uses.

Second reading changed only this report and the new node's independent search evidence;
no Lean repair was necessary. The result remains a decomposition: one original hole
closed, one strictly lower naturality hole added, net zero holes closed. The saved
full attempt is not claimed as a verified proof and is excluded from delivery.
