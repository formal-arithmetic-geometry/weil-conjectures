## What changed

Proved `Algebra.exists_stabilized_presentation_localized_conormal_basis` in
`Sheaf.RingTheory.SmoothStableConormalBasisAux` without changing its signature.
Added the fully proved module `Sheaf.RingTheory.ZeroVariableConormalStabilization`
and its theorem `Algebra.exists_zero_variable_presentation_localized_cotangent_equiv`.
The item imports that theorem and Mathlib's localization base-change and unit basis
rescaling APIs as proof-only imports. The new module constructs zero-variable
presentations, uses the composed-conormal exact sequence with an explicit retraction,
and then reindexes and tensors the resulting equivalence. Updated both proof plans
and docstrings to describe the Lean argument.

The source read was [Stacks Tag 07EZ](https://stacks.math.columbia.edu/tag/07EZ),
proof (e), stabilization and selection of numerator relations. The local source is
absent on this machine. Mathlib's exact sequence, submersive conormal equivalence,
and tensor APIs supply the detailed stabilization argument.

## Proved and sorry left

Closed the one original hole:
`Algebra.exists_stabilized_presentation_localized_conormal_basis`
(node `lem-weil-pbc-smooth-stable-conormal-basis-unbounded`).
Also fully proved `Algebra.exists_zero_variable_presentation_localized_cotangent_equiv`
(node `lem-weil-pbc-zero-variable-conormal-stabilization`).
There are no remaining or added `sorry`s, including in the three private construction
helpers. This is a proof, not a decomposition into unproved statements: holes closed 1,
holes added 0, split off 0. Both modules compile cleanly through `lcompile.py --all`.

The construction handles r=0, q=0, n₀=0, m₀=0, zero coefficient or quotient rings,
and nilpotent a (zero localization) without a nontriviality assumption or any rank bound.
The identity Jacobian determinant remains 1 for the empty matrix; denominators map
to units even in the zero localization. Kernel numerators are chosen only within an
existential theorem proof from fully proved Mathlib surjectivity results. No public
definition or unproved existence theorem supplies data.

## No longer needed

No imports or statement modules are pruned. The proof dependency on
`def-weil-pbc-finitely-presented-algebra` is removed: the supplied finite presentation
already supplies all generators and relations used by the proof. That node remains
a statement dependency of the unchanged theorem, so this does not claim that the
node or its defining Mathlib module is globally unnecessary. The polynomial and
module-localization definition nodes remain used, as does the new proved stabilization
node. No other planned node is bypassed; the unit's realized statements and steps
are unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The DAG's coefficient-level
construction can be replaced by Mathlib's exact conormal sequence and an explicit
zero-evaluation retraction. Mathlib's existing basis-presentation theorem does not
apply to this fixed-variable-count localized statement, but its exact-sequence and
submersive conormal APIs prove the stabilization step.

`blueprint_refs.py ancestor` returned None for the item because its created.item
records a module name. The new node's blueprint ancestry was reconstructed from the
existing parent `lem-weil-pbc-smooth-stable-conormal-basis`, whose from.node is
`thm-weil-pbc-finite-etale-lifting`; no existing ancestry fields were changed.

## Second reading by B2

1. **Statements unchanged.** Compared the delivered auxiliary module with the repository
version byte-for-byte at every declaration signature. The existing theorem statement is
unchanged; the added stabilization theorem is a new, independently stated node.
**Verdict: pass.**

2. **Proof and axioms.** Compiled both modules with `lcompile.py --all`; there are no
`sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or
`debug.skipKernelTC` occurrences in the delivered Lean. The new theorem's axioms are
exactly `propext`, `Classical.choice`, and `Quot.sound`; the auxiliary theorem compiles
against the same proved dependency. **Verdict: pass.**

3. **New statement and node.** Checked the zero-variable stabilization statement on the
empty-index and zero-localization cases represented by the construction, and checked the
node's source, proof steps, dependencies, blueprint ancestry, and Lean declaration against
the module. Searches recorded in `searches.jsonl` found no duplicate declaration.
**Verdict: pass.**

4. **Shortest route and pruning.** The proof uses the Mathlib exact conormal sequence,
an explicit zero-evaluation retraction, localization surjectivity, and basis rescaling;
the old finite-presentation dependency is unused and removed from the proof dependency
list. No unit step is bypassed and no additional import can be removed without breaking
the proof. **Verdict: pass.**

5. **DAG agreement.** The item node records the actual three proof steps and their imports,
and the new node records the stabilization theorem and its realized unit route. The
report lists one original hole closed and no holes added. **Verdict: pass.**

Changed after second reading: added this review record only; no Lean declarations or
statements were altered.

## New nodes

`lem-weil-pbc-zero-variable-conormal-stabilization` states and proves the localized
conormal equivalence for exactly r new zero variables, independently of any stable
trivialization or basis choice. Its module is
`lean/Sheaf/RingTheory/ZeroVariableConormalStabilization.lean`. It is fully proved;
it creates no further proof item or hole. LeanFinder, Loogle, and source grep were
run and recorded; LeanSearch was attempted and returned Internal Server Error.
The imported blueprint search found no matching stabilization statement.
No change record is needed: every existing statement and definition is unchanged.
