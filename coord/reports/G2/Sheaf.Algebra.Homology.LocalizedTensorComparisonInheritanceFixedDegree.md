## What changed
Corrected `ModuleCat.localizedTensorComparison_inheritance_fixed_degree`: the
premise now ranges over every degree. The original assertion is false; see the
counterexample below and the inline STATEMENT-DISPUTED comment. The corrected
assertion is reduced in Lean to the explicit localizing comparison predicate,
its generator case, its closure properties, and the existing
`CategoryTheory.derivedModuleFreeGeneration`. The predicate is a real definition
with no data chosen from a postponed theorem.

Added `Sheaf.Algebra.Homology.LocalizedTensorComparisonProperty`,
`Sheaf.Algebra.Homology.LocalizedTensorComparisonGenerators`, and
`Sheaf.Algebra.Homology.LocalizedTensorComparisonClosure`. Only the latter two
have proof holes. Both statements are strict parts of the localizing argument:
the generator statement handles shifts of A without assuming C-flatness; the
closure statement assumes C-flatness but assumes no comparison is invertible.

The sole caller `Sheaf.Algebra.Homology.LocalizedTensorComparisonInheritance`
has the forced one-line proof adaptation, replacing `(h i)` by `h`.
The change record is
`coord/changes/localizedTensorComparison_inheritance_fixed_degree.md`.

## Proved and sorry left
The corrected `ModuleCat.localizedTensorComparison_inheritance_fixed_degree`
has a complete compiling proof from the two new statements and the existing
generation theorem. This is a decomposition, not a sorry-free proof of the
mathematical result and not a proof of the false original assertion. The old
hole is replaced after the explicitly recorded statement correction; no net
proof progress is claimed. The final assembly in Lean is complete. Holes closed at unchanged statements:
none. The single hole in the false original
`ModuleCat.localizedTensorComparison_inheritance_fixed_degree` is replaced by
the corrected intermediate statement and its assembly. Holes added: the two
named lemmas below. In a raw hole count this replaces one by two (net -1),
subject to the pinned ledger's import-closure calculation; it is not a proof
of the original statement.

Two new named sorries remain:
- `ModuleCat.localizedTensorComparisonProperty_generators`
  (`lem-pc-localized-tensor-comparison-generators`).
- `ModuleCat.localizedTensorComparisonProperty_closure`
  (`lem-pc-localized-tensor-comparison-closure`).

There are no sorries in the item's module, in the new predicate definition,
or in the forced adaptation. No hole is hidden in a definition. The definition
quantifies over representatives and models without selecting an object.

## No longer needed
Removed redundant direct imports `Mathlib.Algebra.Homology.Monoidal` and
`WeilConjectures.Mathlib.Algebra.Homology.Bifunctor` from the item's module.
Both remain in its public transitive import closure through retained imports;
no module is thereby pruned from the target closure.

Of the old direct proof dependencies, `def-pc-base-derived-tensor-cohomology-model`
and `lem-pc-kflat-derived-tensor-associator` are replaced as direct proof steps.
The model remains a statement dependency and is used by the new predicate and
both split statements. The associator remains a proof dependency of both split
statements and is now privately imported in their modules. Thus neither node
is globally unnecessary. `lem-pc-derived-module-free-generation` remains a
direct dependency. No node or UNIT route is bypassed.

## Where the brief, the DAG or earlier work was wrong
STATEMENT-DISPUTED: the original fixed-degree helper is false. Set
R=A=B=C=Z, Q=0, N=Z concentrated in degree 1, U=Z concentrated in degree -1,
and i=0. The zero complex and the shifted free rank-one complex are K-flat;
C is flat over E=A tensor_R B. The source cohomology of both Q and U tensor Q
is zero. The premise is 0 to H^0(N)=0, whereas the conclusion is
0 to H^0(U tensor N)=Z. The inverse scalar-extension tensorator is an
isomorphism and cannot change this failure. The old proposed closure for a
single degree cannot be shift-stable. The corrected all-degree predicate is
what the original localizing-subcategory plan needs.

The global caller already assumes the comparison in every degree, so this
correction preserves its statement and the source's result. Source checked:
[Stacks Tag 0DJA(1)](https://stacks.math.columbia.edu/tag/0DJA) and
[Stacks Tag 0BYJ](https://stacks.math.columbia.edu/tag/0BYJ).
The local Stacks .tex files are absent on this machine, so the official online
versions were read. The detailed localizing argument is recorded as agent
proof origin, derived from the existing DAG plan and those sources.

The existing helper node has no DAG citers, despite the global Lean caller;
its parent node had not been updated to mention the fixed-degree split.
`blueprint_refs.py ancestor` returns None for the two inheritance nodes.
The new nodes record the existing associator's blueprint ancestor
`lem-pc-rf-perfect-base-change` and the intermediate inheritance nodes in `via`.
The UNIT record has empty realized statement and step arrays; no realized
UNIT statement or step was removed or bypassed.

Edge cases checked for the new statements: arbitrary positive and negative
shifts, zero rings, the zero complex, empty coproducts, arbitrary unbounded
complexes and a nonflat A-to-C map. The generator case does not need
C-flatness; closure needs exactly C-flatness over E, so extending the source
long exact sequence is exact. Both quantify over all K-flat representatives
and all canonical models; this invariance is included in their proof sketches.
No choice of a strict C-complex representing the entire E-cohomology action
is assumed. A tentative chain-transport approach was discarded and none of
its files or claims is part of this delivery.

Searches ran through msearch.py and are logged in searches.jsonl: LeanSearch
returned HTTP 500, LeanFinder returned T-structure statements, Loogle returned
generic ObjectProperty declarations, and grep found no specialized comparison
predicate or closure theorem. Existing source and Sheaf modules were also
searched. The existing KFlatModuleBaseChange theorem was read; it proves
scalar-extension K-flatness but does not supply the comparison closures.

## New nodes
`def-pc-localized-tensor-comparison-property` records the explicit universal
predicate on D(A). It has no proof obligations or arbitrary chosen data.

`lem-pc-localized-tensor-comparison-generators` records the unit/shift and
representative-invariance part of the argument. Its full proof in words is
in the new module's theorem docstring.

`lem-pc-localized-tensor-comparison-closure` records coproduct, triangle and
retract stability, without any hypothesis of initial comparison invertibility.
Its full proof in words is in the new module's theorem docstring.

## Forced adaptations
`Sheaf.Algebra.Homology.LocalizedTensorComparisonInheritance` is unclaimed.
Its original line 76 failed against the corrected helper:
```text
Application type mismatch: The argument h i has type
  IsIso (m.localizedComparison i ≫ HomologicalComplex.homologyMap t i)
but is expected to have type
  ∀ (j : ℤ), IsIso (m.localizedComparison j ≫ HomologicalComplex.homologyMap t j)
```
Only `(h i)` changed to `h`. The caller already binds exactly this all-degree
hypothesis. No imports, declarations, signatures, visibility or other proof
lines changed in this module. The delivered adaptation compiles. The delivery
tool additionally checks that the original compiles against the baseline and
fails against the changed dependency.

## Second reading by G2

1. Compared all five delivered modules with the repository. The only existing
   signature change is the recorded all-degree premise of
   `ModuleCat.localizedTensorComparison_inheritance_fixed_degree`. The sole
   caller changes exactly `h i` to `h`; its signature and visibility are
   unchanged. The counterexample is valid: over Z, Q=0, N in degree 1 and
   U in degree -1 make the old premise 0 to 0 and conclusion 0 to Z. The
   change record now reproduces the actual multiline signatures verbatim.
   No target or definition used by a target is changed.
2. Compiled all five modules locally in import order using lcompile.py. The
   only direct sorries are the two reported named theorems; the property is
   a concrete universal predicate and selects no witnesses. No forbidden
   axiom or implementation escape is present. Scratch-copy #print axioms checks passed for all five declarations: the
   predicate uses only propext, Classical.choice and Quot.sound; each of
   the four theorems additionally uses sorryAx, as expected from the two
   open steps and existing generation dependencies. Full local output is
   in scratchpad/second-reading-axioms.txt.
3. Read both split statements and their full docstring arguments. Generators
   need all degrees to handle positive and negative shifts; flatness of C
   is unnecessary for this step, since tensoring an isomorphism preserves
   it. Closure needs C-flatness over A tensor_R B to preserve the source
   long exact sequence, but no initial comparison isomorphism. Checked zero
   rings, Q=0, zero objects, empty sums, nonflat A-to-C scalar extension and
   arbitrary unbounded representatives. These are strict separate parts of
   the argument, not copies of the helper. Independent LeanFinder, Loogle
   and grep searches used homological-functor and retract terminology.
   Mathlib has generic stability of isomorphisms under arrow retracts, but
   no specialized comparison closure or generator result. Read the existing
   BaseDerivedTensorCohomologyModelIndependence and
   BaseDerivedTensorLocalizedNaturality results: they supply model transport
   and naturality, but neither supplies the two requested conclusions.
   No split statement could be closed by a short application of these tools.
4. Followed the proof from the helper to the explicit predicate, generator
   and closure obligations, and derivedModuleFreeGeneration. Checked the
   source [Tag 0DJA](https://stacks.math.columbia.edu/tag/0DJA), its associativity
   reference [Tag 0BYJ](https://stacks.math.columbia.edu/tag/0BYJ), and the
   generation argument [Tag 09PB](https://stacks.math.columbia.edu/tag/09PB).
   The localizing reduction is an agent argument consistent with those
   sources, not a claim that their texts contain this exact predicate.
   The unit sk-thm-picard-semicon has empty realized arrays; no realized
   statement or step is bypassed. Removed two redundant direct public imports
   whose declarations remain publicly available transitively. Individually
   deleting each of the predicate's five supplementary public imports fails
   compilation, confirming that they provide its statement's notation or
   tensor/monoidal instances. All newly added proof-only imports are private.
5. Matched the existing node's three proof steps to the Lean assembly and its
   proof_deps to their cited nodes. Each new node has its source, searches,
   chapter/unit, blueprint ancestry and Lean attachment. Replaced flattened
   lean.statement fields with verbatim multiline signatures. Retained
   statement_change.by = "G2 stage 2": the shared statement-correction
   validator requires this exact form even when invoked by stage 3. Restored private imports of
   the associator named by the two open lemmas' planned proof dependencies.
   The report now explicitly identifies both replaced old direct dependencies
   and explains why they remain necessary transitively.

Second reading changes: redundant imports removed; planned associator imports
restored; verbatim signature metadata and change record repaired; shared
correction-schema label explained; dependency/progress accounting corrected. The mathematical assembly and
both split theorem statements were retained.

The first dry run found only the schema-label error described in point 5;
its local compiler, axiom probes and both counterfactual caller checks passed.
The label was restored rather than changing any project tool.

## Forced adaptations

### Sheaf.Algebra.Homology.LocalizedTensorComparisonInheritance
Original against changed dependencies failed:
```
/tmp/forced-adaptation-pxrd2117/lean/Sheaf/Algebra/Homology/LocalizedTensorComparisonInheritance.lean:76:91: error: Application type mismatch: The argument
  h i
has type
  IsIso (m.localizedComparison i ≫ HomologicalComplex.homologyMap t i)
but is expected to have type
  ∀ (j : ℤ), IsIso (m.localizedComparison j ≫ HomologicalComplex.homologyMap t j)
in the application
  localizedTensorComparison_inheritance_fixed_degree R A B C hC U Q N hU hQ t m mU i (h i)

(with the modules compiled into /tmp/forced-adaptation-pxrd2117/.lbuild) [5.1 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
