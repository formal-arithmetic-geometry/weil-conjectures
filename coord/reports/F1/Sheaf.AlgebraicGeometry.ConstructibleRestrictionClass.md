## What changed

`Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass` now obtains a filtered constructible
presentation using `Scheme.exists_filtered_colimit_constructible`, applies the supplied-colimit
extraction theorem, and returns the stage with its constructibility witness and cocone map.
The existing theorem signature and docstring are unchanged.

Added `Sheaf.AlgebraicGeometry.ConstructibleRestrictionClassCore`, with the named extraction
statement `AlgebraicGeometry.Etale.exists_restriction_class_of_filtered_presentation`.
It assumes an explicit filtered colimit and makes no constructibility assertion. Its
source and complete mathematical proof are in its docstring. Its module imports the
filtered-category definitions and the existing inverse-image/cohomology interface needed
by the signature; it does not publicly import the constructible-presentation theorem.

The original node's proof, proof dependencies and proof origin now describe the actual
three-step Lean reduction. The new core node has a self-contained statement matching Lean,
all five planned proof dependencies, the correct blueprint ancestor and actual search records.

## Proved and sorry left

The item's sole theorem `AlgebraicGeometry.Etale.exists_constructible_restriction_class`
is now syntactically sorry-free: 1 of 1 original declarations. This is a reduction, not an
axiom-free completion: its dependencies include the still-open presentation theorem and core.

The delivery leaves exactly one direct `sorry`, the named theorem
`AlgebraicGeometry.Etale.exists_restriction_class_of_filtered_presentation`, node
`lem-weil-pbc-constructible-restriction-class-core`, in the new core module.

Both files compile locally in import order without warnings. A scratch copy containing
`#print axioms` for both declarations reports only `propext`, `Classical.choice`,
`Quot.sound` and `sorryAx`. No forbidden declaration or hollow definition is introduced.

## No longer needed

Removed the first worker's unused proof imports of
`Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`,
`Sheaf.AlgebraicGeometry.EtaleInverseImageColimits`, and
`Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit` from the target module.
These were additions in the sandbox, not public imports of the repository version.
The target now needs only the constructible presentation and core extraction imports
in addition to its original public signature imports.

Every former direct proof dependency absent from the revised target proof is listed here:
`lem-weil-pbc-module-sheaves-colimits-forgetful`,
`lem-weil-pbc-inverse-image-preserves-colimits`,
`prop-weil-pbc-inverse-image-modules-exact`,
`lem-weil-pbc-cohomology-filtered-colimit`.
The former `def-weil-directed-colimit-abelian-groups` citation is pruned from this route:
the proof uses the general filtered-category Mathlib leaf instead.
No unit-realizing node is bypassed, and no globally unreachable module is claimed.

## Where the brief, the DAG or earlier work was wrong

The initial core node said the presentation stages were constructible, but its Lean statement
has no such hypothesis. The corrected new node explicitly treats arbitrary module-sheaf stages.
The initial core docstring did not contain a complete proof; it now explains the cocone and
leg identifications, the canonical cohomology comparison and elementwise extraction.
The initial node omitted forgetting and inverse-image compatibility dependencies and used
an invalid string for `blueprint.from`. Its search entries did not reflect searches recorded
in this sandbox; they were replaced by searches actually run during this reading.
The target node had not been updated to describe the proof; it now agrees with Lean.

The returned C4 was repaired by replacing the obsolete directed-set dependency in core proof
step 4 with the Mathlib representative-extraction leaf
`lem-category-theory-concrete-iscolimit-exists-rep`, whose exact declaration is
`CategoryTheory.Limits.Concrete.isColimit_exists_rep`.

The known obstacle is genuine: `exists_filtered_colimit_constructible` supplies an index
in `Type (u + 1)`, whereas `etaleCohomology_isColimit_of_isFiltered` currently accepts only
`Type u`. In addition, that theorem uses derived-category cohomology, whereas this target
uses `Sheaf.H`; a natural identification respecting every cocone leg is necessary.
The open core records these mathematical steps without pretending either identification
has been formally proved. Neither existing declaration was modified to evade the obstacle.

## New nodes

`lem-weil-pbc-constructible-restriction-class-core`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-constructible-restriction-class-core.json`,
is the supplied-colimit extraction step below the constructible-representation argument.
It is a strict part of the original argument: it neither constructs the presentation nor
proves constructibility. There are no statement-change records, since no existing signature
or definition changes.

`lem-category-theory-concrete-iscolimit-exists-rep`, in
`dag/nodes/sec-proper-base-change/lem-category-theory-concrete-iscolimit-exists-rep.json`,
records the exact Mathlib declaration used by core proof step 4. It replaces the former
directed-set node citation and has a verified Mathlib match at line 130.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered target module to the repository with `diff`, then compared the
   substring from its theorem keyword through the end of the signature byte for byte.
   Verdict: unchanged after removing one extra space before `:=`. Its original docstring
   is also unchanged; all original public imports remain. The core is a new declaration,
   and neither file contains a definition. No existing mathematical interface changes.
2. Compiled both modules locally in import order and checked both declarations with
   `#print axioms` in a scratch copy. Verdict: no error or warning; only the three standard
   axioms and the expected `sorryAx`. The only direct `sorry` is the core named above.
   Inspected the code for `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, embedded
   sorries and hollow definitions: none. The final delivery tool repeats the checks.
3. Read [Stacks 03SA(3)](https://stacks.math.columbia.edu/tag/03SA) and
   [Stacks 03Q5](https://stacks.math.columbia.edu/tag/03Q5), the four existing colimit
   interfaces and the Mathlib representative theorem at
   `Mathlib/CategoryTheory/Limits/ConcreteCategory/Basic.lean:130`.
   The core hypotheses match the supplied filtered cocone: qcqs X and X₀, arbitrary i,
   finite commutative Λ, a small nonempty filtered category, arbitrary diagram D, vertex F,
   cocone ι with a colimit witness, q and c. Its conclusion chooses a stage and a class
   mapping to c, with the precise underlying restricted cohomology map; it does not assume
   constructibility. Checked q = 0, c = 0, the zero ring, empty X₀, and a one-object identity
   presentation. Filteredness excludes an empty index, even when all classes vanish.
   The nontrivial mathematical content is the cohomology comparison, not the already
   available generic representative lemma. Mathlib LeanFinder, Loogle and grep searches
   were run with different queries; LeanSearch returned Internal Server Error, recorded as
   unavailable. Searched local Lean and upstream by representation and cohomology-colimit
   terminology, and searched all blueprint nodes for filtered cohomology and constructible
   restriction. No duplicate extraction statement was found. Verdict: true intermediate
   statement; the open proof is documented, and it is not a relabeling of the target.
4. Read the original proof plan and `dag/units/sk-thm-p1.json` realized statement and steps.
   This reduction retains the filtered constructible presentation and the cohomological
   extraction route; it operates below the unit level and bypasses no realized unit node.
   Removed three unused imports and the core's unnecessary public import of the presentation
   theorem. Retained the core's signature imports, validated by recompilation. Every removed
   direct node dependency is listed under No longer needed and is retained in the core plan.
   Verdict: route preserved; no completed shorter proof found in the searches.
5. Opened both node records alongside both Lean files. The target node now records obtaining
   A/D/hD/ι/hι, applying the core and packaging the stage. The core node now describes its
   exact hypotheses without a constructibility premise and records the five mathematical
   dependencies its word proof uses, with a self-contained statement, source, blueprint
   provenance and searches. Its recorded Lean signature matches the declaration.
   Verdict: node proof metadata agrees with the delivered code and the documented open work.

Changed in this reading: signature whitespace only; removed unused and over-public imports;
completed the core docstring and module header; repaired the core statement/proof/dependencies,
blueprint and search records; supplied the target node's actual proof metadata; and replaced
the report with this explicit account. The original proof reduction itself was retained.

## Second reading by F1

1. Compared both delivered modules with the read-only repository. The core is new.
   The existing target differs only in two plain proof imports and its proof body;
   its theorem signature is byte for byte identical. The existing node differs only
   in proof, proof_deps and proof_origin. Verdict: no accidental interface change,
   no weakened conclusion, added hypothesis or changed definition.
2. Compiled both files through lcompile.py in import order, then compiled a scratch
   copy with #print axioms for both declarations. Both checks pass cleanly; the
   only axioms are propext, Classical.choice, Quot.sound and expected sorryAx.
   The sole direct sorry is the reported public core theorem; neither module has
   definitions or forbidden declarations. Verdict: valid reduction with open
   dependencies, not an axiom-free completion.
3. Read Stacks [03SA(3)](https://stacks.math.columbia.edu/tag/03SA) and
   [03Q5](https://stacks.math.columbia.edu/tag/03Q5), the colimit/inverse-image
   interfaces, and Mathlib's representative theorem including its section assumptions.
   The supplied-presentation core is true: forget and restrict the colimit, apply
   the canonical cohomology comparison, then extract a representative. Checked
   q=0, c=0, zero coefficients, empty X₀, and the identity one-object diagram;
   IsFiltered supplies nonemptiness. The core does not construct a presentation
   or establish constructibility, so it is a strict part of the target argument.
   Independent LeanFinder, Loogle and grep searches using cohomology-preservation
   terminology, plus rg of the library and upstream, found no closed replacement.
   The universe and Sheaf.H comparison gaps reported earlier remain genuine.
   Verdict: the open statement is justified and documented; not closed in this reading.
4. Checked dag/units/sk-thm-p1.json realized steps against the original and revised
   plans. This item is below the unit level; the constructible-presentation and
   cohomological-extraction route is retained and no realized step is bypassed.
   The two added imports are proof-only; public imports serve the signatures.
   All five old direct dependencies absent from the target's proof_deps are
   accounted for under No longer needed (four moved into the core, the directed-set
   citation replaced by the concrete-category representative leaf). Verdict:
   imports and pruning are consistent; no shorter closed proof found.
5. Checked every node's proof_deps against the union of its step uses, the core's
   stored Lean signature against its actual declaration, and the target's three
   proof steps against its Lean body. New-node provenance and fields are present.
   Corrected the new Mathlib leaf's overstrong preservation hypothesis to the exact
   diagram-specific PreservesColimit F (forget C), its literal Unicode escapes,
   and its search claims to actual logged searches. Verdict: nodes now agree with
   Lean and the verified searches. No existing node statement was changed.

Changed in this reading: repaired only the new Mathlib leaf's statement, signature
text, application description and search records; appended this review. Retained
both Lean files unchanged. One of one original theorem bodies is sorry-free, with
one split-off theorem still open; this count does not mean the target is axiom-free.

The dry run also required a LeanSearch entry separately from Loogle/LeanFinder.
Ran it and recorded the actual Internal Server Error as unavailable, with no verdict;
the other services and source reading independently establish the exact Mathlib match.
