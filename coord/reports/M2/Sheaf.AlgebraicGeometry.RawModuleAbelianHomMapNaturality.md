## What changed

Replaced the original naturality hole by a Lean calculation from four strictly
smaller statements: a source square, a shifted coefficient square, evaluation of
the scalar additive map, and the separate formulas for the two raw pullbacks.
The original declaration's signature, universes and visibility are unchanged.
The generic private `scalar_comparison_pasting` is fully proved from naturality of
an isomorphism and the two square identities. The final calculation identifies
its three-factor composites with the concrete raw maps using the formula lemmas.
All four imports are proof-only imports. No existing data definition is changed.

The square modules provide real definitions for the six source and coefficient
factors, with explicit derived-Hom types. They also construct
`RawModuleScalarComparison.derivedPullbackIso` from the existing exact derived
composition and natural-isomorphism APIs. No data are chosen from an unproved
statement. Each new module contains one public theorem with exactly `:= by sorry`;
its docstring and node give the source and a complete proof in words.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.rawModuleAbelianHomMap_naturality` by a complete proof
from named intermediate statements. Added four holes:

- `AlgebraicGeometry.Etale.rawModuleScalar_source_square`
  (`lem-sbc-raw-scalar-source-square`).
- `AlgebraicGeometry.Etale.rawModuleScalar_coefficient_square`
  (`lem-sbc-raw-scalar-coefficient-square`).
- `AlgebraicGeometry.Etale.rawModuleScalar_map_formula`
  (`lem-sbc-raw-scalar-map-formula`).
- `AlgebraicGeometry.Etale.rawModuleScalar_pullback_formulas`
  (`lem-sbc-raw-scalar-pullback-formulas`).

This is a decomposition, not an axiom-free proof: one upper hole is closed and
four lower holes are added, net -3 holes closed. The pasting argument and the
derived comparison construction are proved. No sorry remains in the item module,
in a private declaration, or inside a definition.

## No longer needed

No original library import, node or module is claimed pruned. The original
`lem-weil-pbc-inverse-image-composition` remains needed below the two square
nodes. Scalar-Hom invertibility, injectivity, surjectivity, cohomological
acyclicity and resolution arguments are unnecessary for this calculation.

Removed the earlier attempt's unlanded
`RawModuleAbelianHomMapNaturalityExpanded` module and
`lem-sbc-raw-module-abelian-hom-map-naturality-expanded` node: they merely
restated the complete target.

## Where the brief, the DAG or earlier work was wrong

The earlier claim that strict intermediate statements could not be expressed
was incorrect. The source square has no G,q,z; the coefficient square has no
S,k,U,z. The map formula has no arrow between Over objects, and the pullback
formulas contain no scalar comparison map or scalar naturality assertion.
Their combination is a real categorical pasting proof.

The original DAG bundles comparison coherence and formula expansion into one
prose step. Repeated concrete evaluation conversions exceeded the kernel's
60-second check limit even though the categorical calculation elaborated.
A diagnostic with a lower heartbeat bound confirmed a kernel deterministic
timeout. Attempts to share the factor constants in the original data definition
did not resolve this, and that change was discarded. The remaining formula
expansions are named steps with their own proof obligations, rather than holes
inside the final calculation. No existing definition or interface is adapted.

Edge cases were checked at the formula level: source t can be zero, source or
coefficient sheaves can be zero, arrows can be identities, and the coefficient
square allows all integer shifts, including negative degrees and zero. Neither
square cancels a class or assumes invertibility of the raw Hom map. The pullback
formulas use arbitrary module and abelian classes independently. The unit
`sk-lem-failure-field` has empty realized lists; no realized unit step is bypassed.
The original statement is not disputed.

## New nodes

`lem-sbc-raw-scalar-source-square`, module `RawModuleScalarSourceSquare`: source
comparison coherence for arbitrary E,L,t, with a complete mate/unit and single
comparison proof in words. Source: original source-factor step, Tags 03D7/03Q8.

`lem-sbc-raw-scalar-coefficient-square`, module `RawModuleScalarCoefficientSquare`:
shifted coefficient comparison coherence, with a complete single, composition
and shift compatibility proof in words. Source: original coefficient-factor
step, Tags 03D7/03Q8.

`lem-sbc-raw-scalar-map-formula`, module `RawModuleScalarMapFormula`: evaluate
one additive scalar map as the source factor, derived image of a class, and
coefficient factor. Source: original expansion step, Tags 03FD/03Q8.

`lem-sbc-raw-scalar-pullback-formulas`, module `RawModuleScalarPullbackFormulas`:
the separate three-factor forms of the module and abelian raw pullbacks.
Source: original expansion step, Tag 03Q8. Its abelian class is arbitrary and
unrelated to the module class; there is no comparison coherence in this statement.

LeanSearch returned service unavailable (Internal Server Error), which is recorded
without a verdict. LeanFinder, Loogle and msearch grep were run, and rg searched both source roots
and Mathlib. Existing exact-derived APIs construct the comparison isomorphism;
they do not provide the two etale scalar squares. The existing bundled module
pullback evaluation lemma is one step in the pullback formula proof, not the
complete factorization. No new statement repeats the target. No change record
or forced adaptation is required.

Recovery check: reread the complete item, all four new statements and their nodes,
the original dependency interfaces, the unit record, and the earlier search log.
Retried the formula proofs by direct evaluation and selective unfolding. A
profiled attempt elaborated in under one second but exhausted the kernel budget.
An experimental explicit-function presentation of the additive map also timed
out and was discarded; it is not part of this delivery. No existing dependency
is adapted, no local transparency attributes or profiling options are delivered,
and the compiler limits are unchanged. The final dry run validates the reduction
with all four independent obligations still explicitly open.

## Second reading by M2

1. I compared the delivered item module with the repository version. The target theorem signature is byte-for-byte unchanged; only proof-only imports, a private helper, and the proof body differ. The four added modules introduce the displayed factor definitions and split theorem statements, with no alteration to an existing declaration.

2. I compiled the sandbox modules with `lcompile.py --all` and checked the delivery dry run. The item proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definition. The four split theorems are the only intentional sorry declarations, each public, named, documented with a complete proof plan, and paired with a DAG node. The categorical pasting helper is fully proved.

3. I checked each split statement against its use and edge cases. The source and coefficient squares are independent coherence equations; the map formula is an evaluation identity; and the pullback formulas are separate module and abelian factorizations. They are strictly smaller than the target, have no extra hypotheses or weakened conclusions, and do not duplicate the target. The source and coefficient definitions are explicit constructions, not witnesses selected from mere existence.

4. I checked the proof route and pruning. The target proof uses the four split nodes and the existing inverse-image composition dependency through their modules, and the unit record's realized route is unchanged. No import or old dependency is claimed pruned; the abandoned expanded restatement is absent from the delivery. The imports required by public signatures remain public, while the target's added imports are proof-only.

5. I checked the DAG records. The target proof and `proof_deps` match the four applications in the Lean proof, and each new node records its declaration, statement, source, proof plan, dependencies, and split status. The report's hole accounting records one target closed and four strictly simpler holes added; no statement change or forced adaptation is present.

Changed during second reading: no mathematical or interface changes. I added this review section only; the source files and DAG nodes were already consistent with the proof and dry-run checks.
