## What changed

Replaced the remaining proof hole in
`WeilConjectures.PurStrictScalar.compactSupportScalarLimitReduction` without changing its
statement, definitions, instances, or public attributes. Its proof now applies the existing scalar
constructibility theorem, the strict scalar mate, two proved single-coefficient native
support lemmas, and one smaller completed-comparison lemma. The finite reduction equality
is derived by injectivity and naturality of the finite scalar adjunction. Both final
coefficient-square clauses use the existing proved generic comparison helpers; the later
parent integral comparison theorem is never invoked.

Added `Sheaf.Paper.CompactSupportNativeRealization`: its proof repeats the native
construction with the **supplied** reduction calculus, proving literal equality of the
normalized underlying tower with the requested native tower. It only requires intrinsic
integral constructibility, not a common Tor interval.

Added `Sheaf.Paper.CompactSupportNativeEffectivity`: it constructs the normalized DVR
tower from the actual coefficient-sequence evaluations and applies the canonical
completed-tower Roos triangle and normalized DVR effectivity. Projection identities
identify the counits literally. Uniqueness of left adjoints expresses each specified
finite compact-support counit as a composite of the reduction identification, native
counit, and evaluation isomorphism. This proves completeness, all quotient cocycles,
and invertibility of the specified finite counits, separately for both coefficient fields.

Added `Sheaf.Paper.CompactSupportScalarLimitCompletedComparison` for the remaining
completed descent and constant/completed projection equations. These are Steps 3--6
of the source argument. Its conclusion omits normalization, effectivity, domain
preservation, strict-limit invertibility, the transposed reduction equality, and all
coefficient-square clauses; it is strictly a part of the original theorem.

Only the assigned existing module and its node, five new modules and their nodes,
and this report are changed. No shared definition or source-library file is changed.
All new imports in the assigned module are proof imports. After profiling, locally mark
the chosen restriction and tensor comparison irreducible and use explicit coordinate and
equality APIs. Since the complete file still exceeded 60 seconds, extract the already
proved arithmetic normalization argument into CompactSupportScalarRoosNormalization.
Its new theorem takes any unit-normalized comparison; the existing theorem, comparison
definition, and every existing public signature remain in their original module unchanged.
The existing theorem now applies this proved helper. A first delivery check then took
62 seconds for the main file; the tensor/Roos normalization proof was likewise extracted
into CompactSupportScalarRoosTensorNormalization, taking two unit-normalized comparisons
and the identified canonical tensor map. Its existing public wrapper remains unchanged. These local attributes and proof
imports change no importer interface or mathematical construction.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.PurStrictScalar.compactSupportScalarLimitReduction`
(node `lem-pur-compact-support-scalar-limit-reduction`) by a decomposition.
The assigned module has zero remaining holes.

Proved, with no local holes:

- `WeilConjectures.compactSupport_native_realization`
  (`lem-pur-compact-support-native-realization`).
- `WeilConjectures.PurStrictScalar.compactSupport_native_effectivity`
  (`lem-pur-compact-support-native-effectivity`).
- `WeilConjectures.PurStrictScalar.scalarRoosNormalization_of_unit`
  (`lem-pur-compact-support-scalar-roos-normalization`).
- `WeilConjectures.PurStrictScalar.scalarRoosTensorNormalization_of_units`
  (`lem-pur-compact-support-scalar-roos-tensor-normalization`).
- The private adjunction helpers `change_adjunction` and `projection_adjoint`.

Added one hole, and the only hole in this delivery:

- `WeilConjectures.PurStrictScalar.scalarLimitCompletedComparison`
  (`lem-pur-compact-support-scalar-limit-completed-comparison`). Its docstring and node
  give the complete argument with the fixed maps, quotient normalization, and source.

This is one upper hole closed and one strictly smaller lower hole added: a decomposition,
not a net decrease in reachable holes. The original theorem combines genuinely proved
normalization/effectivity statements with the remaining comparison step; it does not
merely rename the original conclusion. No data definition is based on the new existence
statement, and no arbitrary witness is used to define a mathematical object.

Validation: all six delivered modules compile cleanly and pass lcompile.py's per-file
60-second check. The first four passed in the latest full-set run; after adding its
necessary statement import, the tensor normalization helper and main file passed together
against those sandbox artifacts. The first delivery recheck had taken 62 seconds for the
main file and pushed nothing, prompting the second proved helper extraction. All profiling
options are removed. Existing main and both normalization theorem signatures match the
originals exactly, new Lean attachments and proof-dependency unions match the source,
and every Lean line is at most 100 characters. The sole local hole remains the completed
comparison. The delivery tool reruns compilation and all required preflight checks.

## No longer needed

Removed the unused proof import `Mathlib.CategoryTheory.Limits.Final`: the arithmetic
initiality proof lives in the foundation module. The new native realization also omits
a redundant import of CompactSupportNormalizedRealization, whose public API is already
available from its statement import. The assigned module no longer directly imports
RoosArithmeticNormalization; its new normalization proof module imports it. All original
public imports in the existing item are retained, preserving its importer contract. No module can be globally withdrawn:
its existing mathematical dependencies remain needed by the supporting constructions.

The following historical direct proof dependencies of this node are no longer needed as
direct steps; their mathematics remains in the foundations, the new normalization/native
lemmas, or the already proved generic coefficient-square helper:

- `lem-pur-compact-support-roos-cofinality` (still a statement dependency)
- `lem-pur-roos-arithmetic-normalization`
- `lem-coef-compact-support-normalized-realization`
- `lem-weil-compact-support-reduction-tower-functor`
- `def-coef-normalized-dvr-tower`
- `lem-coef-normalized-dvr-effectivity`
- `det-pe-products-exact`
- `lem-weil-strict-roos-comparison`
- `lem-sf-strict-roos-derived-limit-comparison`
- `lem-pur-derived-square-normalization-naturality`
- `lem-weil-strict-roos-derivation`
- `lem-pur-completed-scalar-localization-balancing`
- `lem-weil-pbc-ringed-strict-tower-homotopy-limit`
- `lem-weil-pbc-mate-pasting`

In particular, the main theorem does not re-prove coefficient mate pasting or use the
parent integral-coefficient-comparison theorem. Its last clauses specialize the proved
`comparison_quotients` and private `comparisonSquare` in that implementation module,
which precede and do not use its later integral comparison theorem. The import-direction
check accepts this proof import. No DAG dependency on that parent theorem is added.
All unit-level statements and routes are retained.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed and no mathematical hypothesis is changed. The existing
compactSupport_normalized_realization theorem chooses a reduction calculus internally;
its public conclusion alone does not establish literal equality with the supplied
calculus's native tower. Repeating its construction with that specified calculus
provides the missing stronger interface, without changing the existing theorem.

Edge cases: the native proofs use no division by a ramification index and retain every
finite quotient. Identity quotients use the actual transition unit, and zero objects and
empty schemes use the same exact evaluation and adjunction equations. The comparison
step assumes e >= 1, so the selected positive exponent e(n+1) is nonzero, including n=0.
The finite-reduction transposition uses only an adjunction, with no faithfulness assumption
on scalar restriction for arbitrary derived objects.

## New nodes

`lem-pur-compact-support-native-realization` records the proved specified-calculus
realization with equality of native towers. Its source is the native construction of the
existing normalized-realization lemma, with Stacks 0940/0941. Blueprint search for
"native compact support" found no matching imported node.

`lem-pur-compact-support-native-effectivity` records the proved single-field application
of the canonical completed-tower Roos triangle and normalized DVR effectivity, including
actual projection-adjunct cocycles and finite support counit isomorphisms.

`lem-pur-compact-support-scalar-limit-completed-comparison` records the remaining
strictly smaller descent/projection step (parent Steps 3--6), with Stacks 0941, 07A6 and
06YY and the coefficient model/strict scalar mate dependencies. Blueprint search for
"scalar limit" found no matching imported node. Mathlib searches by LeanFinder,
LeanSearch, Loogle, and grep are recorded with their actual outcomes in the nodes.

`lem-pur-compact-support-scalar-roos-normalization` records the proved specialization of
the arithmetic restriction normalization to native support towers and any unit-normalized
Roos comparison. Its proof was extracted only after local definition/API improvements
and profiling; it adds no hole and preserves the existing scalarRoosNormalization API.
LeanFinder, LeanSearch, Loogle and Mathlib grep searches found only generic ordinary-limit
and unrelated complex APIs, recorded in its node. The current blueprint search for
unit-normalized/arithmetic Roos text found no separate matching blueprint statement.

`lem-pur-compact-support-scalar-roos-tensor-normalization` records the proved tensor
normalization under any two unit-normalized Roos comparisons and a specified canonical
complex map. This extracts the existing proof after profiling and local unfolding
improvements; it adds no hole and preserves the existing scalarRoosTensorNormalization
signature and definitions. Its Mathlib searches are recorded in its node. Its statement publicly imports
RoosComparisonHorizontalCoherence to expose the canonical roosAdditiveComparison map.

There are no change records because no existing interface or definition is changed.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
