## What changed

The original submission moved the full cancellation identity into an equivalent
`affineSpectrum_comparison_cancellation_core` hole. That module and node have been
removed. The replacement follows the two separate steps of the existing proof
plan: identify the adjointified equivalence unit with its original composition
unit (`AffineSpectrumUnitNormalization`), then calculate the comparison square
for those original units (`AffineSpectrumCompositionUnitSquare`). The target
uses unit normalization at X and X' and applies the composition-unit square.
Both new imports in the target are proof-only. Its existing public import,
all existing signatures, and the body and docstring of `affineSpectrumUnitInv`
are unchanged. No definitions or target statements change. The new normalization
module marks `derivedPullback` locally irreducible and respects transparency
while checking coherence. Its private triangle helper works for an abstract
functor family, then specializes to `derivedPullback`; no definition data change.

## Proved and sorry left

Hole closed in the original module:
`AlgebraicGeometry.affineSpectrum_comparison_cancellation`.

Locally proved intermediate statement:
`AlgebraicGeometry.affineSpectrum_unit_normalization`
(node `lem-pc-affine-spectrum-unit-normalization`).

New hole left: `AlgebraicGeometry.affineSpectrum_composition_unit_square`
(node `lem-pc-affine-spectrum-composition-unit-square`).

The latter square has no equivalence-unit normalization in its statement; the
former concerns just one affine scheme and no comparison square. Thus the two
statements split the two substantive steps of the original proof, rather than
moving the full identity to a different name. The original core statement is
not delivered. This is a reduction/decomposition: one original hole closed,
one lower hole added,
net zero local holes. The normalization theorem is proved, not another hole.
The remaining square prevents the target from being axiom-free.
The unit-normalization theorem itself uses only the three allowed axioms.

## No longer needed

The proposed `AffineSpectrumComparisonCancellationCore` import, module and node
are removed from this delivery; none existed in the repository baseline.
No original import is removed and no original module becomes unreachable.
The target no longer directly invokes
`def-pc-affine-spectrum-derived-coordinates` or
`lem-pc-ringed-spaces-derived-pullback-composition`; those original proof
nodes are retained as dependencies of the intermediate calculation and
normalization. The target's proof_deps now name the two actual intermediate
lemmas and the direct-coordinate definition used when unfolding its unit.
The unit record `dag/units/sk-thm-picard-semicon.json` is unchanged.

## Where the brief, the DAG or earlier work was wrong

The earlier report called cancellation of an invertible final factor a strict
reduction. It was an equivalent restatement of the item. Its core docstring
also lacked the required complete proof, and its node used the parent in
stmt_deps, while the parent's proof metadata was not updated at all. The report
said the unit definition moved into the core module, but it was still in the
target module, with its docstring deleted. These faults have been repaired.
Stacks 0D5S supplies the derived-pullback composition theorem, and 08HY explains
its base-change use; neither states these Lean-specific coherence identities
verbatim. The new nodes explicitly identify the calculations as agent-written
consequences of the composition/unit laws in the existing proof plan.

## New nodes

`lem-pc-affine-spectrum-unit-normalization` records the single-scheme triangle
and unit-identification calculation in `AffineSpectrumUnitNormalization.lean`.
Its proof uses the existing composition theorem and the constructed equivalence,
not the target cancellation theorem.

`lem-pc-affine-spectrum-composition-unit-square` records the second calculation,
using only the selected composition/identity comparisons and spectrum naturality,
in `AffineSpectrumCompositionUnitSquare.lean`. Both nodes remain in the parent's
chapter and unit. Each carries its complete proof in words, exact Lean signature,
and actual logged searches. Searches by different concepts found generic
Equivalence, NatIso, and inverse-composition tools but no exact derived-spectrum
statement; LeanSearch was unavailable. Local searches also inspected the
existing spectrum comparison and composition modules and DAG nodes.

No change record is needed: all existing interfaces and definitions are unchanged.
The opacity attribute is local to a new module, and no existing module command changes.

## Second reading by K1

1. Compared the delivered target with the repository using `diff -u`. The only
   changes are two plain proof imports and the theorem's proof body. Every existing
   signature and docstring, and the entire existing unit definition, are byte for
   byte identical. There are no interface changes or forced adaptations. PASS.
2. Read the proof from the target down. Unit normalization genuinely proves the
   preliminary triangle calculation from the selected composition theorem; it
   does not assume the target or the raw square. The remaining square is the
   whole proof of a named public theorem with a matching node and full proof
   docstring. There is exactly one delivered `sorry`, in
   `affineSpectrum_composition_unit_square`, and no forbidden construct or
   data definition with a hole. Compilation and axiom checks are recorded below.
3. Rejected and removed the old equivalent core restatement. The replacement
   statements separate the single-scheme unit identification from the composition
   square; the former is now proved. Read Stacks Tags 0D5S and 08HY, the selected
   composition theorem, all spectrum comparison definitions, and Mathlib
   Equivalence.mk/adjointifyη/counit_app_functor. Searches used different terms
   (coherent contravariant composition; adjointification; inverse scheme units),
   including LeanFinder, Loogle and grep, and found only generic building blocks.
   LeanSearch failed with a service error. No duplicate derived-spectrum result
   was found in the library or DAG. Identity g' reduces the remaining square to
   composition unit laws; at a zero object the morphism is unique; the calculation
   uses no points, nonemptiness or Noetherian hypotheses, so empty schemes cause
   no exception. PASS, with the composition-square calculation still open.
4. The proof follows the two steps already present in the parent's plan. The
   normalization proof was simplified using faithfulness and the unchanged
   counit of Equivalence.mk, avoiding expansion of its adjointification formula.
   All imports serve statement or proof dependencies; the target's new imports
   are plain, and the two helpers' public imports are needed in their signatures.
   The No longer needed section names the old direct proof dependencies that
   moved into helper proofs. No original module is pruned. The parent is below
   the unit level: `sk-thm-picard-semicon.json` has empty realized entries here;
   its statement, steps, uses and realized fields are unchanged. PASS.
5. Updated only proof, proof_deps and proof_origin of the existing parent node.
   Both new nodes have the parent's chapter/unit, self-contained statements,
   exact Lean signatures, sources, step dependencies, actual logged searches,
   creation/blueprint records and module/declaration records. Their dependencies
   contain no reference back to the target; the earlier core's parent dependency
   is gone. The new nodes describe the two actual calculations. PASS.

Second reading changed: removed the equivalent core restatement, restored the
unit definition's docstring, proved the composition triangle and unit
normalization, split off only the raw composition-unit square, corrected the
parent's proof metadata, and rewrote the report to state the net-zero hole count.

Validation: `lcompile.py --all` compiled all three delivered modules in import
order, without warnings (composition square 17.8 s, normalization 57.7 s,
target 20.6 s). An explicit scratch `#print axioms` check then compiled in 2.2 s:
`affineSpectrumUnitInv` and `affineSpectrum_unit_normalization` use exactly
`propext`, `Classical.choice`, `Quot.sound`; the composition square and target
add only `sorryAx`. The scratch module was removed before delivery. The
normalization and target have no local holes; only the square remains `sorry`.

Compile-time repair: after a delivery dry run exceeded 60 seconds, the private
triangle helper was generalized over the pullback functor family, and the new
module's transparency options were set to true to respect local irreducibility.
The public normalization signature is unchanged. The resulting single-file
compile took 51.6 s; its sole long-line warning was repaired before final checks.
