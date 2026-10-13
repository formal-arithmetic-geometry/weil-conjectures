## What changed

Proved `AlgebraicGeometry.diagonalConormal_affine_ideal_class_core` in
`Sheaf.AlgebraicGeometry.DiagonalConormalAffineIdealClassCore`, with its original signature,
visibility, and docstring unchanged. Added two proof-only imports:
`Mathlib.AlgebraicGeometry.Morphisms.Flat` for the affine-open section pushout theorem, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf` for the sectionwise kernel lemma.
The existing public imports remain because they supply the statement's API.

The ring equivalence is constructed by uniqueness of two pushout cocones; the cocone equations
prove both projection formulas. The diagonal kills each generator `1 ⊗ a - a ⊗ 1`, so the
entire multiplication ideal maps into its kernel. The proved sectionwise kernel theorem then
supplies every required section. Updated the existing node's proof, proof_deps, and
proof_origin to follow this route. No definition, statement, or other module was changed.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.diagonalConormal_affine_ideal_class_core`
(node `stage3-diagonal-conormal-affine-ideal-class-core`). This is a complete proof, not a
decomposition. Added zero holes; no declaration is left with `sorry` in the delivery.

The final module compiles with `lcompile.py` in about five seconds, with no warnings. The
proof uses only proved Mathlib and upstream results. The argument needs no nonemptiness,
flatness, finiteness, or separatedness assumption; empty U and the zero ring are included by
the general pushout and kernel theorems. No data is chosen from an unproved theorem.

## No longer needed

No imports were removed: both original imports are public and provide the statement's API;
both added imports are used by the proof.

Removed `lem-weil-pbc-diagonal-immersion` from the node's proof dependencies: the proof does
not use the immersion theorem or require a closed-diagonal neighbourhood. Its Mathlib
module is not added. Removed `def-sc-diagonal-conormal` from proof_deps as well: the
statement retains it in stmt_deps and its public module import, but the proof works with the
actual categorical kernel directly and does not use the conormal construction. No claim is
made that this definition or its module is globally unreached.

The explicit Spec-chart transport and identification of the restricted ideal sheaf with a
quasi-coherent ideal are unnecessary for this theorem. There were no separate nodes or
imports for these steps to remove. No other node or module is pruned, and the unit's own
statement and realized steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The original plan cited the general diagonal-immersion theorem for the affine calculation,
but Mathlib already supplies precisely the required affine-open section-ring pushout via
`isIso_pushoutSection_of_isAffineOpen`; despite its location in Morphisms.Flat, it requires
no flatness. The kernel lift can be proved from the generator description of the
multiplication ideal and `Scheme.Modules.range_map_kernelι`, without transporting the
whole ideal sheaf through a Spec chart. The statement itself is correct and unchanged.

The local literature TeX file named by the node is unavailable on this machine; the source
proof was read at https://stacks.math.columbia.edu/tag/08S2 and
https://stacks.math.columbia.edu/tag/01KJ. The Lean proof realizes their affine chart and
kernel calculation directly.

## Second reading by J2

1. Compared the sole delivered module with the repository using `diff` and checked the
   theorem signature byte for byte. The only Lean changes are two plain proof imports and
   replacement of the original `by sorry`; the statement, visibility, definitions and
   existing docstrings are unchanged. No change record is needed. Verdict: pass.
2. Independently compiled the module with `lcompile.py`: clean, no errors or warnings.
   Scanned for forbidden declarations and holes: none. Compiled a scratch copy with
   `#print axioms AlgebraicGeometry.diagonalConormal_affine_ideal_class_core`; it reports
   exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The ring
   equivalence comes from proved colimit uniqueness, and the section lift from a proved
   kernel theorem; no data depends on an unproved existence theorem. Verdict: pass.
3. No statement was split off and no new node or hole was added. Checked the argument's
   empty-open and zero-ring cases: the affine pushout theorem requires only the stated
   affine-open hypotheses, and the generator containment and kernel range theorem have
   no nontriviality hypothesis. Verdict: pass.
4. Read the affine pushout theorem and the upstream sectionwise kernel proof. Repeated
   LeanFinder with a query about affine open rectangles and diagonal annihilation, and
   searched the local geometry library with tensor/section and diagonal/ideal/kernel
   terms. The Spec diagonal results do not shorten this general open-chart proof; the
   other affine pushout modules concern inverse-image sheaf pushouts. The direct existing
   route is appropriate. Both new imports supply lemmas used explicitly; the original
   public imports supply the statement API. Both old proof dependencies are fully listed
   under No longer needed. Read `dag/units/sk-thm-picard-duality.json`: its statement,
   steps and realized record are untouched, and this calculation changes only the route
   below the unit. Verdict: pass.
5. Compared the node JSON: only `proof`, `proof_deps`, and `proof_origin` changed. Its four
   steps match the Lean proof: section pushout, colimit equivalence with projections,
   multiplication-ideal containment, and kernel-section lift. The empty proof_deps agrees
   with use of proved Mathlib/upstream tools rather than the old planned nodes. Statement
   and Lean record remain unchanged; no new nodes require checking. Verdict: pass.

Second reading changed only this report, adding the independent audit. No Lean or DAG
repair was necessary. Closed one hole and added zero holes, as listed above.
