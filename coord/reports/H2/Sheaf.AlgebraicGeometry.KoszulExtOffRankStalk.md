## What changed

Replaced the sorry in `AlgebraicGeometry.koszulRegularImmersion_ext_offRank_stalk`
with a complete compiled proof from existing rank and dual-cohomology lemmas and
one new comparison theorem. The signature and visibility are unchanged.

Added `Sheaf.AlgebraicGeometry.AffineKoszulScalarExtComparison`, whose sole theorem
identifies scalar Ext on a single affine Koszul chart with the associated sheaf
of dual Koszul homology in every integer degree. It has no global regularity
hypothesis, rank function, distinguished point, off-rank exclusion, or tensor
pullback conclusion. It is a local representation step, not a restatement of the item.

The item proves the rank identification, applies the algebraic dual vanishing,
transports the resulting zero object through associated sheafification, proves
local zero implies a zero stalk by restricting representative germs to V∩U,
and uses the existing tensor-pullback stalk comparison. That generic comparison
is a tool from the proper-base-change unit: it transports ordinary module stalks,
without using any proper-base-change theorem or bypassing the Picard unit route.
The unit record has no realized statement or step assigned to this item.

Updated the item's DAG proof and proof dependencies to this compiled argument.
Only the sandbox was edited; compilation used lcompile.py.

## Proved and sorry left

Closed: `AlgebraicGeometry.koszulRegularImmersion_ext_offRank_stalk`
(`lem-sc-koszul-ext-off-rank-stalk`), 1 of 1 original holes.

Added and still sorry:
`AlgebraicGeometry.affine_koszul_scalar_ext_comparison`
(`lem-sc-affine-koszul-scalar-ext-comparison`). Its proof is exactly `by sorry`,
with the source and full proof in its docstring and matching DAG node.
No sorry remains in the item or its private stalk helper.

This is a decomposition: one upper hole closed, one lower hole added, net zero
holes. It is not an unconditional proof of Koszul Ext vanishing. Existing
imported declarations may still depend on other named sorries.

Both delivery modules compile cleanly using lcompile.py. Edge checks for the
new comparison: n=0 resolves A and gives A in degree zero; negative degrees
have zero dual complex terms; an empty affine chart has only zero module
sheaves; a unit ideal has zero quotient and an acyclic regular resolution.
The proof of the item also handles rank zero, and an empty Z has no z to check.

## No longer needed

Removed direct proof imports from the item:
`Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel`,
`Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification`, and
`Sheaf.Paper.DerivedInternalHomRestrictOpen`.
Their nodes (`lem-sc-derived-hom-finite-free-model`,
`lem-sc-affine-quotient-resolution-sheafification`, and
`lem-sc-derived-internal-hom-restrict-open`) now belong to the new affine
comparison's proof plan and stay imported there. They are not globally pruned.
All three other original proof-dependency modules are used in the item.
No node or module is claimed to be no longer needed in the full target closure.

## Where the brief, the DAG or earlier work was wrong

No false statement or changed interface was found. The original plan omitted
an explicit affine comparison interface connecting the sheaf Ext expression
with the recorded algebraic dual complex; the new theorem supplies exactly
that missing bridge. The existing comparison lemmas alone do not provide its
finite-free coordinate and Hom-complex identifications in one application.

The literature checkout is absent on this machine. The cited source was read
online at https://stacks.math.columbia.edu/tag/0BQZ, proof of Lemma 48.15.5.
The new theorem follows that finite free Hom computation and expands the
sheafification and supplied-universe comparison needed by the existing interface.

## New nodes

`lem-sc-affine-koszul-scalar-ext-comparison` in
`dag/nodes/sec-picard-framework/lem-sc-affine-koszul-scalar-ext-comparison.json`:
local scalar Ext representation by associated dual Koszul homology. Its
source is Stacks 0BQZ (finite free Hom computation) and 08DM, Lemma 20.46.9 (corrected in second reading).
LeanSearch was attempted but unavailable (Internal Server Error). Lean Finder,
Loogle, grep, the Sheaf/source library, and the whole imported
blueprint were searched; no equivalent interface was found. Its proof plan
retains the original resolution, restriction, and finite free Hom nodes.
No change records or forced adaptations are required.

## Second reading by H2

1. **Statements and accidental changes.** Compared the delivered item with the repository version. The target declaration has the identical signature and visibility; only proof-local imports, a private helper, and the proof body changed. The added comparison theorem is a separate local representation statement with no extra target hypotheses. Verdict: pass.

2. **Compilation and axioms.** Compiled both sandbox modules with `lcompile.py --all`; both compile cleanly. The item has no `sorry`, and the only remaining `sorry` is the named comparison theorem, with a source, complete proof plan, and matching node. No forbidden declarations occur. Scratch-copy `#print axioms` checks show only `propext`, `Classical.choice`, and `Quot.sound` for the private helper, and these plus `sorryAx` for the item and split theorem. Verdict: pass as a decomposition relying on documented open statements.

3. **New statement.** Checked the comparison theorem against its Lean signature and edge cases recorded above (empty sequence, negative degree, empty chart, unit ideal). It is strictly more local than the target and is not a restatement of the target. Its node, declaration, source, proof steps, and dependencies agree. Independent Lean Finder search for finite-projective module Hom sheafification, Loogle search for Hom complexes, and grep for dual complex usages found no equivalent affine-chart interface. The existing affine pseudo-coherent RHom theorem takes already sheafified complexes and still needs the quotient, coordinate, and restriction identifications; it does not close the new theorem in one application. Checked Stacks 0BQZ and its cited 08DM directly. Corrected the supplementary reference from 0GM8 (a stalk comparison) to 08DM (the strictly perfect internal Hom calculation). Verdict: pass as a necessary decomposition.

4. **Route and pruning.** The item uses the conormal basis/frame, dual-complex vanishing, the new affine comparison, local zero-to-stalk helper, and tensor-pullback stalk comparison. The removed direct imports are transitively used by the new comparison module; no unit step is bypassed, and the item has no realized unit step to preserve. Verdict: pass.

5. **DAG agreement.** Checked both node records and the module declarations. Proof dependencies and proof origins describe the compiled route; the new node has all required creation, source, search, blueprint, and Lean fields. Verdict: pass.

Changed during second reading: corrected the new theorem's supplementary source citation from 0GM8 to 08DM in its docstring, node, and report; added independent search and axiom-check results. No Lean statements or proof bodies changed.
