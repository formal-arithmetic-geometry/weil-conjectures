## What changed

Proved `AlgebraicGeometry.freeCechComplex_block_equiv` with its original signature.
`FreeCechTupleBasis` defines the actual forward map from tuple blocks to the evaluated
Čech module, using product lifts, free generators and coproduct injections. Its generator
formula `freeCechTupleMap_single` is proved. `FreeCechTupleDifferential` states commutation
of this specific forward map with the differential. The original theorem constructs
inverse equivalences from degreewise bijectivity, evaluates the forward commutation
identity on an inverse image and uses injectivity to establish the required identity.
Only a private proof import is added to the original module; its public interface is unchanged.

All three modules compile locally without warnings. New statements were checked against
Stacks Tags 03AT and 03F5 read online, since the literature checkout is absent here.
The original node's proof and dependencies now follow this reduction. No unit route is bypassed.

## Proved and sorry left

Proved: `AlgebraicGeometry.freeCechComplex_block_equiv` (one original sorry eliminated)
and `AlgebraicGeometry.freeCechTupleMap_single`.

Remaining sorries introduced by this delivery:
- `AlgebraicGeometry.freeCechTupleMap_bijective`, node
  `lem-weil-pbc-free-cech-tuple-basis`, module `Sheaf.Paper.FreeCechTupleBasis`.
- `AlgebraicGeometry.freeCechDifferential_compatibility`, node
  `lem-weil-pbc-free-cech-differential-compatibility`, module
  `Sheaf.Paper.FreeCechTupleDifferential`.

Each is strictly part of the argument: bijectivity alone says nothing about differentials;
differential compatibility alone says nothing about invertibility. Neither restates the item.
No sorry is left in the item or any definition. The proofs of these two helpers remain work
for subsequent workers; this is a reduction, not a sorry-free transitive closure.

## No longer needed

No original imports removed. The power-set module is retained for its definitions only;
none of its contractibility, exactness, or homotopy theorems is used. Thus the node
`lem-weil-pbc-power-set-complex-contractible` is a statement dependency but not a proof
dependency of this item's assembly. The sheafification and étale-site nodes are now
statement dependencies here and used below in the tuple-basis node, rather than proofs
needed directly by the assembly. No whole original module can yet be pruned.

## Where the brief, the DAG or earlier work was wrong

The original proof plan bundles the product-basis bijection and the face computation
into one elementary step. Mathlib supplies the ingredients, but not their precise
interface with this evaluated Čech complex. The delivery isolates those two obligations
with explicit definitions. No mathematical error or changed target statement was found.
Edge cases checked in the argument: empty family, empty lift blocks, degree zero, zero
ring and noncommutative ring. `DFinsupp.lsum ℕ` avoids incorrectly requiring commuting
left actions of the possibly noncommutative coefficient ring.

## New nodes

`lem-weil-pbc-free-cech-tuple-basis` states bijectivity of the explicitly defined tuple map.
It realizes the degreewise decomposition of Tag 03AT with coefficients as in Tag 03F5.

`lem-weil-pbc-free-cech-differential-compatibility` states commutation of that map with
alternating deletion, without any bijectivity or exactness assertion. Its proof docstring
spells out the face action, preservation of the block index, and the signed sum.

No change records are needed: no existing signature, definition or public import changed.

## Second reading by R2

1. **Visible declarations and signatures.** I compared the delivered target module with the
repository copy. The theorem `AlgebraicGeometry.freeCechComplex_block_equiv` has the same
signature byte for byte; the only change is its proof and one proof-only import. The two
new helper declarations have signatures matching their DAG nodes. Verdict: pass.

2. **Compilation and trust.** `lcompile.py --all` compiles `FreeCechTupleBasis`,
`FreeCechTupleDifferential`, and `FreeCechComplexBlockEquiv` without errors or warnings.
Scratch-copy `#print axioms` checks show only `propext`, `Classical.choice`, and
`Quot.sound` for both tuple definitions and `freeCechTupleMap_single`; the target and
two open helpers additionally use `sorryAx`, exactly as expected. The delivery probe
also passes. The files contain no `axiom`, `unsafe`,
`opaque`, `implemented_by`, `extern`, or hollow definition. The only remaining `sorry`s
are the two named split theorems and are documented above. Verdict: pass.

3. **Truth and strength of split statements.** I read Tags 03AT and 03F5 and checked the
empty family, empty lift block, degree-zero, and zero-ring cases. `freeCechTupleMap_bijective`
asserts only the degreewise basis bijection. `freeCechDifferential_compatibility` asserts
only commutation of the explicit map with alternating deletion. Neither restates the target,
adds hypotheses, or claims exactness. Searches in the source library and Mathlib found no
existing declaration of either statement. The independent LeanFinder search found
`ModuleCat.freeHomEquiv` and `PresheafOfModules.freeObj_map`, which supply ingredients
but do not assert either helper. Loogle found no matching Cech face theorem. I checked
`FormalCoproduct.cech` and `mapPower`, `AlternatingFaceMapComplex.objD`, and
`PresheafOfModules.evaluation_preservesColimit`: these validate the product projection,
signed face sum, and pointwise coproduct facts used in the two docstring proofs. A tuple
of length n+1 always has a zeroth projection, so its common base map needs no arbitrary
choice. With a noncommutative coefficient ring, the signs are central integers and the
`DFinsupp.lsum` extension uses natural-number scalar linearity. Verdict: pass.

4. **Pruning and imports.** The target proof uses exactly the tuple bijection and the
differential compatibility theorem, via `LinearEquiv.ofBijective`, evaluation on an inverse
image, and injectivity. The target retains all public imports required by its displayed
types; `FreeCechTupleDifferential` is a plain proof import. The power-set contractibility
module remains needed for the tuple differential definitions and no old proof dependency is
silently used. The complete old `proof_deps` removed from the target assembly are
`def-weil-presheaf-modules-sheafification`, `def-weil-pbc-etale-site`, and
`lem-weil-pbc-power-set-complex-contractible`; all remain statement dependencies, and
the first two enter the tuple-basis proof plan below. No entire module is pruned.
Verdict: pass.

5. **DAG and unit route.** The target node proof and `proof_deps` match the Lean reduction;
the two split nodes record their declarations, sources, searches, docstring proofs, and
blueprint ancestry. The unit route is retained: this is the degreewise decomposition step
used by the existing proper-base-change route, with no bypass of a realized unit step.
Verdict: pass.

I added the missing blueprint identifiers to the two new module docstrings and this
review record. No Lean declaration signature, proof, or node statement required repair.
