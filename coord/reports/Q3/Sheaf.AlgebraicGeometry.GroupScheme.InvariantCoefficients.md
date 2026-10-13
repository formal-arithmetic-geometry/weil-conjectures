## What changed

Proved `AlgebraicGeometry.GrpObj.invariantCoefficient_mul` in
`Sheaf.AlgebraicGeometry.GroupScheme.InvariantCoefficients`, with its signature unchanged.
Added the proof-only import `WeilConjectures.AlgebraicGeometry.DualNumbersBaseChange`.
The existing pullback theorem constructs a unique lift of right translation preserving the
same epsilon. Group associativity proves its composition formula. Its comorphism fixes epsilon
on every open; expanding a dual number proves the coefficient formula and additivity.
All added helpers are private and proved. No existing public definition or signature changed.
The private lift uses the pullback universal property, which determines it uniquely, and the
underlying pullback theorem is already proved, without sorry.
Updated the item's proof route and recorded the existing pullback theorem as a DAG tool node.
Local compilation completed without warnings in approximately five seconds.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.GrpObj.invariantCoefficient_mul`
(node `lem-ag-invariant-coefficient-add`). No sorry remains in the delivered module and no hole
was added. This is a proof, not a decomposition. The added node attaches the already proved
`AlgebraicGeometry.Scheme.isPullback_dualNumbersProj` from the existing source library.
The proof works for arbitrary base schemes, arbitrary characteristic, empty opens and the
empty scheme; its ring calculation uses no nonzero or field hypothesis.

## No longer needed

None. The original two imports supply the infinitesimal-point definitions and additive
endomorphism type. Both original DAG dependencies are used. No original planned module or node
was bypassed. No additional diagonal-derivation or affine reduction theory is needed.

## Where the brief, the DAG or earlier work was wrong

The original two-step DAG plan cited only definitions for the lifted composition step.
The missing concrete interface is available as the already proved
`Scheme.isPullback_dualNumbersProj`; the updated route records its use explicitly.
No statement error or unit-route change was found. `sk-d-tangent` has no numbered steps or
realized-node requirements in its unit record. The blueprint ancestor command returns no
ancestor because the original node's created.item names a Lean module, but its recorded
blueprint.from points to `def-wf-lie-algebra-derivation`; the new tool node preserves that
recorded ancestor, with the original coefficient node in via.
Searches used LeanFinder, Loogle, Mathlib grep and project rg. LeanSearch returned Internal
Server Error. No existing DAG node attaches the pullback theorem, and the blueprint search
found no duplicate.

## New nodes

`lem-ag-dual-numbers-projection-pullback` records the already proved, arbitrary-scheme theorem
`AlgebraicGeometry.Scheme.isPullback_dualNumbersProj`, in
`WeilConjectures.AlgebraicGeometry.DualNumbersBaseChange`. Its statement is the exact cartesian
projection square used to construct the lift; its proof follows the source's explicit
square-zero evaluation and unique-factorization construction. No new Lean module, sorry or
change record is required. It is a generic tool below the unchanged unit route.

## Second reading by Q3

1. Interface preservation: PASS. Compared the sole delivered Lean module against the
   repository version. All existing declaration signatures, bodies of definitions,
   visibility and docstrings are byte for byte unchanged; the sole replaced existing
   proof is invariantCoefficient_mul. The new import is proof-only, and every new
   declaration is private. No change record or forced adaptation is needed.
2. Proof and trust: PASS. Compiled the module using lcompile.py with no errors or
   warnings (5.3 seconds). Read all new helper proofs and the final composition argument.
   A scratch copy with #print axioms for all 23 module declarations and the upstream
   pullback theorem compiled (5.0 seconds); every axiom list is contained in propext,
   Classical.choice and Quot.sound, with no sorryAx. Source scanning found no sorry or
   forbidden declaration. The private lift uses a proved universal property determining
   it uniquely; no arbitrary witness of an unproved existence theorem is chosen.
3. Split statements and edge cases: PASS. No statement or hole was split off. The one
   new DAG node attaches an existing proved pullback theorem, rather than restating the
   item. Checked its exact source signature and its evaluation/factorization proof.
   Identity translations, empty opens, the zero section ring, empty schemes and
   characteristic two require no exceptional step: the ring expansion and projection
   identities hold without division, cancellation or nonzero assumptions.
4. Route and pruning: PASS. Independent LeanFinder search for first-order product
   coefficients found no scheme theorem; Loogle found TrivSqZeroExt.snd_mul, already
   used by the ring simplification. Project and Mathlib rg searches found the existing
   pullback theorem and related diagonal coefficient modules, with no shorter proved
   scheme-level bridge. The imports supply the public infinitesimal-point and additive
   endomorphism types and the actually used proof-only pullback theorem. Both old
   proof dependencies remain used, so No longer needed is complete. Read the unit
   record: sk-d-tangent has empty steps and empty realized lists, which are preserved.
5. DAG agreement: PASS. Compared the existing node; only proof, proof_deps and
   proof_origin changed. The three recorded steps match the lift, associativity and
   sectionwise coefficient calculation. Their dependency union is exactly proof_deps.
   The new node records the existing theorem with its exact signature, source, complete
   proof route, searches and blueprint ancestry; it adds no Lean module or hole.

Second reading changed only this report by adding the independent review. No Lean or
DAG repair was needed. Holes closed: AlgebraicGeometry.GrpObj.invariantCoefficient_mul
(1 of 1 original holes). Holes added: none. Split off: none.
