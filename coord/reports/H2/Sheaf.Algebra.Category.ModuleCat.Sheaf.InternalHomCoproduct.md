## What changed

Proved `SheafOfModules.internalHomCoproductFanIsLimit` in
`Sheaf.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct` without changing its signature
or either public import. Private helpers construct local transposition of internal-Hom maps,
prove involutivity and compatibility with precomposition, and lift those laws to sheaf morphisms.
The fan lift is the transpose of the coproduct descent of the transposed projections.
Factorization and uniqueness use the original cofan universal property.
Updated the existing node's proof, proof dependencies and proof origin to match this route.
Change record: `coord/changes/internalHomCoproduct-private-scope.md` documents the static
interface flag on commands scoping private helpers; no public signature changes.
All helpers are proved, with real explicit data constructions; no new modules or nodes were added.

## Proved and sorry left

Closed one of one original holes: `SheafOfModules.internalHomCoproductFanIsLimit`
(node `lem-sc-internal-hom-coproduct-fan`). Added zero holes. No sorry remains in the item
or is added elsewhere. The axiom probe prints exactly `propext`, `Classical.choice`, `Quot.sound`.
The file compiles without warnings using lcompile.py. The construction handles an empty index
and zero summands with the same universal-property proof, and retains separate universes u, v, w.

## No longer needed

No imports were removed: the two original public imports remain necessary for the statement.
The proof does not need `lem-pc-sheaf-modules-tensor-closed` or its module
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed`; that module was not imported originally.
Its tensor/sheafification route is replaced by explicit local transposition. The node's statement
dependencies are unchanged; only its proof dependency on tensor closure is replaced by the existing
`def-pur-sheaf-hom`, whose source module the item already publicly imports.
No unit statement or realized proof step is bypassed (the unit record's realized lists are empty).
Do not prune internal Hom itself or its sheaf-condition proof: they are still used by the statement.

## Where the brief, the DAG or earlier work was wrong

Repair of return X-86f1c (head 86f1c920d), 2026-10-13: the accepted delivery failed
during batch source-link-tree creation (`cp -as`), before a Lean compiler error was
reported. Revalidated the sandbox module with lcompile.py (exit 0, no warnings) and
with scompile.py on the project server (exit 0, compiled in 7.3 seconds). The repair
uses deliver3.py to fetch current sheaf-dag and reconstruct the delivery commit on
that base, rather than reuse the returned commit. The mathematical proof and its
signature need no adjustment for this infrastructure return. The final dry run
checks the reconstructed commit; actual batch landing remains the maintainer's check.

The suggested tensor-closure dependency has equal site-object/morphism universes and explicit
sheafification assumptions, whereas this item's statement has independent u and v and no such
assumptions. The target statement is true; no interface change is necessary. Direct transposition
uses only the existing internal Hom and proves the more general statement already requested.
The second reading updated the original tensor-based theorem docstring to describe the
implemented direct-transposition proof, consistently with the DAG and inline comments.

Searches: LeanFinder for internal Hom sending coproducts to products returned generic monoidal
closure/adjunction results but no applicable sheaf theorem. Loogle found Fan.IsLimit.mk, which
is used. msearch grep found no homObj/coproduct or transpose theorem. Local rg of the source and
statement libraries found tensorHomEquiv/MonoidalClosed, whose additional hypotheses were checked.


## Earlier second reading (a previous round; superseded)

1. Compared the entire delivered Lean module against the repository with `diff -u`.
   PASS: the only existing declaration's signature is byte for byte identical, including
   universes, variables, visibility, notation and both public imports. Added helpers are all
   private; the conservative static scope flag is documented in
   `coord/changes/internalHomCoproduct-private-scope.md`. No target or public definition changes.
2. PASS: independently compiled the delivered module with lcompile.py without warnings.
   Read all explicit pairing/transposition data and proofs: no hollow definition, arbitrary
   unproved witness, sorry, axiom, unsafe, opaque, extern, implemented_by or kernel bypass.
   A fresh scratch copy probes all nine private helpers and the public theorem with
   `#print axioms`; only propext, Classical.choice and Quot.sound occur.
3. PASS: zero split-off statements and zero added holes. The local pairing is bilinear by
   the two linearities of the input map. Restriction compatibility gives the transpose;
   its involutivity and precomposition law have explicit proofs. The universal-property
   argument covers an empty indexing type, singleton families and zero summands without
   nonemptiness or nonzero hypotheses. No separate edge-case assumption enters the proof.
4. PASS: independently searched for homObj transpose/flip in the source library, Sheaf and
   Mathlib with rg and msearch grep, and checked Fan.IsLimit.mk with msearch Loogle.
   Existing presheaf tensor curry/uncurry and sheaf MonoidalClosed results require equal
   site universes; the original theorem allows independent u and v. No applicable shorter
   theorem was found. Both public imports supply signature symbols and remain necessary.
   The sole old proof dependency lem-pc-sheaf-modules-tensor-closed is fully listed under
   No longer needed. It was never imported here, so no module is claimed globally pruned.
   Checked dag/units/sk-thm-picard-duality.json: its realized lists are empty, and this local
   argument does not alter or bypass any unit statement or step.
5. PASS: compared the node JSON against the original: only proof, proof_deps and
   proof_origin changed. Each proof step now matches the actual local-transposition
   construction and fan universal-property proof. The union of uses is exactly
   def-pur-sheaf-hom, whose recorded declaration is the existing imported homObj.
   No new nodes require validation. Verified the cited bilinear correspondence in
   [Stacks 03EO](https://stacks.math.columbia.edu/tag/03EO).

Second reading changed the theorem's stale tensor/sheafification proof docstring to the
actual direct-transposition argument and corrected the corresponding report sentence.
The checked Lean proof and DAG were retained unchanged. One of one original holes is
closed, zero holes are added, and zero statements are split off.

## Second reading by H2

1. Compared the delivered module with the repository version using `diff`; the existing
   theorem signature and both public imports are unchanged byte for byte. Added helpers are
   private, and the interface change record documents their scope.
2. Compiled the module with `lcompile.py`; it succeeds without warnings. There are no
   `sorry`, hollow definitions, forbidden declarations, or arbitrary witnesses. The proof
   uses only explicit pairing/transposition constructions and universal properties.
3. No statements were split off and no holes were added. The sole original hole,
   `SheafOfModules.internalHomCoproductFanIsLimit`, is closed; the empty-index and zero-
   summand cases are covered by the same fan and cofan universal properties.
4. Searched Mathlib, Sheaf, and the source library for an applicable internal-Hom
   coproduct theorem. Existing tensor-Hom results require hypotheses absent here, so the
   direct transposition route is the shortest applicable proof. Both public imports remain
   necessary.
5. The DAG node proof, dependencies, and origin match the implemented three-step route,
   and the unit's realized list is empty, so no unit step is bypassed.

Changed only this report section; the Lean proof and node metadata were otherwise retained.
