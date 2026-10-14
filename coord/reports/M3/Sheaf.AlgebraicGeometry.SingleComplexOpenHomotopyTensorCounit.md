## What changed

Closed `AlgebraicGeometry.singleComplexOpen_homotopy_tensor_counit` without changing
its signature or existing docstring. Added the proof-only import
`Sheaf.AlgebraicGeometry.SingleComplexOpenUnderivedTensorMate`.

The new module proves `AlgebraicGeometry.singleComplexOpen_underived_tensor_mate`.
It uses the existing `schemeMVOrdinaryOpenCounit_square`: its restriction comparison
is definitionally the same as our underived direct-image comparison. A private
categorical lemma conjugates the four tensor restriction factors without unfolding
scheme categories. Left-adjoint uniqueness handles the two open factors; tensor
composition is defined by inverse conjugation. Injectivity of the open mates
correspondence identifies the resulting horizontal mate.

The item's private `map_homotopy_counit_square` is fully proved. It represents an
arbitrary homotopy object by a complex, rewrites the induced counits as quotient
images, and proves equality degreewise. The target follows from the underived mate
identity and Mathlib's `mateEquiv_counit`.

Updated the item's DAG proof and recorded the proved underived lemma as a new node.
No definitions, existing statement signatures, instances, or public imports of the
item changed. The only dependency import of the new module used solely by its proof
is `Sheaf.AlgebraicGeometry.OrdinaryOpenCounitSquare`.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.singleComplexOpen_homotopy_tensor_counit`
(node `lem-pc-k3-open-homotopy-tensor-counit`).

Also proved the new theorem `AlgebraicGeometry.singleComplexOpen_underived_tensor_mate`
(node `lem-pc-m3-open-underived-tensor-mate`). All private helpers are proved.
No `sorry` remains in either delivered module; no hole was added or split off.
The proof uses the existing ordinary open counit square and its existing dependencies.

## No longer needed

No imports or modules were pruned. The old direct proof dependency
`def-pc-tensor-pullback-composition-iso` is no longer a direct dependency of
`lem-pc-k3-open-homotopy-tensor-counit`; it is used by the new underived mate node.
All other old proof dependencies remain direct dependencies. Tensor composition
is still in the target import closure, so this is dependency relocation, not pruning.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The plan did not name the existing ordinary open
counit square, whose comparison is definitionally the same as the underived one.
Using it avoids repeating the geometric calculation on sections.

The unit record `sk-thm-picard-semicon` has empty realized statement/step lists, and
this proof retains the assigned open-square counit route. The existing ordinary
open counit square is in the same unit and is used as a categorical/geometric tool.
Edge cases introduce no new hypotheses: the conjugation and quotient identities
hold for empty and top opens, zero modules and zero complexes, and arbitrary f.

## New nodes

`lem-pc-m3-open-underived-tensor-mate` in
`dag/nodes/sec-picard-framework/lem-pc-m3-open-underived-tensor-mate.json` records the
proved module `Sheaf.AlgebraicGeometry.SingleComplexOpenUnderivedTensorMate`. Its
statement has no homotopy, derived-category or additivity hypotheses and is exactly
the underived mate calculation used in step 1 of the existing node. Searches found
Mathlib's individual conjugation/restriction tools, not this named comparison.
LeanSearch was unavailable; LeanFinder, Loogle and grep ran and are logged.
Blueprint-wide search for "open tensor counit" returned no matching node.
No change record or forced adaptation is needed.

## Second reading by M3

1. Interface preservation: PASS. Read the full diff of the existing module against
   the repository and compared its theorem signature byte for byte, including all
   hypotheses, let bindings and conclusion. The signature and original docstring
   are unchanged. Only a proof-only import, a proved private lifting lemma, local
   elaboration options and the theorem proof were added. No definition or instance
   changed; the other delivered module is new. No change record is required.
2. Proof verification: PASS. Compiled both modules in dependency order through
   lcompile.py: 17.8 s for the underived module and 35.0 s for the item, without
   warnings or errors. Scanned both sources: no sorry, axiom, unsafe, opaque,
   implemented_by or extern; no data definitions were added. Scratch copies with
   explicit #print axioms for both public theorems compiled and showed exactly
   propext, Classical.choice and Quot.sound, without sorryAx. Removed the scratch
   copies before delivery. The chosen tensor adjunctions come from the existing
   proved, canonically pinned adjunction theorem; no arbitrary data witness from
   an unproved existence theorem was introduced.
3. New statements and search: PASS. No statement was split off with sorry. The new
   public underived mate theorem is a strictly earlier categorical calculation,
   with no complex or additivity hypotheses; its complete proof is supplied.
   Read every private helper: conjugation reverses the four factors correctly,
   left-adjoint uniqueness identifies the open factors, and the commuting-square
   congruence has the correct inverse orientation. Empty/top opens and zero
   modules/complexes require no extra assumptions or cancellations of noninvertible
   maps: all cancellations are of genuine isomorphisms or equivalences. Independent
   LeanFinder search for descent of counit squares, Loogle search for conjugation
   with composite adjunctions, Mathlib grep, and repository rg found the generic
   mates/conjugation tools already used, and a bounded-below mate lemma rather than
   an existing theorem for these named comparisons and arbitrary homotopy objects.
4. Route and pruning: PASS. Read the ordinary open counit square and both explicit
   sectionwise comparisons: they are definitionally identical. The underived
   argument uses this existing proved square, uniqueness and Mathlib mates laws;
   the upper argument is the direct degreewise quotient lift. The imports supply
   the signature constructions or the actual proof; the ordinary counit square
   and new underived mate are imported privately. No shorter matching result was
   found. Read sk-thm-picard-semicon.json: its realized statement list and sole
   realized step list are empty, and no recorded unit step is bypassed. Corrected
   No longer needed to list the relocated tensor-composition dependency explicitly;
   no module is claimed as pruned.
5. DAG agreement: PASS after repair. Both node lean.statement records match the
   signatures verbatim; proof_deps equals the union of step uses, and every named
   dependency exists. The existing node records the actual underived counit
   reduction and degreewise lifting. The new node has source, complete proof,
   proof origin, searches, creation, blueprint, chapter/unit and Lean records.
   Added def-pc-derived-mayer-vietoris-open-counit-model and
   def-pc-kinjective-mayer-vietoris-data to the relevant new-node steps and rebuilt
   proof_deps, to name the composition model and open adjunction used explicitly.

Second reading changed only DAG dependency completeness and report bookkeeping;
the Lean proofs needed no repair. One original hole closed, zero holes added,
zero split-off holes, and no modules pruned.
