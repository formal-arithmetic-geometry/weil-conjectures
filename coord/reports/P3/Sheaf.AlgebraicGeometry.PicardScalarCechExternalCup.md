## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup_core`
with a complete Lean reduction. The proof extracts the three ordinary module
comparison witnesses, restricts the total cochain map to one bidegree, and uses
`cyclesMap_i` and `homologyπ_naturality` to identify the image cycle and class.
It applies the new ordinary module Cech comparison, substitutes the comparison
witness equations, then applies the existing
`scalar_moduleCohomologyPullback_comparison` twice and
`scalarCup_moduleCup_compatibility`. The definition of `externalCup` finishes the
argument. In particular, the scalar Ext identification is no longer bundled into
the remaining Cech hole.

The internal core now assumes both genuine cover equalities; its sole caller in
the same file passes the equalities it already had. The outer theorem's signature
and all definitions are unchanged. No other Lean module requires adaptation.
Ordinary module pullback is locally irreducible in this proof, preventing a final
reflexivity check from expanding the derived-functor implementation. File checks
compile the assigned module in about eleven seconds and the new module in about
five seconds, within the fixed sixty-second limit.

## Proved and sorry left

Replaced the false, unrestricted statement of
`AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup_core` by the documented
cover correction, and supplied a Lean proof of the corrected statement. This does
not prove the original unrestricted statement; it is an interface repair followed
by a decomposition. The already proved
`AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup` remains proved with
exactly its original signature.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.picardModuleCech_externalCup`, node
`lem-sc-picard-module-cech-external-cup`, in the new module
`Sheaf.AlgebraicGeometry.PicardModuleCechExternalCup`.
This is a decomposition: one hole closed and one added, not a net reduction of
holes. The remaining statement is strictly the ordinary module Cech part: it uses
one bidegree pairing and one target cycle, and contains neither a total cochain map,
scalar comparison witnesses, scalar Ext cup, nor scalar cohomology pullback.
The scalar/module cup and pullback bridges already existed and were imported;
their existing holes are not new statements of this delivery.

## No longer needed

Removed the direct proof import `Sheaf.Paper.CechCupPullbackCompat` from the assigned
module. Its refinement and cup comparison theorem is still needed in the plan of
the new ordinary module comparison, so no global pruning of that module is claimed.
The outer theorem's old seven proof dependencies are replaced by its actual sole
proof dependency `lem-sc-picard-scalar-cech-external-cup-core`; their substantive
work is retained under the corrected core and new ordinary comparison node.
Specifically, the outer node no longer directly uses:
`def-sc-cech-cup-product`, `def-sc-cech-refinement-cochain-map`,
`def-sc-field-linear-module-cohomology-operations`,
`def-sc-module-cohomology-cup-product`, `lem-sc-picard-cech-cup-pullback-compat`,
`lem-sc-picard-external-cech-cup-component`, and
`lem-sc-picard-scalar-cech-comparison`. The core no longer directly uses
`lem-sc-picard-cech-cup-pullback-compat`. These dependencies remain below the
core or new ordinary comparison; none is claimed globally pruned.
No source module or blueprint unit is bypassed or withdrawn. The unit's `realized`
arrays are empty, and the theorem-of-cube/Kunneth route is retained.

## Where the brief, the DAG or earlier work was wrong

The earlier core split claimed compatibility without genuine cover hypotheses.
This is false for the characterization used by `IsModuleCechComparison`, which
only states the alpha/beta equation. On a noncover the equation may have multiple
solutions and these need not preserve cup. See the explicit degree-zero example
in the change record. An initial clopen version of that example was discarded:
linearity over global sections forces its omitted component to vanish. The final
example uses a connected projective scheme with global functions k instead.

The source texts were not present under `literature/stacks-project` on this clone;
read the referenced Stacks pages 01FD, 0FKV and 0BED directly. Both 01FD and 0FKV
explicitly assume open coverings. The new theorem's proof in words specializes
these comparison squares, without an affine-intersection assumption.

Searches: LeanFinder returned only unrelated group-cohomology formulas; Loogle
found `HomologicalComplex.homologyπ_naturality`; Mathlib grep found no scalar/Cech
cup theorem. LeanSearch returned HTTP Internal Server Error, recorded as
unavailable. Repository searches located and reused the two scalar/module bridges.
A blueprint-wide search for external cup returned no duplicate blueprint node.

## Statement corrected

Restored `hUc : iSup U = ⊤` and `hVc : iSup V = ⊤` on the non-target helper
`picardScalarCech_externalCup_core`. The node records the old statement, reason,
source and every DAG citer. A declaration-use search found no external use of the
core. All transitive importers retain the same outer theorem statement and the
same definitions; no target meaning changes. The change record is
`coord/changes/picardScalarCech-core-covers.md`.

## New nodes

`lem-sc-picard-module-cech-external-cup` states ordinary module comparison for a
single prescribed external bidegree pairing and a product cycle with its exact
cochain image. Its proof refines both factor covers to the product cover, applies
the two refinement comparison squares, identifies the front/back Cech cup cycle
using restriction composition and monicity, and applies the Cech/sheaf cup square.
The source and full proof are in its docstring and node. Edge cases checked:
p=q=0 is the tensor section pairing, zero coefficients give zero cycles, and an
empty covering index set forces the corresponding scheme to be empty. No theorem
chooses data from an unproved mere-existence statement.


## Second reading by P3

1. Compared both delivered modules with the repository. The new ordinary module
   comparison has no predecessor. The outer theorem signature is byte for byte
   unchanged, and there are no definition changes. The only existing signature
   change is the two cover hypotheses on the core, declared in
   `coord/changes/picardScalarCech-core-covers.md`. A full-library declaration
   search found its sole caller in this module; the caller already has both
   hypotheses. Confirmed the noncover counterexample: on P1 the two distinct
   rational-point skyscrapers are quasi-coherent, global functions are k, and the
   single-open restriction and diagonal splitting differ while satisfying the
   degree-zero comparison equation. Thus the old core cannot be retained as a
   true theorem. Verdict: documented intermediate-statement repair; no target
   change, and no claim to prove the false original statement.
2. Compiled both files locally in import order without errors or warnings. Scratch
   copies with #print axioms for all three theorems list only propext,
   Classical.choice, Quot.sound, and sorryAx. The assigned module contains no
   direct sorry. The one new direct sorry is the public named theorem
   picardModuleCech_externalCup. No definitions, forbidden declarations or kernel
   bypasses were added. The cup witness is uniquely characterized, not arbitrary
   data from mere existence. Verdict: valid Lean reduction, still resting on the
   reported ordinary comparison and existing lower holes.
3. Read the ordinary comparison signature, front/back characterization, ordinary
   comparison alpha/beta equation, and cup characterization together. Checked
   p=q=0 (tensor of pulled-back global sections), zero coefficients, and empty
   covering indices (the covered scheme and product are empty). The maps transport
   scalar and module Cech homology via their common additive presheaf. Independently
   read Stacks [01FD](https://stacks.math.columbia.edu/tag/01FD),
   [0FKV](https://stacks.math.columbia.edu/tag/0FKV),
   [07MB](https://stacks.math.columbia.edu/tag/07MB), and
   [0BED](https://stacks.math.columbia.edu/tag/0BED); they support the refinement,
   degree-zero coefficient-complex cup formula, and comparison argument for covers.
   Independent LeanFinder, Loogle and Mathlib grep searches used different wording;
   repository and upstream searches found the existing generic cup/refinement
   comparisons but no theorem already performing these external scalar/module
   transports. Verdict: true and strictly smaller remaining statement; not a
   renaming of the core. Closing it requires the two cycle transports and coordinate
   identities, beyond a short application of the generic comparison theorem.
4. Followed the core proof through cyclesMap_i and homology projection naturality,
   then its ordinary comparison and the two existing scalar/module bridges. These
   are genuine reductions. All added imports in the assigned module are private
   proof imports. Public imports of the new module provide signature vocabulary;
   its private imports provide the remaining theorem's documented proof route.
   Listed every removed old proof dependency explicitly above. The cube unit's
   realized arrays are empty in the repository; its statement, steps and route are
   untouched. Verdict: no unit bypass and no global pruning claimed.
5. Checked every Lean signature against its node's verbatim lean.statement and
   checked the union of step uses against proof_deps. Existing-node edits stay in
   the stage-3 fields and the documented statement-change fields. The new node
   has the required source, chapter/unit, blueprint provenance, searches, creation
   and Lean records. Verdict: consistent after the following metadata repairs.

Second reading changed the new theorem's docstring and planned proof to name
existence of canonical comparisons on the product cover, their uniqueness,
refinement-map existence and Cech-cup existence. Added its private proof import
Sheaf.Paper.CechComparisonMapNaturality and the matching DAG proof dependency;
added the missing ordinary-pullback statement dependency. Retained the statement-change schema
label "P3 stage 2" and its empty base-DAG citer list: the base outer node did not
list the core in stmt_deps or proof_deps, though its Lean body calls it. Verified
that caller separately above. Extended independent search records and made the pruning list and interface-repair accounting explicit.
The Lean proof terms and theorem signatures from the first worker were retained.
