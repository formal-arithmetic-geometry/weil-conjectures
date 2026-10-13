## What changed

`Sheaf.RingTheory.ArtinianCoefficientPresentation` now selects finite generators using
Hopkins–Levitzki and `IsNoetherian.noetherian`, applies a fixed-generator coefficient
adjustment claim, and proves the final algebra-generation clause from Mathlib adic
surjectivity. The private generation lemma does not use the characteristic or H1 hypothesis.
Its proof identifies the image of the contracted maximal ideal, proves that contraction
nilpotent, proves nilpotent-adic completeness, and uses the residue section to obtain
surjectivity modulo that ideal. No existing statement, definition, or public import changed.

Added proof imports: `Mathlib.RingTheory.HopkinsLevitzki`,
`Mathlib.RingTheory.AdicCompletion.Functoriality`, and
`Sheaf.RingTheory.NilpotentCoefficientAdjustment`. Both delivered modules compile cleanly
with lcompile.py. The source's coefficient-field claim was read at
https://stacks.math.columbia.edu/tag/07FG because the local literature source is absent.

## Proved and sorry left

Closed the original hole in `Algebra.exists_artinian_coefficient_presentation`
(node `lem-weil-pbc-artinian-coefficient-presentation`). It is a decomposition, not an
axiom-free completion: one original hole closed, one new hole added, net zero.
The generator selection and algebra-generation arguments are complete Lean proofs.
The named private helpers `Algebra.complete_of_nilpotent` and
`Algebra.adjoin_eq_top_of_residue_section` contain no sorry.

The only delivered sorry is `Algebra.exists_nilpotent_coefficient_adjustment`, node
`lem-weil-pbc-nilpotent-coefficient-adjustment`, in
`Sheaf.RingTheory.NilpotentCoefficientAdjustment`. It states exactly the induction claim
for already fixed generators of a nilpotent maximal ideal. It omits the generator
existence and algebra-generation conclusions of the original theorem. Its docstring and
node give the complete source argument, including the finite differential obstruction
and why coefficients from the base field act through their residues on the last layer.

## No longer needed

No existing imports removed, and no entire downstream module is claimed globally pruned.
The old source did not import `Sheaf.RingTheory.ExistsLiftOfFieldCharP` or
`Sheaf.RingTheory.JacobiZariskiHomologySequence`; their nodes are now planned dependencies
of the new adjustment claim rather than direct dependencies of the outer proof. Neither
module is claimed pruned from the mathematical argument. The new holed module keeps only
the imports needed by its statement; its future lifting and homology proof is described
in its docstring and DAG.
The original node's direct proof dependencies `def-weil-pbc-noetherian-ring`,
`def-weil-pbc-mv-polynomial-ring`, `def-pc-field-extension`,
`lem-weil-pbc-field-char-p-nilpotent-lifting`, `def-weil-pbc-kahler-differentials`,
`lem-weil-pbc-jacobi-zariski-homology-sequence`, and `def-weil-pbc-smooth-ring-map`
are replaced by the new claim and the Artinian/Noetherian/nilpotence Mathlib leaf.
The claim retains the needed field, polynomial, differential, lifting, and homology
nodes in its own proof dependencies; the outer generation proof uses none of them.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction. The original eight-step plan combines two
separate issues: coefficient adjustment and ordinary generation by a coefficient
section plus ideal generators. The latter has a direct Mathlib proof and is now closed.
The named local Stacks source file is not present in this checkout; the official Tag 07FG
page supplies it. LeanSearch returned Internal Server Error, recorded as unavailable;
LeanFinder, Loogle, and grep searches were available and found no adjustment theorem.

Checked the new claim on the field case (m=0, t empty or consisting of zeroes): the inverse
residue isomorphism and c empty suffice. Finite families with redundant zero generators
also satisfy the same claim. Nilpotence exponent zero cannot occur in a nontrivial local
ring. The claim makes no finiteness assumption on the residue field, matching the source.
Its nilpotence-plus-fixed-generators assumptions are precisely those used by the source
induction and introduce no new restriction on the original Artinian theorem. The unit
route is unchanged; this node is below the unit's realized steps.

## New nodes

`lem-weil-pbc-nilpotent-coefficient-adjustment`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-nilpotent-coefficient-adjustment.json`,
is the fixed-generator coefficient claim (Tag 07FG, induction paragraphs), stated in
`lean/Sheaf/RingTheory/NilpotentCoefficientAdjustment.lean`. It is strictly the
coefficient-adjustment part of the argument; its conclusion contains no existence of
maximal-ideal generators and no algebra-generation equality. No change record is needed,
since every existing signature, definition, visibility, and public import is unchanged.

## Second reading by K4

1. PASS. Compared the delivered module with the repository using diff. The existing
   definition, theorem signature, docstrings, visibility, and four public imports are
   byte-for-byte unchanged. Changes are three proof imports, two private proved helpers,
   and the original theorem's proof. No change record is necessary.
2. PASS. Compiled both files in import order through lcompile.py without errors or
   warnings. The only sorry is the named public coefficient-adjustment theorem listed
   above. No forbidden trust feature or holed definition occurs. Scratch axiom checks
   confirm the helpers use only standard axioms; the outer theorem depends additionally
   on sorryAx through the explicitly reported adjustment claim.
3. PASS AS DECOMPOSITION. Independently read official Stacks Tag 07FG. The new claim
   isolates its coefficient adjustment for fixed generators, omitting both generator
   existence and algebra generation, which the delivery actually proves. It is true
   for the field case, an empty family, redundant zero generators, and arbitrary residue
   extensions satisfying the H1 hypothesis. Nilpotent maximal ideal plus a finite
   generating family suffices for the induction; Artinian is unnecessary there.
   Checked the square-zero layer, constant coefficient of the lifted map, finite
   differential obstruction, and multiplication of the remaining discrepancy by base
   coefficients through their residues. The docstring and node describe the full
   induction. Independent LeanFinder, Loogle, Mathlib source and project searches found
   no existing adjustment theorem. The remaining induction cannot be closed in a few
   minutes; one hole closed and one added, net zero, is reported explicitly.
4. PASS. Hopkins-Levitzki supplies generators and nilpotence, and the general Mathlib
   adic surjectivity lemma proves generation without the adjustment hypotheses. Checked
   the completeness helper, contraction nilpotence, ideal-map equality, and residue
   surjectivity. No shorter applicable coefficient-adjustment route was found. Proof
   imports are private and needed; the new module's public imports serve its signature.
   All seven removed direct proof-dependency nodes are listed above. No physical source
   import or whole module was pruned. Checked sk-thm-p1.realized: this supporting node
   is below its realized steps, and no unit route is bypassed.
5. PASS AFTER REPAIR. Existing node changes are confined to proof, proof_deps and
   proof_origin. New node fields and verbatim Lean statement match its module. Its
   proof_deps are the union of its proof-step uses. Added the polynomial-ring dependency
   used by the truncated-polynomial lifting step, which the first report claimed retained
   but the new node had omitted. Added independent search evidence. Corrected the report
   to distinguish planned DAG dependencies from imports that were never in the old file.

Second reading changed only node dependency/search metadata and the report; Lean proofs
and statements were retained. The delivery remains a decomposition with no claimed
whole-module pruning. Source checked: https://stacks.math.columbia.edu/tag/07FG.
