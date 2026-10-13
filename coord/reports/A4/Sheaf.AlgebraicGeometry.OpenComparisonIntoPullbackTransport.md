## What changed

Replaced the sorry in
`AlgebraicGeometry.SingleComplexBaseChange.exists_open_comparisonIntoPullback_transport`
with a reduction to the literal termwise restriction of P, followed by the existing
proved representative-naturality theorem. The original declaration's signature,
visibility, and docstring remain unchanged.

Added a proof-only import of
`Sheaf.AlgebraicGeometry.OpenRestrictedComparisonTransport`. Its single theorem
constructs the comparison only for the literal restricted complex, including its
K-flatness certificate and its derived identification. It has no arbitrary second
representative Q or prescribed identification eQ. Two proved private helpers package additive representative naturality and the
composition of comparison squares. The main proof supplies that
missing representative-change argument: it constructs the derived isomorphism
`eR ≪≫ eQ.symm`, lifts source cohomology transport to the tensor algebra using
`exists_comparisonSourceIso`, extends and forgets scalars, applies
`comparisonIntoPullback_naturality`, and composes the comparison squares.

Updated the existing node's proof and dependencies to follow this reduction.
No definitions, existing signatures, public imports, or unit-level route changed.

## Proved and sorry left

Closed in the item:
`AlgebraicGeometry.SingleComplexBaseChange.exists_open_comparisonIntoPullback_transport`
(node `lem-pc-open-comparison-into-pullback-transport`). No sorry remains in that module.

Added one remaining sorry:
`AlgebraicGeometry.SingleComplexBaseChange.exists_open_restricted_comparison_transport`
(node `lem-pc-open-restricted-comparison-transport`), in the new module
`Sheaf.AlgebraicGeometry.OpenRestrictedComparisonTransport`.

This is a decomposition: one upper hole closed and one strictly narrower hole added,
net zero holes. The representative-change part is proved using existing declarations.
The new theorem fixes the second complex to the actual restriction of P and constructs
its identification; it does not assume an arbitrarily supplied representative on U.

## No longer needed

No original import was removed and no module is claimed pruned from the targets'
closure. The open-restriction, derived-composition, and tensor-model dependencies
remain in the literal-restriction lemma's planned proof. Source transport and
representative naturality are used directly in the main proof. The original seven
proof dependencies are thus retained directly or through the new node.

The old direct proof dependencies now delegated to the new literal-restriction
node are `lem-pc-ringed-spaces-derived-pullback-composition`,
`lem-pc-open-restriction-stalk-extension-iso`, `lem-pc-kflat-open-restriction`,
`def-pc-base-derived-tensor-cohomology-model`, and
`lem-weil-pbc-module-stalk-pullback`. They remain needed in that lower argument;
none is claimed globally pruned. The composition declaration also occurs in the
unchanged signature and its proof-local abbreviation β.

An attempted additional import of
`Sheaf.AlgebraicGeometry.Modules.IsKFlatRestriction` was removed from the main module;
the literal-restriction lemma supplies its K-flatness certificate. This is not claimed
as global pruning, since that theorem remains a dependency of the new node's proof.

## Where the brief, the DAG or earlier work was wrong

The existing dependencies provide underived restriction-stalk isomorphisms and
representative naturality, but not the comparison square on literal restrictions.
That square and the natural derived stalk comparison are now isolated as a separate
item rather than leaving implicit glue in the upper proof. The literature source was
read at Stacks Tags 0DJ8 and 0DJ9; its local restriction argument is expanded in the
new theorem's docstring and node. Searches found no existing full comparison square.

The unchanged module compiles locally. A broad initial `dsimp` was removed to keep
large comparison constructions abstract. The main declaration uses transparency controls set to true, scoped to that one
declaration. The original module defaults are unchanged. The private additive
naturality helper uses the original false settings, which allow the necessary
scalar-extension conversions without unfolding those constructions throughout the
main proof. The natural isomorphism and restricted comparison witnesses are extracted
explicitly with Classical.choose inside the theorem proof; no new definition chooses
data. This avoids repeated existential-elimination motives containing the large
comparison types. The full theorem and both private helpers compile through lcompile.py. A scoped
unusedVariables linter option preserves the original hP/hQ binder names inside the
forall statement without warnings; no binder is renamed. The delivery dry run checks
the complete set, its axiom probe, and the maintainer preflight. The K-flatness certificate is part of the literal-restriction conclusion, avoiding
an additional import in the main module.

## New nodes

`lem-pc-open-restricted-comparison-transport` states and plans the open comparison
square for the literal termwise restriction of a K-flat complex, before changing its
representative. It inherits the item's chapter and unit. Its docstring records the
construction of the natural stalk comparison, restriction counit and derived
identification, source tensor transport, and counit-compatible comparison equation.
Empty opens have no z; top opens, zero complexes and zero stalk rings introduce no
extra hypotheses. No coefficient morphism, affine hypothesis or base-flatness is used.
No change record or forced adaptation is needed.

## Second reading by A4

1. **Existing interface: pass.** Compared the delivered main module with the
repository using diff. Its existing theorem signature and docstring are byte for
byte identical. The only additions are two proved private helpers, a proof-only
import, declaration-scoped elaboration/linter options, and the replacement proof.
No definitions, public imports, or target statements change. The existing node
changes only proof, proof_deps, and proof_origin.

2. **Proof and trust: pass.** Both delivered modules compile through lcompile.py
without warnings. The only remaining sorry is the named literal-restriction
transport theorem reported above, with its source, complete docstring argument,
and node. There are no definitions in either delivery, nor forbidden declarations
or attributes. The main proof first constructs the literal restricted complex,
then uses eR followed by eQ inverse, scalar extension of the source isomorphism,
and representative naturality. The identity Lq*(d);Lq*(eQ)=Lq*(eR) gives exactly
the required endpoint; the final square is composed using functoriality and
associativity. Existential witnesses are eliminated inside a theorem proof only;
no definition chooses arbitrary data from an unproved existence assertion.

3. **Split statement: pass as a decomposition.** Read the literal-restriction
statement and its node against Stacks Tags 0DJ8, 0DJ9 and 06YB, and the existing
K-flat-restriction and derived-pullback declarations. Its restricted complex is
explicitly constructed, not an arbitrary representative selected by existence.
The source stalk and final stalk ring stay the same under the open immersions;
the base stalk actions agree by the pullback condition. The K-flat counit supplies
hcQ and exact restriction supplies the identification eQ. Empty U has no z;
U=top gives the usual identity-restriction comparison; zero complexes and
arbitrary degrees do not require extra assumptions. The statement fixes Q and
constructs eQ, so excludes the independently supplied representative and
identification handled by the proved upper argument. Independent leanfinder,
loogle and grep searches (recorded in searches.jsonl), and rg in both library
roots, found no full literal-open comparison square. The nearby normalized-open
transport theorem additionally restricts opens in S and S', so is not this
statement or a direct replacement. The split is strictly part of the original
argument, but net holes remain zero: one closed, one added.

4. **Route and pruning: pass.** The two private helpers use existing source
transport and representative naturality followed by elementary category laws.
The two public imports supply signature declarations; the new import is private
and supplies the proof. No unused new proof import remains. The report now lists
all five old dependencies moved out of the parent's direct proof_deps and into
the lower node's plan; none is globally pruned. Read
 dag/units/sk-thm-picard-semicon.json: neither node is named in its realized
statement or step lists (which are empty), and no unit file or route is changed.
The original source-open step is retained rather than bypassed.

5. **DAG agreement: pass.** Both node lean.statement fields match their actual
Lean signatures verbatim, and each proof_deps equals the union of its proof-step
uses. The parent node records literal restriction, representative change and
composition exactly as the proof does. The new node has source, proof steps,
search records, split status, created item/group/date, blueprint provenance,
chapter/unit and the correct new Lean module/file/declaration. No cycles are
introduced by pointing the parent at this new lower lemma.

**Changes made by this reader:** clarified direct-dependency relocation and
pruning in the report and appended this independent review. The Lean proofs and
node statements required no repair. The scratch-copy #print axioms check
shows no axioms for compose_comparison_square; the main theorem, additive helper
and split theorem use only propext, Classical.choice, Quot.sound and sorryAx.
The additive helper also rests on still-open imported dependencies, so closing
the new literal-restriction lemma alone would not yet remove every sorryAx from
the upper theorem. The scratch probe was removed. A dependency-closure check
examined 238 nodes below the new lemma and found no path back to the parent.

**Delivery verification:** deliver3.py --no-push printed OK: compilation, axiom
probe and maintainer preflight passed. Review class CODEX reflects the added
module/node and its explicitly reported remaining sorry.
