## What changed

Recovery verification on 2026-10-13: retained the earlier reviewed Lean proof and
node records after checking their signatures, local-to-global argument, and Stacks
Tags 069C, 0B6G and 09U9. Both modules compiled again through `lcompile.py --all`.
`deliver3.py A4 Sheaf.AlgebraicGeometry.PerfectRelativeFiniteTor --no-push` now
prints OK and passes compilation, axiom probes and preflight (review class CODEX).
Nothing was pushed. This supersedes the earlier SSH-failure status preserved in
the previous reader's historical verification below; that reader's text is unchanged.

Replaced the whole proof of `AlgebraicGeometry.Scheme.perfect_hasFiniteTorDimensionOver`
with a compiling proof preserving its signature and visibility. It chooses a global
representative using the proved essential-surjectivity API and a K-flat scalar-restricted
resolution using `CochainComplex.exists_isKFlatResolution`. A new local-bound theorem
supplies neighbourhoods; the delivered main proof itself selects a finite subcover,
constructs common endpoints by finite induction, detects zero on all abelian stalks,
and reflects zero through the faithful underlying-sheaf functor.

Added proof-only imports of `Sheaf.Algebra.Homology.KFlatResolution` and
`Sheaf.AlgebraicGeometry.PerfectRelativeTensorLocallyBounded`. Added the latter module
and its node, and updated the original node's proof and proof dependencies. The new
statement has no compactness hypothesis and applies to any prescribed K-flat model;
it contains the local geometric and finite-complex argument, while the main module
proves the global uniformity and existential witnesses. No definition or existing
statement was changed. No forced adaptations are needed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.perfect_hasFiniteTorDimensionOver`
(node `lem-pc-perfect-relative-finite-tor`): no sorry remains in the item's module.

Added one hole in
`AlgebraicGeometry.Scheme.perfect_relativeTensor_locally_bounded`
(node `lem-pc-perfect-relative-tensor-locally-bounded`), in its own new module.
This is a decomposition: one upper hole closed, one strictly local hole added,
net zero new hole progress before accounting for shared dependencies. It is not a
complete proof of the local geometric theorem. Its complete natural-language proof
is in its docstring and node. Existing K-flat-resolution dependencies may still have
holes; no additional holes were added to them.

Both delivered modules compile without errors or style warnings via `lcompile.py --all`.
The finite-interval construction includes the empty cover and returns [0,0]; local
zero models and arbitrary test-module quantification were checked in the local proof.
The final proof requires no compactness of Y beyond the unchanged Noetherian assumption.

## No longer needed

None of the original imports or planned arguments is removed. The perfect-complex,
perfect-morphism and relative finite-Tor definitions remain necessary. The old proof dependencies `def-pc-perfect-complex` and
`def-pc-perfect-morphism` are no longer direct proof dependencies of the upper node where delegated to the new
local theorem, but remain statement dependencies and occur below it; this is not pruning.
No nodes or modules are claimed globally unreachable. The absolute Tor statements
`PerfectPseudoCoherentLocallyFiniteTor`, `QuasiCompactFiniteTorDimension`, and
`TorAmplitudeOpenLocal` were inspected but not imported: they tensor over O_X,
whereas this item tensors over f⁻¹O_Y. The new module directly imports the components
needed by its statement rather than the unused `FiniteTorDimensionOver` predicate.

## Where the brief, the DAG or earlier work was wrong

The plan's dependencies were definitions, not theorems implementing its non-elementary
local step. The new node exposes that missing argument without changing the plan or
the unit route. There is no mathematical dispute with the original statement.
The actual unit is `sk-thm-picard-duality`; its realization fields are empty and
unchanged, and the local-bound/finite-subcover route of this node is retained.

The literature source files are not present in this local read-only checkout.
WANTED: `literature/stacks-project/more-morphisms.tex`, Tags 069C and 0B6G,
and `literature/stacks-project/cohomology.tex`, Tags 08CG and 09U9,
for `lem-pc-perfect-relative-tensor-locally-bounded`.
Checked the authoritative online [069C](https://stacks.math.columbia.edu/tag/069C),
[0B6G](https://stacks.math.columbia.edu/tag/0B6G), and
[09U9](https://stacks.math.columbia.edu/tag/09U9) text. The expanded local proof is
marked agent-written because the local literature files are absent. LeanSearch
returned Internal Server Error; LeanFinder, Loogle and source searches were completed.

## New nodes

`lem-pc-perfect-relative-tensor-locally-bounded`, in
`dag/nodes/sec-picard-framework/lem-pc-perfect-relative-tensor-locally-bounded.json`,
states the local relative tensor-homology bound for a prescribed representative and
K-flat resolution without a quasi-compactness hypothesis. Its declaration is
`AlgebraicGeometry.Scheme.perfect_relativeTensor_locally_bounded` in
`lean/Sheaf/AlgebraicGeometry/PerfectRelativeTensorLocallyBounded.lean`.
The proof uses pseudo-coherence to upgrade stalkwise Tor finiteness, the bounded
strictly-perfect model's filtration, and K-flat model independence/stalk exactness.
No change record is necessary: no existing interface changed.

## Earlier second reading (a previous round; superseded)

1. Compared the item module and existing node with the repository using diff.
   The existing theorem signature and visibility are byte-for-byte unchanged;
   the only Lean changes there are the proof and two plain proof imports.
   No definition, target, public import, or other existing declaration changed.
2. Compiled both delivered modules locally in import order with lcompile.py.
   The item contains no sorry; the new local theorem is the sole added hole,
   with its whole proof exactly `by sorry`. No prohibited declarations or hollow
   definitions occur. The explicit axiom check and delivery probe permit only
   propext, Classical.choice, Quot.sound and sorryAx from the documented holes.
   The resolution witness is eliminated inside a theorem proof, not used to
   define an arbitrary object from an unproved existence statement.
3. Read the new signature against the actual perfectness, stalkwise Tor and
   K-flat definitions, and checked Stacks 069C, 0B6G and 09U9 online.
   The interval precedes the arbitrary test sheaf; scalar restriction and the
   prescribed representative are correctly retained. Empty X is vacuous, a zero
   model admits [0,0], and a shifted finite free model has the shifted local
   interval. The statement is the local part of the original argument without
   compactness, rather than a renamed global conclusion. Independent LeanFinder,
   Loogle and grep searches, together with reading the absolute Tor-amplitude
   APIs, found no usable direct replacement. This substantial geometric hole
   cannot be closed in a few minutes with the available declarations.
4. Read the global proof top downward: essential surjectivity, K-flat resolution,
   local bounds, finite subcover, explicit endpoint induction, stalk detection,
   and faithfulness. The empty finite cover is handled by [0,0]. Existing public
   imports supply the signature; both added plain imports supply proof premises.
   The new module imports statement vocabulary only. The report now explicitly
   lists the two old dependencies delegated to the local theorem. No module is
   pruned. The unit sk-thm-picard-duality has empty realization fields, unchanged;
   its route and this node's local-to-global route are preserved.
5. Checked both node records, their declarations and signatures, proof-dependency
   unions, sources, creation fields and proof origins. The upper node follows
   the actual finite-subcover proof. The new node describes the remaining local
   argument and now explicitly includes the K-flat stalk criterion needed to
   use the one-point tensor comparison at stalks.

Second reading changed the new theorem's natural-language proof and node plan to
make K-flatness of stalks and the common-resolution comparison explicit, and
clarified the old dependency IDs under No longer needed. The compiled global
proof and all theorem signatures were retained. One original hole is closed and
one local hole is added: a decomposition, with net zero holes closed.

Delivery verification: local compilation and the delivery axiom probes passed.
The required dry run was retried three times after repairing the long docstring
line; each failed at the tool's `git fetch -q origin` because the project server's
SSH connection timed out, reset, or closed. No preflight OK or push was obtained.
The reviewed work is preserved in this sandbox for the next delivery attempt.

## Second reading by A4

Independent second reading on 2026-10-13, after the recovery verification above.

1. Compared the original module and original node against the read-only repository
   with diff. The existing theorem signature, docstring and visibility are unchanged
   byte for byte. Only its proof and two plain proof imports changed. No existing
   definition, public import or target statement changed; no change record is needed.
2. Compiled both modules in import order with the prescribed lcompile.py --all.
   Both compile without errors or style warnings. Compiled the scratch axiom check:
   both declarations use only propext, Classical.choice, Quot.sound and sorryAx.
   The sole delivered sorry is the named local theorem, with its proof exactly
   by sorry and a matching node and proof docstring. No axiom, unsafe, opaque,
   implemented_by, extern or hollow definition occurs. K and P are witnesses
   eliminated inside a theorem proof; this delivery defines no chosen data.
3. Read the new statement alongside IsPerfect, HasStalkwiseFiniteTorDimension,
   IsKFlat and HasFiniteTorDimensionOver. Checked the authoritative online text
   of Stacks Tags 069C, 0B6G and 09U9. Pseudo-coherence from the finite-type and
   Noetherian hypotheses supplies the neighbourhood bound; the bounded perfect
   model gives [r-d,s]. The bound precedes every test module and works for the
   prescribed K-flat resolution. Empty X is vacuous, zero models allow [0,0],
   and a finite free term in degree j gives [j-d,j]. The local theorem omits
   compactness and global witness selection, which the delivered upper proof
   genuinely supplies; it is a strictly local part, not a renamed conclusion.
   Repeated source searches with relativeTensor, locally_bounded, TorAmplitude
   and the actual predicates in both library roots and the upstream checkout,
   and an independent LeanFinder query about neighbourhood finite Tor amplitude,
   found no direct replacement. Loogle did not know the project-local IsPerfect
   identifier; that result is not evidence of absence. The absolute Tor APIs
   tensor over O_X and cannot directly supply the relative geometric step.
   This remaining geometric theorem cannot be closed in a few minutes from
   the available interfaces.
4. Read the upper proof from its conclusion through representative selection,
   K-flat resolution, local bounds, finite subcover, endpoint induction and
   faithful stalk detection. Outside [c,d] the inequalities put the degree
   outside every selected [a_x,b_x]. The empty induction supplies [0,0].
   The two added plain imports are used only by the proof; the new module's
   public imports supply its statement vocabulary. The old direct dependencies
   def-pc-perfect-complex and def-pc-perfect-morphism are explicitly reported
   under No longer needed as delegated, not globally pruned. The unit
   sk-thm-picard-duality has empty realized fields; its route is unchanged.
5. Checked the two node signatures verbatim against Lean, their source places,
   creation and blueprint records, and equality of proof_deps with the union
   of step uses. The existing node changes only proof, proof_deps and
   proof_origin. Its plan now follows the actual global proof. The new node
   records the local geometric argument and explicitly cites the stalk
   K-flatness criterion, tensor comparison and stalk exactness used in its
   final step. No new dependency cycle or duplicate theorem was found.

This reading retained the Lean proofs and nodes and added this independent review.
One original hole is closed, one local hole is added: decomposition, net zero
holes closed. No imports or modules are claimed pruned.
