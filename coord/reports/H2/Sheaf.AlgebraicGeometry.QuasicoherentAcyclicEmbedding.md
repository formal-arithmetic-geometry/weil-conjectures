## What changed

Completed the earlier sandbox reduction in
`Sheaf.AlgebraicGeometry.QuasicoherentAcyclicEmbedding`. The existing theorem's signature,
visibility and docstring are unchanged. It obtains geometric embedding data from the new
`Sheaf.AlgebraicGeometry.AffineCoverModuleEmbedding`, proves pushforward quasi-coherence,
and proves positive-degree acyclicity using existing affine-scheme vanishing, the
module/source cohomology comparison, and the affine-morphism edge isomorphism. The combination
is real Lean: subsingletonness transfers through two injective maps and yields an IsZero
module object. No object is defined by choosing from an unproved existence theorem.

The geometric helper is a strictly smaller part of the original argument: it asserts an
embedding into an affine pushforward but no vanishing. Its docstring supplies the finite
cover, pullback, adjunction unit and stalk argument, including the empty scheme. Its new
node and the upper node's proof dependencies now match the Lean proof. The source was checked
against https://stacks.math.columbia.edu/tag/0BDY; the literature sources are not populated
in this read-only clone. LeanFinder and Loogle searches found no combined embedding theorem;
LeanSearch returned Internal Server Error. Local searches found geometric ingredients but
no existing statement of this entire geometric subclaim.

Both delivered modules compile together with lcompile.py. Removing the direct-image proof
import was tested and failed with an unknown pushforward quasi-coherence theorem, so that
import is retained. No definitions, existing statements, public imports or other existing modules
were changed. The second reader removed the redundant direct Čech proof import; its
affine-vanishing declaration remains available through the retained imports.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.exists_quasicoherent_acyclic_embedding`
(node `lem-sc-picard-qcoh-universal-delta-embedding`). The item's module has no remaining
`sorry`.

Added one hole:
`AlgebraicGeometry.Scheme.exists_affine_cover_module_embedding`
(node `lem-sc-picard-affine-cover-module-embedding`), in its own new module. This covers only
the geometric steps 1–3. The positive cohomology argument is complete from existing
library declarations. This delivery is a decomposition: one upper hole closed and one
lower hole added, net zero before any import-closure pruning. It is not an unconditional
axiom-free proof of the original theorem.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing`
and its upper-node dependency `pqf-lem-affine-vanishing`. We apply
`lem-pc-affine-vanishing` directly on the affine scheme U; an affine-open restriction
comparison is unnecessary in this argument. This does not claim that the affine-open
module is unreachable from other targets.

`lem-sc-picard-affine-diagonal-intersections` and
`lem-weil-pbc-affine-morphism-permanence` move from the upper node's direct dependencies
to the geometric helper's dependencies. They are still needed, not pruned. The affine
edge comparison and affine pushforward quasi-coherence remain needed. No other planned
nodes or modules are declared unnecessary, and the unit route is preserved.

The second reader also removed the redundant direct proof import
`WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech`, after compilation without it.
Its affine-vanishing declaration remains used and available transitively; this removes
no further dependency node and claims no additional unreachable module.

## Where the brief, the DAG or earlier work was wrong

The earlier report described two obsolete helpers that are not in the current sandbox,
and claimed removal of imports still used by the proof. Replaced that report and supplied
the missing node for the actual helper. No mathematical error in the DAG or brief was
found. The field assumption is retained; the geometric construction does not use it.
The original node's finite-cover and stalk arguments marked elementary hide substantial
Lean glue, now isolated as one geometric item. All cohomological inputs already exist.

## New nodes

`lem-sc-picard-affine-cover-module-embedding` states the geometric portion of Stacks
Tag 0BDY: an affine U, affine j, quasi-coherent G and monomorphism F → j_*G. It has the
same field, compactness and relative affine-diagonal hypotheses as the parent, and
contains no cohomological conclusion. Its complete construction in words handles zero
modules, affine X and empty X, and it lives in
`lean/Sheaf/AlgebraicGeometry/AffineCoverModuleEmbedding.lean`. No change records are needed.

## Second reading by H2

1. Compared both delivered Lean modules with the read-only repository. The geometric
   helper is new; the existing module differs only in private proof imports and its
   theorem body. The existing theorem signature, visibility, docstring and all public
   imports are byte for byte unchanged. No definitions or change records are present.
   Verdict: pass; no interface or target statement changes.
2. Compiled both modules in import order with lcompile.py. Inspected the only sorry:
   exists_affine_cover_module_embedding, a named theorem with its source, full proof
   docstring and matching node. There are no forbidden declarations or hollow
   definitions. A scratch import file printed axioms for both public theorems: exactly
   propext, Classical.choice, Quot.sound and sorryAx. The upper proof transports
   subsingletonness from affine cohomology through the additive comparison and the
   injective affine edge map, then applies ModuleCat.isZero_of_subsingleton. The
   existential witnesses are eliminated inside a theorem proof; no data definition
   chooses an arbitrary witness from an unproved existence theorem. Verdict: pass as
   a decomposition, not an unconditional proof.
3. Read Stacks Tag 0BDY part (1) independently. The geometric helper isolates its finite
   affine-cover construction and stalk-injective adjunction unit, with no vanishing
   conclusion. It is true and strictly a part of the parent argument. Checked empty X
   (empty cover, Spec of the zero ring, vacuous stalk condition), F=0 (zero pullback),
   and affine X (identity cover). The relative affine diagonal hypothesis supplies
   affine intersections over the affine base Spec k. New LeanFinder query on injectivity
   of the adjunction unit for a surjective open cover, Loogle query
   "SheafOfModules, CategoryTheory.Mono", and grep query on affine embeddings and
   pullbackPushforward mono found no complete existing helper. Local source search
   found isAffineHom_sigmaDesc and finite affine coproducts, but no combined module
   embedding theorem. The remaining geometric glue is not a few-minute closure.
   Verdict: pass; no duplicate or disguised restatement.
4. Read the proof from the upper theorem downward and checked all applied declarations.
   It uses existing affine-scheme vanishing, module/source comparison, affine edge
   comparison and pushforward quasi-coherence. Removed the redundant direct import
   WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech after a successful scratch
   compilation without it. The old dependency pqf-lem-affine-vanishing is bypassed;
   affine intersections and permanence are retained under the helper. No other old
   dependency is discarded. The unit sk-prop-av-cube and its route are unchanged:
   this is a reduction inside the existing Kunneth/acyclic-embedding tool argument.
   The unit's realized arrays were already empty in the repository; this delivery
   neither bypasses its step nor changes those records. Verdict: pass.
5. Compared the old and new parent nodes: only proof, proof_deps and proof_origin
   changed. Checked the new helper node's required fields, verbatim Lean statement,
   source, searches, chapter/unit and provenance. In each node proof_deps is exactly
   the union of the steps' uses. The parent names every substantive declaration
   invoked by its Lean proof; the helper describes the sourced geometric argument.
   Verdict: pass.

Second-reading changes: removed one redundant private Čech import, expanded the
No longer needed report accordingly, and recorded independent review and axiom checks.
One existing hole is closed and one strictly simpler geometric hole is added: net zero.
