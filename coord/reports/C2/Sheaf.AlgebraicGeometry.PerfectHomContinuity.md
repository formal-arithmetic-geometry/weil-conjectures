## What changed

Replaced the sorry in `AlgebraicGeometry.perfect_hom_continuity` with a complete
Lean proof by `quasiCompactOpen_induction`. The theorem's signature, universes,
instances, visibility and original public imports are unchanged.

Added the real proposition `AlgebraicGeometry.PerfectHomContinuityOn`, quantified
over all perfect pairs on every open-immersion presentation of an open. This
includes adjacent shifts needed by Mayer--Vietoris, and allows the final top-open
specialization to use the identity morphism of X with no chosen comparison data.
Added two independently actionable intermediate theorems: the affine-open base
case and the affine-open adjoining step. Each has its own module, node, source,
and complete proof in words. Neither is the original statement renamed: one
requires an affine open, and the other assumes continuity on the two smaller
opens and their intersection. The original theorem combines them by actual
quasi-compact-open induction and specialization.

The original node now records exactly this reduction. The unit record
`sk-thm-picard-semicon` has empty realized statement/step lists, so no mandated
realized unit step is bypassed. No definition or existing theorem signature was
changed; no forced adaptations are needed.

## Proved and sorry left

Closed the item's sole hole: `AlgebraicGeometry.perfect_hom_continuity`
(node `lem-pc-perfect-hom-continuity`). This is a decomposition, not a finished
sorry-free mathematical proof: two lower holes were added.

Remaining new holes, both exactly `:= by sorry` in separate public theorems:

- `AlgebraicGeometry.perfect_hom_continuity_affine`
  (node `lem-pc-perfect-hom-continuity-affine`, module
  `Sheaf.AlgebraicGeometry.PerfectHomContinuityAffine`). Remaining work:
  identify canonical sheaf-derived Hom transport with the module-derived Hom
  diagram, then apply the existing `CochainComplex.affine_perfect_hom_colimit`.
- `AlgebraicGeometry.perfect_hom_continuity_union`
  (node `lem-pc-perfect-hom-continuity-union`, module
  `Sheaf.AlgebraicGeometry.PerfectHomContinuityUnion`). Remaining work:
  construct the compatible Mayer--Vietoris Hom comparison sequences and apply
  filtered-colimit exactness and the five lemma.

`AlgebraicGeometry.PerfectHomContinuityOn` is a direct proposition definition,
with no sorry and no data chosen from an existence theorem. The item's module
contains no remaining sorry. No existing lower holes were changed.

Edge cases checked mathematically: an empty open is affine and its derived Hom
groups are zero; a zero perfect object gives zero Hom groups; constant diagrams
have the expected comparison; a merely preordered index is enough, and the
specified index i supplies nonemptiness. The universal predicate quantifies
only over structure morphisms equal to the given composite, preventing an
unrelated morphism from satisfying the range condition. For the union step,
quasi-separatedness gives compactness of the intersection. Quantification over
all perfect pairs supplies both positive and negative shifts.

## No longer needed

Removed from the item's direct proof imports:

- `Sheaf.AlgebraicGeometry.AffinePerfectHomColimit`
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`
- `Sheaf.AlgebraicGeometry.DerivedAdjoint`
- `Sheaf.AlgebraicGeometry.DerivedMayerVietorisTriangle`
- `Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective`
- `Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four`

These imports and their original nodes are still needed by the two intermediate
proof plans, and are imported there. This is relocation, not global pruning.
No original dependency module or node is claimed pruned from the target closure.
The original node now directly needs only the predicate node, the two new lemma
nodes and `lem-sc-invert-s-cohomology-induction`; all former geometric comparison
dependencies move into the new nodes. Original public imports are retained for
signature and visibility compatibility. The open induction import is used.

## Where the brief, the DAG or earlier work was wrong

The original affine step's object equivalences do not themselves state the
compatibility with the counit-pinned `perfectStageMap` and `perfectLimitMap`.
The gluing step also needs compatibility of boundary arrows with pullback,
not just existence of a Mayer--Vietoris triangle. These bridges remain explicit
work in the two new lemmas; their docstrings and node steps name the missing
identifications rather than treating them as proved.

The local literature checkout has no `literature/stacks-project/perfect.tex`.
WANTED: that file, Tag 09RE (lemma-descend-homomorphisms), for the new affine and
union nodes. The source was read online at
https://stacks.math.columbia.edu/tag/09RE; the Lean reduction and expanded proof
plans are marked agent-written. LeanSearch returned Internal Server Error;
this is recorded as unavailable, not as a failed mathematical match. LeanFinder,
Loogle, Mathlib grep, repository searches and blueprint searches found no existing
statement providing the needed canonical continuity comparisons. The ancestor
helper returned None for this created item; the new nodes follow its existing
blueprint.from chain to `lem-pc-rf-perfect-base-change`.

## New nodes

`def-pc-perfect-hom-continuity-on`: the open predicate, in
`Sheaf.AlgebraicGeometry.PerfectHomContinuityOn`; a real definition with no hole.

`lem-pc-perfect-hom-continuity-affine`: affine-open base case, in
`Sheaf.AlgebraicGeometry.PerfectHomContinuityAffine`; one remaining public hole.
Its proof plan uses the existing finite-projective affine model, affine derived
equivalence, K-flat pullback dictionary, and affine Hom colimit theorem.

`lem-pc-perfect-hom-continuity-union`: affine-open adjoining step, in
`Sheaf.AlgebraicGeometry.PerfectHomContinuityUnion`; one remaining public hole.
Its hypotheses are precisely the three local conditions needed for the
Mayer--Vietoris/five-lemma argument in every shift.

There are no change records because no existing interface was changed.

## Second reading by C2

1. Interface: diffed every delivered module against the repository. Only
   PerfectHomContinuity already exists; its theorem signature is byte for byte
   identical, including both derived-category instance hypotheses and both tail
   clauses. The original public imports, universes and visibility are preserved.
   No existing definition is changed and no change record is required.
2. Proof: all four modules compiled locally in import order without warnings.
   The predicate is a real Prop-valued definition with no chosen data or sorry.
   Only perfect_hom_continuity_affine and perfect_hom_continuity_union contain
   sorry, each exactly a named public theorem with its source, word proof and node.
   Scratch #print axioms checks give only propext, Classical.choice and Quot.sound
   for PerfectHomContinuityOn, and those plus sorryAx for the three theorems.
   No forbidden declaration, implementation attribute or hidden definition hole
   occurs. The upper proof is an actual induction and identity specialization.
3. New statements: read Stacks Tag 09RE, lemma-descend-homomorphisms, online.
   Its affine calculation and Mayer--Vietoris induction justify the two local
   lemmas; requiring both objects perfect is its case (1). The affine lemma
   handles just an affine open, while the union lemma assumes continuity on U,
   V and their intersection. Neither restates the global theorem. Checked empty
   opens, zero objects, U contained in V, disjoint opens, and constant diagrams:
   empty Hom groups are zero groups (singleton Hom sets); the gluing exact
   sequence reduces accordingly. The specified i rules out an empty index type;
   a directed preorder suffices for tail cofinality. The predicate fixes both the
   open image and the composite structure morphism, and quantifies over all
   perfect pairs, including shifts. Local restrictions remain qcqs and locally
   of finite presentation because the opens used are quasi-compact.
   Repeated LeanFinder with "derived morphisms of perfect complexes commute
   with a filtered affine inverse limit of schemes", Loogle with
   "AlgebraicGeometry.IsAffineOpen, CategoryTheory.Limits.IsColimit", and Mathlib
   grep with Hom/continuity and Mayer--Vietoris/Hom synonyms. Finder returned
   ordinary scheme/section descent, Loogle no matches, and grep unrelated
   continuity results. Repository searches also found no duplicate local theorem.
   Read affine_perfect_hom_colimit, perfect_iff_affine_bounded_projective,
   exists_affineQCohDerivedEquivalence, the tilde pullback comparisons, canonical
   perfect Hom transport and Mayer--Vietoris declarations. No local hole can be
   closed merely by applying these: the scalar-extension Hom identifications
   and the compatible long exact sequence still need construction.
4. Route and pruning: quasiCompactOpen_induction is applied to the quantified
   predicate at the compact top open; compactness and quasi-separatedness follow
   from s to the affine base. The identity range proof and final specialization
   retain exactly the original Hom maps. Each retained public import supplies
   names in the signature; the new predicate needs finite-presentation names in
   its definition. New lemma proof imports supply their documented plans.
   sk-thm-picard-semicon has realized.statement = [] and realized.steps = [[]],
   so this reduction bypasses no realized unit step. The old affine, adjunction,
   Mayer--Vietoris and five-lemma dependencies are relocated to the lower lemmas;
   no module is claimed pruned from the target closure. One original hole is
   closed and two new holes are added: a decomposition, with no claim of net
   sorry-free progress.
5. Nodes: checked the predicate definition and all three theorem signatures
   against their Lean records, and checked proof_deps equals the union of uses
   for every delivered node. Existing-node changes are only proof, proof_deps
   and proof_origin. New nodes have source, creation, ancestor chain, searches,
   chapter, unit and Lean fields; the predicate has empty proof dependencies.
   The main node matches induction and identity specialization. The lower nodes
   document the remaining affine comparison and gluing arguments. The five
   lemma is the recorded Mathlib leaf isIso_of_epi_of_isIso_of_isIso_of_mono.

Changed in this reading: the union lemma's plan overlooked the existing
schemeDerived_mayerVietoris_directImage (and its natural boundary) in
DerivedMayerVietorisFunctorial. Added that proof-only import and its existing
node to the union proof dependencies, and explained in the new lemma's docstring
and node how the adjunction unit produces the Hom-sequence comparison. This
uses an existing bridge instead of rebuilding boundary naturality from scratch;
identification with the fixed canonical Hom transports remains explicit work.
No signature, definition body, Lean proof or hole count was changed. The extra
import makes existing functoriality holes reachable; they are not new holes
created by this delivery and no decrease in the total import-closure ledger is
claimed. The final delivery checks verify the repaired set and its axioms.
