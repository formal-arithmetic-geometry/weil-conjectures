## What changed

Replaced the original all-degree existence hole by dependent recursion on finite
replacement stages and a proved assembly of the resulting tower. The original
`exists_finite_split_replacement` signature and docstring are unchanged. Its new
imports are proof-only imports of the initial-stage, successor-stage, and
assembly modules.

`FiniteSplitReplacementStage` constructs restriction of the existing truncated
finite split data, proves its identity and transitivity laws, and packages a
finite stage with its refinement map. It also spells out the next boundary's
universal property among **all** schemes over the base.

Proved the initial stage directly from Mathlib: the degree-zero matching property
makes K_0 cover X, compactness selects finitely many affine opens, and their
coproduct gives the degree-zero splitting and refinement.

Proved the geometric successor step directly from Mathlib. Finite cofans of qcqs
schemes remain qcqs, including the stage's splitting cofans. The intersection
argument for quasi-separatedness uses the clopen components of a disjoint union.
Finite limits in the over category of etale, quasi-compact, quasi-separated
morphisms then give the universal next matching scheme. Pulling back K's
matching cover and selecting finitely many affine opens gives the new finite
nondegenerate object and its compatible maps to the boundary and to K.

Constructed the new simplicial term explicitly as a binary and indexed
coproduct. Proved every operator identity using old splitting cofans and ordinal
image factorizations. Constructed its refinement natural transformation and
proved exact restriction of both functor and refinement. These proofs adapt the
operator algebra in `SiteHypercoverAttachmentOperators` and
`SiteHypercoverAttachmentComposition` to actual scheme coproducts.

The remaining theorem equips this explicit attached functor with finite
splitting and matching data. The attachment theorem itself is now proved by
combining that data with the constructed refinement and its restriction law.
The successor module combines the proved geometry with that attachment theorem.
The assembly theorem constructs the full functor, its refinement natural transformation, splitting cofans, finiteness,
and matching witnesses from compatible finite stages. Its underlying functor
construction reuses the proved private tower helpers from
`Sheaf.CategoryTheory.SiteFiniteBasisHypercoverExistence` via a proof-only
`import all`; the finite boundary
index construction adapts the corresponding construction in
`Sheaf.CategoryTheory.SiteFiniteBasisHypercoverStep`.

## Proved and sorry left

Original hole closed:

- `AlgebraicGeometry.FiniteSplitEtaleHypercover.exists_finite_split_replacement`.

New theorems proved without additional holes:

- `AlgebraicGeometry.TruncatedFiniteSplitEtaleHypercover.restrict_self` and
  `restrict_restrict`.
- `AlgebraicGeometry.FiniteSplitReplacementStage.restrict_self` and
  `restrict_restrict`.
- `AlgebraicGeometry.FiniteSplitEtaleHypercover.exists_replacement_stage_zero`.
- `AlgebraicGeometry.exists_replacement_boundary`.
- `AlgebraicGeometry.exists_finite_relative_boundary_cover`.
- `AlgebraicGeometry.SchemeSplitAttachment.attachedSimplicial_restrict`,
  `attachedRefinement_restrict`, and all operator and refinement naturality
  lemmas in `FiniteSplitReplacementAttachmentConstruction`.
- `AlgebraicGeometry.exists_replacement_stage_of_boundary_cover`.
- `AlgebraicGeometry.FiniteSplitEtaleHypercover.exists_replacement_stage_extension`,
  from the proved geometry and the attachment theorem above.
- `AlgebraicGeometry.FiniteSplitEtaleHypercover.exists_replacement_of_stage_tower`.

One new hole remains:

- `AlgebraicGeometry.SchemeSplitAttachment.exists_attached_split_structure`, in
  `lean/Sheaf/Paper/FiniteSplitReplacementAttachmentStructure.lean`, node
  `lem-weil-pbc-finite-split-replacement-attachment-structure`.
  It must give the already constructed attached functor its nondegenerate
  objects, splitting cofans, and matching witnesses. The top nondegenerate
  object is V, and its matching object is Q.M. The cofan is the canonical
  coproduct cofan after separating the unique identity epi label from proper
  epi labels. The new matching map is uniquely determined by Q.universal;
  uniqueness identifies its restriction to V with b, giving surjectivity.
  Old fields must be retained with an exact restriction equality. Its complete
  proof in words is in the theorem docstring and node. The functor laws,
  refinement map and all naturality equations are already proved. This theorem
  has no target K or refinement morphism and is strictly a data-construction
  part of the attachment.

This is a decomposition: one original hole closed, one new hole added, net zero
holes. It is not a completed proof of the original theorem without sorry axioms.
No definition contains sorry, and no arbitrary object is defined by choosing a
witness from an unproved existence theorem.

## No longer needed

Second reading removed redundant proof imports already exposed by the remaining
public import closure: Mathlib.AlgebraicGeometry.Limits and
Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated from geometry, and
Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated from relative cover and
stage zero. The affected modules compile without these four import lines.

All six old direct proof dependencies of the item have been accounted for:

- `def-weil-pbc-etale-site` is supplied by the unchanged public interfaces;
  the new proof has no separate use of this node.
- `def-weil-pbc-finite-split-hypercover` remains a statement dependency and is
  used by the stage, splitting, and assembly constructions.
- `lem-weil-pbc-etale-covering-base-change`,
  `lem-weil-pbc-etale-covering-affine-refinement`, and
  `lem-weil-pbc-qcqs-morphism-permanence` remain in the geometric children.
  These are Mathlib leaves, not additional Sheaf modules: the proofs use their
  recorded Mathlib ingredients directly (pullback stability, finite affine-open
  selection, and qcqs permanence).
- `lem-weil-pbc-qcqs-finite-affine-open-cover` is unused. Compactness selects
  finitely many affine opens in the source of the relative etale cover directly;
  no preliminary affine covering of its matching target is needed.

The item's direct proof dependencies are replaced by stage zero, successor,
stage restriction data, and assembly, exactly as its proof now uses them.
Both original public imports of the item are retained. Every added import of the
item is proof-only. The stage interface does not import EtaleHypercover; only
modules whose statement or proof uses that predicate import it. No existing
Lean module is withdrawn or established to leave the target import closure;
modules pruned: none.

## Where the brief, the DAG or earlier work was wrong

The original geometric proof plan is correct, but its stated dependencies do not
provide the finite simplicial extension or the strict assembly of compatible
stages. This delivery makes those steps explicit and proves the assembly,
restriction, initial stage, and geometric matching-cover construction.

The existing proved formal-family attachment theorem
`CategoryTheory.FormalSplitAttachment.exists_split_truncated_extension` does not
apply directly to arbitrary coproducts of etale schemes: a scheme map into a
coproduct need not factor globally through one component. The scheme attachment uses the splitting cofan's universal property instead
of an index-level choice of a target component; its operator and refinement
proofs are included. Only its finite split and matching data remain open.

Edge cases checked in the Lean constructions include an empty base and empty
finite cover, degree zero with an empty matching diagram, and arbitrary lower
ordinal maps (not merely injective faces). No compactness of K's terms is used.
No existing target, declaration signature, or definition was changed. The
blueprint unit route is preserved. The source passages read were Stacks
Hypercoverings 0DAV, 01GJ, and 094K; the fetched source copy is in the sandbox's
scratchpad because the shared checkout is read-only.



## New nodes

`def-weil-pbc-finite-split-replacement-stage`: finite replacement stages, strict
restriction, and universal boundary data, in `FiniteSplitReplacementStage`.

`lem-weil-pbc-finite-split-replacement-stage-zero`: the proved initial finite
affine replacement, in `FiniteSplitReplacementStageZero`.

`lem-weil-pbc-finite-split-replacement-stage-assembly`: the proved passage from
compatible stages to a full split hypercover and refinement, in
`FiniteSplitReplacementStageAssembly`.

`lem-weil-pbc-finite-split-replacement-boundary-matching`: the proved qcqs universal
matching scheme, in `FiniteSplitReplacementGeometry`.

`lem-weil-pbc-finite-split-replacement-relative-cover`: the proved finite affine
cover of the relative matching target, in `FiniteSplitReplacementRelativeCover`.

`def-weil-pbc-finite-split-replacement-attachment-construction`: the explicit
simplicial attachment, operator proofs, refinement and restriction proofs, in
`FiniteSplitReplacementAttachmentConstruction`.

`lem-weil-pbc-finite-split-replacement-attachment-structure`: the one remaining
finite splitting and matching construction on that explicit functor, in
`FiniteSplitReplacementAttachmentStructure`.

`lem-weil-pbc-finite-split-replacement-boundary-attachment`: the proved attachment
of a relative boundary cover, in `FiniteSplitReplacementBoundaryAttachment`.

`lem-weil-pbc-finite-split-replacement-stage-extension`: the finite successor step,
proved from the matching, relative-cover, and attachment nodes, in
`FiniteSplitReplacementStageExtension`.

No change record is needed: all supporting interfaces are new modules, and the
item's existing interface is unchanged.

## Earlier second reading (a previous round; superseded)

1. Compared every delivered module with the shared repository. Only the item's
   module existed there. Its existing theorem signature and docstring are byte
   for byte unchanged; its only changes are three plain proof imports and the
   proof body. All nine supporting modules are new. No existing definition,
   target statement, visibility, or module held by another group is changed.
   Verdict: pass; no change record is required.

2. Compiled all ten modules together through lcompile.py in import order,
   without errors or warnings. Searched the complete delivered Lean sources:
   the only sorry is the named public theorem
   AlgebraicGeometry.SchemeSplitAttachment.exists_attached_split_structure;
   no forbidden axiom, unsafe, opaque, implemented_by, extern, or kernel
   bypass occurs. Read every concrete definition: restrictions, coproduct
   attachment and tower functor are real constructions. The remaining theorem
   is eliminated inside proofs only; no public definition chooses arbitrary
   data from it. Scratch-copy #print axioms checks show only propext, Classical.choice and
   Quot.sound for stage zero and assembly, and additionally sorryAx for the
   successor and original theorem, as expected from the reported remaining
   attachment-structure hole. The delivery probe checks every declaration.
   Verdict: pass as a decomposition, not an axiom-free completed target proof.

3. Read the sole split-off theorem, its full proof docstring and matching node,
   and the actual attachment operators. It is strictly the finite splitting
   and matching-data part of one successor step: no target K, refinement map,
   global tower, initial cover, or compactness choice remains in it. In degree
   zero the next cofan is V plus the identity degeneracy of U_0, and its
   matching scheme has the two vertex projections. Empty schemes and empty
   finite presentations cause no nonemptiness assumption. In all degrees
   epi endomorphisms of an ordinal are identities, and lower epi labels cannot
   target the new top degree. Coproduct universality and Q.universal give the
   stated data, retaining all old fields; surjectivity follows on the V summand.
   This is true and exactly sufficient for the boundary attachment theorem.
   Searched again with leanfinder for adjoining one degree while retaining the
   old truncation, loogle for CategoryTheory.SimplicialObject.Splitting, and
   grep, plus direct rg searches in both library roots. The Mathlib hits give
   splitting structures, reindexing and skeletal Kan extensions, not this
   finite split scheme attachment. Read the existing formal-family extension:
   it requires FormalCoproduct morphisms with global component choices, so it
   does not replace the scheme-coproduct construction here. Closing the
   remaining dependent structure construction is substantial, not a short
   lemma application. Verdict: pass with the one explicitly reported hole.

4. Read the proof downward from the item through stage zero, geometry, relative
   cover, attachment and assembly; compared with Stacks 0DAV, 01GJ and 094K in
   the fetched source. The finite geometric steps use Mathlib directly.
   All new public imports supply types or concrete definitions; imports used
   only by proofs are plain. Checked the unit record sk-prop-h2: the item is
   not one of its realized statement or step nodes (those lists are empty),
   and this delivery changes neither its statement nor route. Expanded the
   pruning report to account explicitly for all six old direct proof deps and
   distinguish a removed DAG dependency from actual module pruning.
   Verdict: pass; no shorter applicable all-degree or scheme attachment result
   was found, and no module pruning is claimed.

5. Read all ten delivered JSON nodes. Their IDs, Lean module/declaration and
   verbatim signatures, sources, creation records, unit/chapter, blueprint
   provenance, search records and proof steps agree with the code. Each
   proof_deps list is exactly the union of the proof steps' uses. The old
   geometric nodes retained by the children are verified Mathlib leaves;
   their ingredients are used directly, without missing Sheaf imports.
   The existing item's proof follows stage zero, dependent recursion over
   successor stages, then assembly. Verdict: pass.

Second-reading changes: clarified and completed No longer needed; recorded the
independent searches and this review. Removed four redundant proof-import lines
from three new modules; the affected files recompile. No Lean signature,
definition, or proof body required repair. One original hole closed and one
strictly smaller hole added, net zero holes, with no modules pruned.

Superseded repair note (incorrect; repaired in the current reading):
`FiniteSplitReplacementStageAssembly` had four private theorem helpers whose
statements duplicated private helper theorems in `Sheaf.CategoryTheory.SiteFiniteBasisHypercoverExistence`.
The earlier reader incorrectly assumed those private helpers could not be imported, and kept equivalent
local proof terms; each helper is now a private proposition-valued `def` (with the `defProp` linter disabled),
so the import-prune duplicate-statement check does not reject the delivery. Their bodies and all public
statements are unchanged.


## Second reading by M4

1. Interface comparison: diffed every delivered module against the shared
   repository. The item is the only existing module. Its theorem signature,
   docstring, public imports, and visibility are byte for byte unchanged; only
   three plain proof imports and the proof body differ. All nine supporting
   modules are new, and no change record or forced adaptation is needed.
   Verdict: pass.

2. Proof and data audit: compiled all ten delivered files in dependency order
   through lcompile.py. The only hole is the named public theorem
   `AlgebraicGeometry.SchemeSplitAttachment.exists_attached_split_structure`.
   No forbidden declarations or kernel bypasses occur. Restrictions, attached
   coproducts and operators are concrete definitions. All elimination of the
   remaining existence hole takes place inside proofs of existence, never to
   define an arbitrary public object. The tower construction now uses the
   existing library proofs rather than seven local copies. Scratch #print axioms
   checks and the delivery's exhaustive declaration probe validate the final
   sources. Verdict: pass as a decomposition; the original theorem still depends
   on the explicitly reported attachment hole.

3. Remaining statement: read its exact Lean signature, docstring, node and
   attachment formulas. Its hypotheses supply U, V, Q, b, surjectivity, and a
   finite qcqs presentation; it asks only for splitting and matching data on the
   already constructed functor, with exact old restriction. It has no K or
   refinement map and is strictly smaller than the item. For n=0 the new term
   is V plus the identity degeneracy of U_0; the matching diagram has the two
   vertices. Empty X and empty finite presentations require no inhabitance.
   An epi ordinal endomorphism is the identity, and lower-degree epi labels
   cannot reach the new top degree. Coproduct universality gives splitting;
   Q.universal determines the matching map uniquely, whose composite with
   coprod.inl equals b, proving surjectivity. Old data can be retained exactly.
   Repeated leanfinder, qualified loogle, and grep searches with new wording,
   plus rg in the Sheaf library, found no ready-made scheme attachment theorem.
   The formal-family extension requires global component choices for maps;
   arbitrary scheme coproduct maps do not provide them. The scratch work still
   needs the full dependent matching-data and restriction assembly, not a short
   lemma application. Verdict: true, needed, strictly smaller; keep this hole.

4. Route and pruning: read the item downward through zero, successor geometry,
   relative cover, explicit attachment and tower assembly. Compared with Stacks
   hypercovering.tex, lemma-hypercovering-object (0DAV), lemma-covering (01GJ),
   and lemma-w-contractible (094K). The finite affine selection and qcqs limit
   steps use Mathlib directly, without compactness of K's terms. All imports
   required only by proofs are plain, including the new import all for generic
   tower helpers. The shared sk-prop-h2 realized lists are empty and unchanged;
   no unit statement or step is bypassed. No longer needed accounts for all six
   old proof dependencies. The added generic-tower import closure contains no
   further sorry. One old hole is replaced by one smaller hole: net zero; no
   module is claimed pruned. Verdict: pass.

5. DAG comparison: inspected all ten node records, including each source,
   statement, proof step, proof_deps union, provenance, searches, chapter/unit,
   creation record, and verbatim Lean signature. The original node changes only
   its proof route and allowed Lean metadata. Updated the assembly provenance
   to record actual reuse of the existing generic tower helpers. Updated the
   remaining node's proof wording and independent searches. Verdict: pass.

Changes in this reading: removed seven copied private generic tower declarations
from FiniteSplitReplacementStageAssembly, including four proposition-valued defs
and their disabled defProp lint checks. A proof-only import all exposes the
existing private helpers in SiteFiniteBasisHypercoverExistence, so their copies
are unnecessary. This supersedes the earlier repair note: recasting duplicate
proofs as defs was not an acceptable repair. Clarified the remaining theorem's
proof docstring and node to use uniqueness of colimit witnesses as well as proof
irrelevance for proposition-valued fields. Updated the assembly node and report.
No existing Lean signature, target statement or definition changed. Holes closed:
exists_finite_split_replacement (one); holes added: exists_attached_split_structure
(one); decomposition, net zero; modules pruned: none.
