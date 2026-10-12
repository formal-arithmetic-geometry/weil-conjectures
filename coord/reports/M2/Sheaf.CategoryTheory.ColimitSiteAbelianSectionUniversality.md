## What changed

Replaced the sole sorry in
`CategoryTheory.colimit_site_abelian_section_universality` with a complete Lean
proof from two strictly weaker, elementwise statements. Added proof-only imports
of `Mathlib.CategoryTheory.Filtered.Final`,
`Sheaf.CategoryTheory.ColimitSiteAbelianSectionRepresentatives`, and
`Sheaf.CategoryTheory.ColimitSiteAbelianSectionEventualEquality`.
All existing signatures, visibility, public imports and definitions are unchanged.

The first new theorem gives representatives under the unit-characterized alpha
maps; it does not mention theta, D, E, K, e, hD or hK. The second says that two
sections at a single stage with equal alpha images become equal under some theta
transition; it does not claim existence of representatives for arbitrary limit
sections and does not mention D, E, K, e, hD or hK. These are the surjectivity and
eventual-equality parts of the original presentation argument, not renamed
universal properties.

The main proof transfers these facts through E, e, hK and hD. Two proved private
helpers transfer element values or kernel equalities across an equality of arrows
with possibly different target objects. It then uses
`Types.FilteredColimit.isColimitOf'` on the underlying-set cocone and reflects the
colimit through `forget AddCommGrpCat`. The inverse maps of the supplied E and e
are used explicitly; no object is selected from an unproved existence theorem.
The parent node's proof, proof_deps and proof_origin now record this argument.

The source was read at https://stacks.math.columbia.edu/tag/0A35 and
https://stacks.math.columbia.edu/tag/03CO; the local literature checkout contains
lists but not the cited tex files. Both new docstrings and nodes include the
presentation, finite-cover sheaf, adjunction and finality argument that remains.
The unit record `sk-thm-p1` was read: this node is not one of its realized unit
statements or steps. This is a split below the unit level, keeping the original
section-formula route.

## Proved and sorry left

Closed the original hole:
`CategoryTheory.colimit_site_abelian_section_universality`
(node `lem-weil-pbc-colimit-site-abelian-section-universality`).
The item's module now has zero sorries. Both private helpers are proved.

Added exactly two holes, each in its own new public theorem module:

- `CategoryTheory.colimit_site_abelian_section_representatives`
  (node `lem-weil-pbc-colimit-site-abelian-section-representatives`).
- `CategoryTheory.colimit_site_abelian_section_eventual_equality`
  (node `lem-weil-pbc-colimit-site-abelian-section-eventual-equality`).

This is a decomposition, not a sorry-free proof of the section formula: one upper
hole closed, two lower holes added, net -1 before any pruning. The two new holes
are exactly `:= by sorry`; there are no holes inside definitions or partial
proofs. No target declaration or existing theorem statement was changed.

Validation: all three modules compile together with the required lcompile.py
wrapper, against the sandbox overlay. The delivery dry run also checks the
library declarations and their axioms. The original theorem still transitively
uses sorryAx through the two explicitly reported new lemmas.

Before stating the new lemmas, checked the empty-source-stage case (no U), empty
covers (zero section group), zero sheaves, identity/constant stage systems, and
parallel refinement arrows. The first two clauses do not exclude any of these
cases; eventual equality requires filteredness to equalize refinements. HEq in
the representative clause records the target transport from cocone naturality,
not a freely supplied target isomorphism. The eventual-equality clause compares
two images in one target group and requires no such transport.

## No longer needed

No imports were removed and no modules are claimed pruned from the targets'
closure. Every original public import still supplies statement types or instances
needed to elaborate the existing signature, including abelian sheafification.

The parent no longer directly uses the old presentation-theory proof dependencies:
`def-weil-pbc-arrows-functor`, `def-weil-pbc-finite-precoverage`,
`def-weil-pbc-sites-and-cohomology`,
`lem-weil-pbc-conjugate-iso-unit-equation`,
`lem-weil-pbc-filtered-colimit-sets-elementwise`,
`lem-weil-pbc-filtered-colimits-commute-finite-limits`, and
`lem-weil-pbc-initial-functor-cofiltered-criterion`.
These remain statement or proof dependencies of the two new nodes, so they are
relocated rather than globally pruned. `def-weil-pbc-category-colimit` stays a
parent proof dependency for the colimit criterion and reflection step.

The investigated modules `ColimitSiteSetEvaluationPresentation`,
`ColimitSiteSetSectionPresentation`, `SitePullbackAbelianUnderlying`,
`ColimitSiteUnitZeroDetection`, and `ColimitSiteSections` are not imported by this
proof. The first three require additional set-pullback finite-limit preservation
hypotheses or comparisons, and the zero-detection module requires stronger
precoverage and exactness assumptions. The sections module concerns an already
supplied colimit of sheaves, rather than this inverse-image section cocone. No
claim is made about their uses elsewhere in the library.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or marked disputed. The planned low-level
lemmas provide representative/finality and finite-limit tools, but do not already
state the abelian presentation sheaf or its adjunction comparison. Those steps
remain explicitly in the proof sketches of the two new elementwise statements.

Lean's `Types.FilteredColimit.isColimitOf'` supplies the final universal-property
assembly directly. Arrow equalities hK and hD may have propositionally equal,
not definitionally equal, targets: extracting an ordinary equality of their
hom fields without transporting endpoints would not typecheck. The private
helpers handle precisely this issue.

Searches were actually run with msearch.py and recorded in searches.jsonl.
LeanSearch was unavailable; LeanFinder returned generic sheaf and colimit tools,
and Mathlib source grep found sheafification/point constructions but no exact
colimit-site statement. Existing Lean modules and the blueprint were also
searched; no duplicate representative or eventual-equality statement was found.

## New nodes

`lem-weil-pbc-colimit-site-abelian-section-representatives`, in
`dag/nodes/sec-proper-base-change/`, corresponds to
`lean/Sheaf/CategoryTheory/ColimitSiteAbelianSectionRepresentatives.lean`.
It asserts only existence of stage representatives, with the limit endpoint
transport expressed by HEq, and has no supplied section diagram/cocone.

`lem-weil-pbc-colimit-site-abelian-section-eventual-equality`, in the same
chapter directory, corresponds to
`lean/Sheaf/CategoryTheory/ColimitSiteAbelianSectionEventualEquality.lean`.
It asserts only eventual equality of two existing same-stage representatives.
Both nodes inherit the chapter and unit, record the actual three kinds of search
(including LeanSearch unavailability), and carry their unchanged Lean signatures
verbatim, sources and complete natural-language proof steps.

There are no change records or forced adaptations.

## Second reading by M2

1. **Interfaces: PASS.** Independently diffed the delivered parent against the
   read-only repository. Its theorem signature is byte-for-byte identical, as are
   its original public imports and docstring. The changes are three plain proof
   imports, two private proved helpers and the replacement proof. The other two
   modules are new. No definition, target or existing public declaration changed;
   no change record or forced adaptation is needed.

2. **Proof and axioms: PASS, with the reported decomposition.** All three modules
   compile in dependency order through the required lcompile.py wrapper, with no
   compiler errors or warnings. Compiled independent scratch copies with explicit
   #print axioms for all three public theorems and both private helpers. Each
   public theorem has exactly propext, Classical.choice, Quot.sound and sorryAx;
   each private helper has only propext and Quot.sound. The parent contains no
   sorry. The only two delivered holes are the whole proofs of the new named
   theorems reported above. No forbidden declaration or hollow definition occurs.
   Checked the orientation of hK and hD, both arrow-target transports, cancellation
   of E and e, same-stage equality, filteredness of Under i, and reflection from
   the underlying-set cocone. The proof assembles both lower clauses rather than
   applying a renamed universal-property assertion.

3. **Split statements: PASS.** Read both complete signatures, docstrings and nodes
   independently against Stacks 0A35 and 03CO. Representatives assert only joint
   surjectivity; eventual equality asserts only the same-stage kernel criterion.
   Neither supplies D, E, K or e, and neither asserts IsColimit. The representative
   lemma does not even assume theta. HEq accounts for cocone endpoint equality;
   the eventual-equality conclusion compares images in one target. Checked zero
   sections, empty covering families, constant identity diagrams, vacuous empty
   source stages, and parallel refinements: these require no missing hypothesis.
   In particular empty covers use the empty finite limit, and parallel refinements
   require filtered equalization. The construction uses finite covering equalizers
   of abelian stage sheaves, not an assumed finite-limit-preserving set pullback.
   Independent searches used the different terms "direct limit site", "joint
   surjectivity" and "kernel vanishing", plus source grep and Loogle. No duplicate
   abelian statement was found. Read the nearby set representative/equality
   modules, SitePullbackAbelianUnderlying and ColimitSiteSections: their extra
   finite-limit/comparison hypotheses or already supplied sheaf colimit prevent
   direct application here. Closing either remaining construction is not a
   few-minute proof.

4. **Route and pruning: PASS.** Mathlib's filtered-set recognition and reflection
   are the direct final assembly; no shorter applicable theorem was found. The
   three added parent imports are proof-only. The public group limit, colimit and
   filtered-colimit imports supply the concrete sheafification and Kan-extension
   instances used by the signatures, as well as reflection in the parent. The
   "No longer needed" list contains all seven removed parent proof dependencies;
   category-colimit is retained and the seven are relocated, not claimed globally
   pruned. Read sk-thm-p1.json including realized: the parent is not a realized
   statement or step, and no unit route or unit record is changed. This delivery
   closes one original hole and adds two lower holes: a decomposition, net -1
   before pruning, not a sorry-free proof of the section formula.

5. **DAG correspondence: PASS.** Parsed all three node files and checked each
   recorded Lean signature against its source verbatim, each proof_deps against
   the union of proof-step uses, and the parent fields against the repository.
   Only proof, proof_deps and proof_origin changed in the existing node. The two
   new nodes have the required creation, blueprint, chapter/unit, source, search,
   split status and Lean records. Their proof sketches describe the construction
   still left open; the parent sketch describes the actual reduction and helpers.

Second reading changed only this report by adding the independent review and
verification evidence. No mathematical or Lean repair was necessary. Scratch
axiom-check copies are under scratchpad and are excluded from delivery.
