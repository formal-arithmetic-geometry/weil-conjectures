# Stage-1 report: lem-trf-positive-copy-graded-quotient

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-positive-copy-graded-quotient.json`: statement, split into six proof steps; not a Mathlib leaf. The statement and statement dependencies are unchanged.
- `citations.json`: eight verbatim statement excerpts, one for each step/node citation.
- `report.md`: this report. `searches.jsonl` is the search command's own log.

There are zero new nodes and zero new Mathlib leaves. The inherited item searches are retained, with five actually executed Q146 searches appended. No prior split or report existed in this sandbox.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id, positive-copy spellings, homogenization, graded quotients, and symmetric surjectivity. Hits on dehomogenization and symmetric-algebra maps for module quotients do not state the present sheaf-algebra construction and all its clauses. No Mathlib declaration is proposed as a project attachment.

## WANTED

None. Sources used are present locally.

## Corrections and scope

No statement correction or dispute is needed. The empty proof was replaced by the actual construction and argument, rather than a new node restating each conclusion. In particular the argument does not identify a categorical sheaf coproduct with sectionwise direct sums on arbitrary opens. It proves the identification on affines from the existing tilde functor's coproduct property. Arbitrary affine inclusions are handled by the canonical summand maps, without assuming that they are principal open inclusions or that intersections of affine opens are affine.

The source for the item is Stacks Tag 0B3I, `morphisms-lemma-finite-projective`, read at morphisms.tex:11237–11285. That proof uses the same degree-one unit element in the pushforward algebra for the canonical projective-bundle embedding; the positive-copy calculation is an agent-written verification below that construction, as the item's source already says. I also read Schemes Tags 01I7, 01IB, 01ID (`lemma-compare-constructions`, `lemma-equivalence-quasi-coherent`, `lemma-colimit-quasi-coherent`), Modules Tag 01CF and Lemma 01CG (`section-symmetric-exterior`, `lemma-local-tensor-algebra`), and Algebra Tag 00DM (`section-tensor-algebra`). The tag-to-label table was checked. The proof origin remains explicitly agent-written. No SGA source is used.

The blueprint ancestor is `lem-trf-local-term-locality`; this algebra construction serves its already-established finite-projective-bundle descendant, not a replacement of the unit's contracting-correspondence argument. I read the chapter and unit records and the ancestor's current `blueprint_update`. Full-blueprint searches for direct sums, symmetric algebra, positive-copy, positive degree and symmetric quotient found no other blueprint node with this item's statement. DAG searches found the affine tilde/sections and restriction theorems already present; these are reused. The symmetric universal-property and grading nodes are declared as generic tool uses from another unit.

## Not duplicates

No new nodes are created. The existing coproduct quasi-coherence nodes were found, but the affine tilde/sections theorem already supplies both the local model and its sections in one argument. There is no need to create a second affine coproduct comparison or a special symmetric-surjectivity lemma.

## Unfinished

None of the stage-1 split remains to be written. No Lean was written or compiled. Delivery is subject to the required server dry run and push.

## Review by Q146

I checked the split against delivery-errors B through E with the cited statements open. There are no statement-only auxiliaries to audit and no Mathlib-leaf claims. The item's unchanged objects are introduced in its statement and its existing definition dependencies remain valid. All six steps are below 2000 characters. No step conceals an independent comparison theorem: the affine comparison is an application of the already existing, explicitly stated colimit-preservation and unit/counit theorem.

Step 1 uses `def-weil-pbc-quasi-coherent-algebra` for the underlying quasi-coherent module and algebra structure, and `def-weil-pbc-graded-sheaf-structures` for the homogeneous laws and their extension to the sheaf direct sum. I checked the latter really includes bilinearity plus sheafification extension; I do not cite a definition for a separate sheafification theorem. The written cases cover three, two, one and zero positive degrees, using multiplicativity and unitality of the given structure map. There is no assumption that this map is injective.

Step 2 uses `lem-weil-pbc-module-restriction-open-immersion-colimits`, whose statement explicitly covers both colimits and preservation of quasi-coherence under open restriction. It then uses clauses (2), (3) and (4) of `lem-weil-pbc-affine-tilde-gamma-adjunction`: global sections of a tilde module, the counit for a quasi-coherent module, and tilde preserving all small colimits. The diagram is the small discrete family indexed by natural numbers. Thus its hypotheses apply to every affine open of an arbitrary scheme; no global qcqs hypothesis is inserted. The definition `pqf-def-coherent` turns the resulting affine models into quasi-coherence. The structure sheaf on Spec R is the associated module for R, from the affine structure-sheaf construction. I read the above Schemes lemmas for this use.

Step 3 uses the explicit canonical map established in Step 2, not another node's proof. Checking products on the summand inclusions and distributing over finite sums proves the algebra comparison. Restriction of those very inclusions computes the map on every degree, and is enough to prove naturality for arbitrary affine inclusions. This is a calculation, so it needs no new generic naturality lemma.

Step 4 uses clause (a) of `lem-weil-pbc-quasi-coherent-symmetric-algebra`, which explicitly allows every target algebra sheaf and imposes only quasi-coherence on the source module. Step 1 supplies a commutative unital target and the coproduct inclusion is linear. The theorem therefore supplies existence and uniqueness of the underlying algebra map, exactly as claimed.

Step 5 uses clause (b) of that same node and the actual statement of `lem-weil-pbc-symmetric-algebra-graded`, which says that the homogeneous part is spanned by products of n degree-one generators. The displayed product image proves degree preservation on affines. The sheaf symmetric grading is the sheafification of these homogeneous components, as in Modules 01CF/01CG; restriction of generators respects their degree. This is why the check proves a graded sheaf map and is not merely an ungraded universal-property assertion. The affine-section isomorphism here is the one extending the given degree-one map, a compatibility explicitly included in the cited statement.

Step 6 uses the previously constructed q and gives an actual homogeneous preimage: j(a) times j(1_E) to the power n−1. Multiplication by that fixed section defines a restriction-compatible linear map into the degree-n sheaf, whose composite with q_n is the identity on E. This directly verifies surjectivity without another node. I checked n=0 separately (identity), n=1 (zero exponent), E=0 over a nonzero base, a noninjective map such as Z to Z/2, and arbitrary non-finitely-generated E. If E=0, both positive-degree sheaves vanish, while degree zero stays O_S; none of the proof conflates 1_E in degree one with the algebra unit 1 in degree zero. The empty base is vacuous. These checks confirm that neither finiteness nor local freeness nor faithfulness of the structure map was silently used.

For the Mathlib audit I read all returned search hits. Loogle's `SymmetricAlgebra.lift` and `lift_ι_apply` were opened at Basic.lean:99 and :113; they give the ring-level lift, not the whole sheaf construction. LeanSearch returned quasi-coherence structures, and two LeanFinder phrasings returned general graded algebras and Proj constructions. The restricted AlgebraicGeometry grep returned zero hits. Those outcomes are recorded as no match, with exact query strings taken from the command's log. Existing item searches were preserved rather than attributed to Q146.
