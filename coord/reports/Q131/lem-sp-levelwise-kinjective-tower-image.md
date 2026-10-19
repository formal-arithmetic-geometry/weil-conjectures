# Q131: lem-sp-levelwise-kinjective-tower-image

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-levelwise-kinjective-tower-image.json`: item, statement, split in six steps; no full Mathlib match.
- `citations.json`: one verbatim statement quotation for every step/node pair.
- `searches.jsonl`: actual search-command records, retained in the sandbox.
- `report.md`: this report.

No new nodes; no new Mathlib leaves. All work is in the assigned sandbox. No git command, Lean edit, compiler, Lake invocation or local preflight script was run.

## Attachments

None. Searched the slopmaster2 project's WeilConjectures tree by the exact item id and by K-injective, IsKInjective, tower and evaluation. There is no project declaration stating all the clauses of this item. The existing DAG evaluation lemma has a closed audit, but proves only evaluation preservation, so it is a dependency rather than an attachment for this item. Master-source sorry declarations were not used as finished proofs.

## WANTED

None. The relevant Stacks sources and current blueprint are available locally.

## What was wrong or missing

The item was unsplit, with an empty proof. Its statement is valid as written; no STATEMENT-DISPUTED correction is required. Added only the existing definition citation `def-sfb-right-derived-functor` to explain the already stipulated total right derived functor and canonical comparison. Retained the inherited statement, source, searches, creation record, unit and blueprint ancestry otherwise. The extra definition is not an extra hypothesis on G.

The important distinction is between a K-injective tower and a tower whose evaluations are K-injective. The latter need not itself be K-injective. The proof never identifies these notions. Likewise, the homotopy inverses of q_n need not form a strict tower map. Only the actual q does; its image is the strict comparison, and levelwise quasi-isomorphisms suffice for localization.

The ancestor is fix-lem-exchanges (via lem-sp-completed-pullback-adjunction). I read the current blueprint statement and proof at `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/fix-lem-exchanges{,.proof}.md`, the item chapter and unit records, and the parent statement. This is the generic strict-tower calculation supporting the integral naturality/pasting argument, not a replacement of the unit's geometric route. The old chapter filename in inherited metadata differs from the current blueprint location; I retained the maintainer-owned chapter/unit and ancestry.

## Not duplicates

No new nodes were created. The whole-DAG searches by Tags 0941/070I and K-injective evaluation/comparison terminology, and blueprint_refs searches for K-injective, levelwise, and strict tower K-injective evaluation quasi-isomorphism, identify the existing tools used below. In particular lem-weil-tower-evaluation-kinjective states exactly evaluation preservation, lem-weil-pbc-kinjective-hom-derived supplies homotopy equivalence, and lem-weil-tower-category-levelwise-abelian supplies exact evaluation. None should be duplicated. No blueprint node found states this full levelwise-derived-image assertion, so the item's same_as remains [].

## Review by Q131

I read Stacks `sites-cohomology.tex`, Tag 0941 (lemma-derived-limit-is-ok), specifically the paragraph constructing the exact left adjoint to evaluation and applying preservation of K-injectives. I read `derived.tex`, Tag 070I (lemma-K-injective), including all three equivalent conditions and the proof, and Tags 070Y/070K (lemma-K-injective-defined and lemma-enough-K-injectives-implies), including their K-injective computation argument. The full statement here combines these results with the explicit calculations below; its proof_origin is therefore agent. No SGA source is used. There are no new-node sources to review.

For step 1 I opened the statements of lem-weil-tower-category-levelwise-abelian and lem-weil-tower-evaluation-kinjective. The former explicitly gives abelianness and exact evaluation, hence evaluated cohomology; the latter explicitly gives K-injectivity of the evaluated complex without boundedness, enough-injectives or transition assumptions. They apply to A=Mod(R), an abelian category by the item's existing definition dependency. Positive versus nonnegative indexing is just the order isomorphism n -> n-1. This proves both claims about q_n; no hypothesis about degreewise injective terms has entered.

For step 2 I opened lem-weil-pbc-kinjective-hom-derived. Its final sentence explicitly says that a quasi-isomorphism between K-injective complexes is a homotopy equivalence. The source X_n is K-injective by the item hypothesis, the target by step 1, and q_n is a quasi-isomorphism by exact evaluation. I deliberately do not assume these levelwise inverses are compatible with transitions.

Step 3 uses the actual additivity definition in def-weil-pbc-additive-functor. Applying G to f-g=dh+hd preserves the equation, so the two inverse homotopies remain inverse homotopies. The cohomology definition in def-weil-abstract-derived-category shows directly why homotopic maps induce equal cohomology maps: dh+hd restricts on cycles to a boundary. Thus G(q_n) induces inverse maps on cohomology. This is a short elementary calculation, not an assertion that an arbitrary additive functor preserves all quasi-isomorphisms. In particular G need not be left exact.

Step 4 uses lem-weil-tower-category-levelwise-abelian again for kernels and cokernels in the target tower category. It spells out why inverse components commute with transitions, so a levelwise isomorphism of cohomology towers is an isomorphism of towers. Localization at quasi-isomorphisms is exactly the statement of def-weil-abstract-derived-category. This makes the single actual strict tower map Tq invertible in the derived tower category, rather than merely producing unrelated isomorphisms of evaluated derived objects.

For step 5 I read def-sfb-right-derived-functor's full statement. It gives a natural unit, explicitly says its component on a K-injective is invertible, and supplies the canonical computation using any K-injective resolution. Q is K-injective in the tower category by the stipulated resolution, and q is a quasi-isomorphism. The formula c_q=eta_Q^{-1} RT(q) and the naturality identity c_q eta_X=L(Tq) then identify the canonical unit, not a newly chosen isomorphism. Existence of the stated total derived construction is already stipulated by the item's wording; this proof does not introduce monomorphic-resolution, boundedness or left-exactness hypotheses. This is a use of an existing derived-functor interface whose computation assertion is explicitly in its statement, not an appeal to a definition node for an unstated theorem. Generic off-unit uses are declared in split_report.tool_uses.

Step 6 uses that same natural unit for naturality in strict maps. I wrote the transition equation q_n t_n^X=t_n^Q q_{n+1} and its image under G, which proves the precise compatibility needed. The final constant-term, endomorphism-transition assertion is then the definition of the image tower and step 5; it is not delegated to a new node restating a clause of the item. Independence of the resolution follows because the comparison just proved invertible is the fixed natural unit.

I checked the edge cases G=0 and G=identity, X=0, q=identity on a K-injective tower, and transitions s=0 or s=identity. The displayed homotopy equations, strict squares and canonical-unit formula remain valid. Unbounded complexes cause no infinite sum: every homotopy equation uses only two compositions. There is no product-exactness argument. I checked that none of the four substantive existing tool nodes reaches this item through statement/proof dependencies. Each citation quote was tested as a literal substring of the cited statement. All six proof steps have fewer than 2000 characters; none hides a separate comparison lemma or a standard argument. The elementary steps write out the argument from the cited interfaces. These checks address delivery-errors B through E: no duplicate/elementary/restatement child, no uncited non-elementary input, no mismatch of cited hypotheses or objects, and explicit coherence equations.

The own Mathlib searches ran through msearch.py: two distinct LeanFinder phrasings, Loogle, LeanSearch and two greps. Read the hits and the sources DerivedCategory/KInjective.lean:41-58, CategoryTheory/Abelian/RightDerived.lean:25-65 and Algebra/Homology/Localization.lean around 346-355. KInjective.quasiIso_iff is a constituent already represented by the existing DAG leaf, rightDerived is the individual-object/natural-number construction, and mapHomologicalComplex_upToQuasiIso_Q_inverts_quasiIso requires preservation of homology, which is not assumed here. Thus there is no full-item Mathlib match. All existing imported searches were retained and actual own searches appended from their log, with exactly the executed tool/query texts.

## Unfinished work

None in the mathematical split. Delivery validation and push are recorded below after the required tool exits.
