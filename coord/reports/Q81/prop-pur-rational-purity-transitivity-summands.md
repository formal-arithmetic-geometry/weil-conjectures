## Files written

- `dag/nodes/sec-smooth-purity/prop-pur-rational-purity-transitivity-summands.json`: repaired split, seven steps; statement and Lean record unchanged.
- `dag/nodes/sec-smooth-purity/lem-pur-semilinear-scalar-localization.json`: statement-only generic semilinear localization and exact-comparison transport lemma; unsplit, no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-pur-two-square-interchange.json`: Mathlib leaf, exact `CategoryTheory.TwoSquare.hCompVCompHComp`, `Mathlib/CategoryTheory/Functor/TwoSquare.lean:155` (definitions at 130–143).
- `citations.json`: every proof-step citation with a literal quotation of the cited statement. Existing quotations and search log retained.

## Attachments

None. The item's project declaration audit is `none`; searching WeilConjectures for its blueprint id, purity/transitivity and semilinear localization supplied no declaration stating the whole item. The source has general TwoSquare uses and adjunction mate formulas, not an attachment of this assertion. Upstream master is reference material only.

## WANTED

None. Both extracted facts are generic categorical tools. Their blueprint source place is the finite-extension sentence of `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-field-extension/prop-pur-rational-purity-transitivity-summands.proof.md`; no SGA route is used. The semilinear tool is agent-extracted rather than attributed to a nonexistent Stacks tag.

## What was wrong and what changed

The returned version's old Step 3 mixed extension across different valuation rings, natural-transformation transport, exactness/coherence, and a tensor-associator pasting argument. The retained interrupted repair already extracted the former into `lem-pur-semilinear-scalar-localization` and logged six Mathlib searches, but left the whole pasting calculation in Step 3 and had no report. I read that retained statement, proof, citations and all logged result summaries, compared its item with the shared returned node, and continued the repair. Only proof, proof dependencies, status and split report differ on the item; its statement, source record, Lean/audit records and historical unit binding remain as returned.

The finite-extension argument is now Step 3, applying the semilinear tool, followed by Step 4, citing the exact Mathlib interchange theorem and substituting the original associator equations. It retains the explicit cancellation and equality with the direct extension. The two short steps are 764 and 1202 characters. Other arguments remain the same; their step references were renumbered. No non-elementary step exceeds 2000 characters. The two elementary summand calculations were read in full: they are direct substitutions of naturality, retraction and idempotent equations, with no hidden existence argument. Existence of splittings is cited explicitly.

## Not duplicates

lem-pur-semilinear-scalar-localization vs prop-weil-pbc-rational-transport: the latter assumes a single valuation ring and the same coefficient extension on source and target; the new statement permits an arbitrary ring homomorphism R → S and independently inverted t,u, and supplies semilinearity and preservation of whiskered equations.

lem-pur-semilinear-scalar-localization vs lem-weil-linear-scalar-localization-triangulated: the existing node constructs the triangulated structure and exact localization functor; it does not extend a functor between categories over different rings. The new node assumes that established structure when asserting exactness of the extension.

lem-pur-semilinear-scalar-localization vs lem-weil-linear-scalar-localization-category: the existing node constructs Hom modules, composition and shift for a single category; it does not state different-ring functor or comparison extension.

lem-pur-two-square-interchange vs lem-weil-pbc-mate-pasting: mate-pasting concerns adjunction transposes of squares; the new leaf is the interchange identity for arbitrary natural-transformation squares and assumes no adjunction.

lem-pur-two-square-interchange vs lem-cbc-proper-open-interchange-coherence: that node is about geometric proper/open exchange maps, not the generic grid interchange law. Searching all node statements and records for hCompVCompHComp and generic natural-transformation interchange found no existing node stating the leaf.

Whole-DAG keyword searches, `blueprint_refs.py search` for scalar localization, semilinear, semilinear scalar, pseudonatural, comparison squares, pasting, interchange and interchange law, and the ancestor query were read. The blueprint has geometric coefficient and pasting results but neither extracted generic statement. Both new nodes have ancestor the item itself and specify the finite-extension sentence they serve. Neither is the item's purity transitivity or summand clause: one supplies raw scalar functor transport; the other a general categorical interchange identity.

## Mathlib searches read

The retained semilinear searches are reused, not invented or rerun: grep for semilinearity and localization/liftNatTrans, Loogle for Localization/liftNatTrans, LeanSearch for semilinear functors and central scalars, and two LeanFinder phrasings. I read Mathlib `Localization/Linear.lean:29–100`, `Localization/Predicate.lean:322–354` and `RingTheory/Localization/Module.lean:205–225`. These respectively transport a same-ring linear structure along an already established categorical localization, lift transformations between already established lifts, and extend scalar linearity between modules already localized. None states the new concrete different-ring Hom-module localization theorem with the specified object map, fraction formula, coherence and exactness. These remain useful future proof ingredients; the node stays unsplit.

For the pasting tool I ran two semantic phrasings, LeanSearch, Loogle and grep. The final exact query and grid/interchange queries all returned `CategoryTheory.TwoSquare.hCompVCompHComp`. I opened `Functor/TwoSquare.lean:49–164`, including horizontal/vertical pasting formulas (130–143) and the complete theorem (155–164). The new statement is exactly that theorem, with all nine categories, twelve edge functors and four natural transformations introduced and its component formulas written explicitly. The final directory grep independently supplies file and line 155. Broader searches also found CatCommSq and bicategorical modifications; none is substituted for this exact match. Only actually executed queries are in the node records, with results copied from searches.jsonl.

## Review by Q81

I read the current blueprint proof named above, the current field-extension unit statement, the historical chapter and unit records (`sec-smooth-purity`, `sk-thm-purity-transport`, Step 3), and each cited node's actual statement. The blueprint's finite-extension-flatness sentence suppresses the coherence calculation; the repaired proof continues its same rationalization, finite-extension, common-stage, summand route. It does not infer equality of specified transformations merely from flatness. The main statement is identical to the returned statement.

Step 1 uses `thm-pur-rational-and-qbar-purity` for the precise geometric setting and the rationalization origin of gamma. `lem-weil-pbc-finite-type-over-noetherian` and `lem-kun-dimension-finite-type` provide noetherianity and finite dimension over the field k. `def-weil-pbc-rational-category` specifies the actual integral lattice category. `lem-weil-pbc-integral-stratified-perfect-characterization` explicitly identifies that category with the derived-complete integral category with the same completed sheaf and reductions, and `lem-coef-integral-residue-tor` explicitly provides uniform Tor bounds. Thus `lem-pur-adic-purity-scalar-naturality` applies to every lattice considered: smooth separated pure dimension d, finite-type separated schemes, and ell different from p all match its statement. Its statement supplies simultaneous gamma, exact functors, comparisons, the square and all composition/shift equations; I did not take these from an internal proof.

Step 2 invokes `prop-weil-pbc-rational-transport` only at one coefficient ring, where its exact linear functor hypotheses hold by Step 1. The fraction description is precisely that of `def-weil-pbc-rational-category`. Inverses and the displayed naturality equation are direct functorial computations, including rational idempotents without integral idempotent representatives.

Step 3 uses `prop-weil-pbc-scalar-extension` for ordinary derived tensor by the completed coefficient sheaf followed by rationalization, not tensor by a discrete field sheaf. `lem-pur-adic-purity-scalar-naturality` states comparisons for exactly this ordinary derived-tensor presentation. The new semilinear lemma applies with R=O_E, S=O_F: the image of a uniformizer is nonzero in F and hence invertible, without any assumption that the uniformizers agree or the extension is unramified. Its statement explicitly transports transformations, inverses, whiskered equations and exact shift comparisons, precisely the data used here.

Step 4 uses `lem-pur-two-square-interchange` for composition of natural-transformation squares. This exact Mathlib leaf is valid without exactness, invertibility or coefficient assumptions, so applies to the comparison grid. The composition laws substituted afterward are explicit clauses of `lem-pur-adic-purity-scalar-naturality`, transported by Step 3; the tensor associator is the one supplied by `prop-weil-pbc-scalar-extension`. Naturality moves A_X across the gamma arrow and gamma_L across A_Y; since A_X is an isomorphism, cancellation yields the direct coefficient square. This is a short application plus algebra, with the substantial general interchange now a cited node.

Step 5 applies the actual formula and the final compatible-transformation/equations clause of `prop-weil-pbc-descent-functors`. Steps 3–4 discharge its unit, associator and shift hypotheses. `def-weil-pbc-qbar-category` gives the pair objects and common-stage representative morphisms. The three-line naturality calculation is still explicit; it uses the previous squares and localized naturality, while the cited descent statement supplies representative independence. No small-colimit existence theorem is silently invoked.

Step 6 uses `def-weil-karoubi-envelope` for its identity e and sandwich condition, and computes both inverse composites directly. `thm-weil-pbc-finite-stage-karoubian` supplies actual splittings in the raw rational category under the scheme hypotheses checked in Step 1; `thm-weil-pbc-idempotent-complete-triangulation` supplies them at the algebraically closed stage. Neither category is silently replaced by its envelope. Step 7 uses the scalar functors of `prop-weil-pbc-scalar-extension` only to preserve the two splitting equations. Its remaining equalities are direct substitutions of naturality at i,r and of ri=1, including the common-stage classes already covered by Step 5. I checked the inverse formula and the alternate-splitting comparison r'i, ri'.

For the new semilinear statement I checked t=1, u=1, R=S with the identity coefficient map, ramified E ⊂ F with different uniformizers, t-torsion Hom modules, and t=0 when the target localization is zero. The invertibility hypothesis is essential: without it an integral arrow scaled by t need not have a scalar-localized image. Its formula kills localized torsion, respects composition by bilinearity, and gives transformation naturality after multiplying by phi(t)^(-n). Distinctive equations and shifts are part of its statement, not hidden instructions to a later worker. For the Mathlib leaf I checked identity squares, noninvertible transformations, empty categories and unrelated category universes: the theorem has no omitted restriction. For the item I checked K=0 and e=0,1; the restriction formulas produce the zero and full summands respectively.

This repairs the single numbered human demand in full: old Step 3's localization argument is extracted as an unsplit generic lemma, its nontrivial square-pasting law is a searched exact Mathlib leaf, the applications are short, and the original route, other arguments, statement and Lean record are retained. The two new nodes are statement-only. Generic off-unit tools are described in the retained `split_report.tool_uses`; no maintainer-owned tool_uses field was written. No live repository, launcher, Lean file or compiler was modified or run.

## Unfinished work

No stage-1 argument is left incomplete. The semilinear localization node is intentionally statement-only and unsplit, to enter the subsequent queue as required. Delivery validation follows this report.
