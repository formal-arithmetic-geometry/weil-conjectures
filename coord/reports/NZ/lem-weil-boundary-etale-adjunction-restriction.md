# Stage-1 report: lem-weil-boundary-etale-adjunction-restriction

## Files written

- dag/nodes/sec-six-functors/lem-weil-boundary-etale-adjunction-restriction.json: item, statement, split into eight steps. No full Mathlib match.
- citations.json: one exact quotation from the statement of each node used by each step (26 entries).
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. All 20 proof dependencies already exist in the live DAG.

## Attachments

None. I searched the project source for the blueprint id and the notions, and read WeilConjectures/SixFunctors/Etale/Derived/UpperShriek.lean, including hasBoundedBelowUpperShriek and the ambient adjunction. It gives important portions, but no declaration found states every geometric assertion, the actual full-subcategory unit/counit normalization, and the lower-bound reflection and specified comparison-unit assertion together. The partial source results are not an attachment for this item. No compiler, Lake, or build was run.

## WANTED

None. The relevant documents and source texts are available locally.

## What was wrong or missing

The item was statement-only. Its statement is unchanged. The missing proof must establish boundedness of the ambient right adjoint before restricting the adjunction; using bounded-below full faithfulness on that right-adjoint value first would be circular. I instead use finite cohomological dimension and the existing generic unbounded upper-amplitude theorem. I checked the actual statement of lem-pur-bounded-heart-amplitude and rejected it as insufficient here: that node only treats bounded inputs. The stronger needed statement is already lem-etale-derived-functor-upper-amplitude. Thus no new amplitude node, no relabelled clause of the item, and no assumption of a pro-etale ambient adjoint is needed.

The nearest blueprint ancestor is cor-weil-boundary-duality-discharge, through lem-weil-boundary-dualizing-composition. The master ancestor text and current DAG/unit record were read. The dated main snapshot does not contain that path, so I use the existing master ancestor text explicitly as an agent proof origin. The unit has no proof steps in its record and this is not its key statement; no unit realization fields were changed. The chapter/unit route is preserved: this is preliminary ordinary etale adjunction preparation for the boundary identification. I use no SGA source.

## Not duplicates

No new nodes were created. Searches of the DAG and blueprint found the existing finite-type dimension, Nagata, ordinary exceptional-adjoint, relative torsion dimension, unbounded derived amplitude, exact comparison, and bounded-below unit nodes. In particular lem-etale-derived-functor-upper-amplitude and lem-etale-upper-shriek-explicit-amplitude-interface are reused rather than duplicated.

## Review by NZ

I read the supplied contract, GOAL.md, stage-1 brief, stage document, the three blueprint levels in SETUP.md, delivery-errors B through E, the item, chapter and unit records, its ancestor boundary-duality text, and the source declaration search results. The source of the finished proof is agent-written synthesis of those existing statements, not a claim that the ancestor already contains the detailed argument. I read the statements of every node in the proof dependency union and copied their exact text to citations.json; the quotations do not borrow properties from their proofs.

For step 1, clause 4 of def-weil-l-adic-coefficient-extension supplies finite commutative A. Finite additive groups are torsion, and finite A annihilates its module sheaves locally (indeed uniformly). A field is Noetherian directly from its two ideals. The finite-type-over-Noetherian and locally-Noetherian-quasi-separated nodes give exactly Noetherianity and quasi-separatedness of V and W. The Nagata statement supplies existence over a qcqs target, with separatedness and finite type present in the item. I read morphisms.tex lemma-finite-type-noetherian (01T6) and properties.tex lemma-locally-Noetherian-quasi-separated (01OY), not just their tag names.

For step 2, properness includes finite type, and lem-sfb-finite-type-composition-base-change supplies the composition over k. The same Noetherian/QS statements apply to every chosen ambient scheme. I read the blueprint source and current statement of lem-kun-dimension-finite-type: it asserts finite dimension of any finite-type scheme over a field. This gives a nonnegative integer bound; the empty case is handled separately by zero. Density of the open is never required. This is an arbitrary compactification, not only Nagata's chosen one.

Step 3 applies precisely thm-amb-etale-exceptional-adjoint, whose current statement requires a finite commutative coefficient ring and Noetherian schemes and whose source blueprint text I read. Those hypotheses were established before application. Its ordinary unbounded module categories are exactly the item's categories. The proof does not substitute a condensed coefficient category or an unsupported pro-etale adjunction.

For step 4, I verified that the extension-by-zero exactness node and the exact-functor/cohomology node give preservation of all lower (and upper) bounds. The module direct-image statement actually asserts additive left exactness. The negative-vanishing node asserts the lower bound for D-plus, and src-right-derived-functor-plus-compatibility identifies the bounded-below and unbounded right derived functors, so there is no silent change of construction. The source is derived.tex negative-vanishing (05TC), together with sites-modules.tex extension-by-zero-exact (03DJ) and the explicitly cited compatibility statement.

For step 5, I read the relative torsion bound node, which allows separably closed k and any additively torsion commutative coefficient ring; hence the ring hypothesis is satisfied without importing an extra invertibility argument. The geometric hypotheses are qc plus locally finite type p, W locally finite type over k, and dim(ambient) at most d_c; all were checked. Its conclusion is the higher-image vanishing for every module sheaf, not merely constructible sheaves. I read derived.tex lemma-unbounded-right-derived (07K7), especially (4)(c), and the actual existing upper-amplitude statement. The cited Grothendieck, enough-injectives and K-injective statements provide its resolution hypotheses for the ordinary module-sheaf category in a common larger universe. The upper bound applies to unbounded-below inputs. Composing with the exact j-shriek gives the precise hypothesis of the existing exceptional-adjoint amplitude criterion. That criterion only claims preservation of D-plus, which is all this step takes. This avoids the bounded-input gap. No new node hides this argument.

Step 6 is the explicit elementary full-subcategory argument: both functors land in D-plus by the preceding proof, Hom sets literally agree, naturality is inherited, and the transposes of identities give the ambient unit and counit. I also read Mathlib CategoryTheory/Adjunction/Restrict.lean lines 28-84 after the logged Loogle and grep hits. Its general restriction lemma agrees with this argument, but is only part of the item and cannot turn the whole item into a Mathlib leaf.

For step 7 I read the exact-comparison node, including its unbounded termwise cohomology statement, and Bhatt--Scholze Corollary 5.1.6 in the local PDF together with thm-weil-pbc-site-comparison. The latter is for ordinary modules over a finite discrete ring, with no constructibility assumption. It supplies faithfulness on degree-zero sheaves. Faithfulness reflects the equality identity=zero, hence zero objects; exactness computes cohomology degree by degree. This proves reflection for arbitrary unbounded C, without falsely applying the D-plus unit theorem to such C. This short deduction is elementary relative to its two cited statements.

For step 8, I checked that the map being used is the unit named by thm-weil-pbc-site-comparison, not an unspecified isomorphism between its objects. It is applied only to the given bounded-below L. Its isomorphic target is bounded below; step 5 handles both right-adjoint values and exact comparison preserves that property. Applying the composite functor to the unit's inverse proves precisely the displayed canonical map is invertible.

I tested the empty ambient scheme (zero module category and d_c=0), a nonempty zero-dimensional scheme, arbitrary disconnected finite-type schemes (still Noetherian of uniformly finite dimension), arbitrary shifts, unbounded-below C in step 7, and coefficient levels n=1 and n>1. Nothing uses regularity or that A is a field; a non-field Artinian quotient is allowed. Every non-elementary fact used is supplied by a cited statement, and no step exceeds 2000 characters (maximum 1051). Elementary steps 6--8 give the actual Hom/identity/cohomology arguments. Off-unit preliminary tool uses are declared in split_report.tool_uses for review, not installed as accepted tool_uses. No source error or statement dispute was found.

The item's inherited Mathlib searches are retained. Additional searches were run with the prescribed msearch.py and read from searches.jsonl; their exact query text and hits were added only when actually logged. Generic restriction, t-structure, sheaf-adjunction and etale-site hits do not state this full item. There are no new nodes requiring new-node search gates.

## Unfinished work

No mathematical part remains in this one-level split. Dry-run and delivery results follow below once the required tools finish.
