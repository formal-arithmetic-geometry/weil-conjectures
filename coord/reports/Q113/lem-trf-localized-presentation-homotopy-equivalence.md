## Worker report

Files written: dag/nodes/sec-trace-formula/lem-trf-localized-presentation-homotopy-equivalence.json (statement, split; no full Mathlib match). Also citations.json (11 literal excerpts), searches.jsonl (five executed searches), and this report. No new nodes, no new Mathlib leaves. The original statement, source, created record, blueprint ancestry and earlier search records are retained. There was no earlier split or report in this sandbox. No repair note exists for this item.

Attachments: none. Searched lean/WeilConjectures for the exact blueprint id and localized-presentation terminology, then for conormal, cotangent and homotopy. The matches concern other presentations, Koszul comparisons or abstract minimal complexes and do not give this assertion. No declaration satisfying the attachment criterion was found.

WANTED: none.

The item had no proof. Its statement is correct, including the need for a lift only modulo I squared. Stacks 00S1 proves the polynomial case; it cannot be applied directly with the localized ring as a polynomial presentation or used to claim an inverse ring map. The split uses the already present 04EG square-zero-lifting leaf instead. The inherited source accurately describes this extension. The assembly now supplies the calculations that 00S1 omits.

Nothing remains unfinished in stage 1. No Lean was written and no compiler, Lake or build tool was invoked.

## Sources and route

Read literature/stacks-project/algebra.tex, Tag 00S1 (lemma-NL-homotopy), statement and entire proof, Tag 04EG (lemma-localization-formally-etale), statement and proof, and Tags 07BK (definition-differentials) and 00RO (lemma-universal-omega), including the displayed generators-and-relations construction. Checked tag-to-label assignments in literature/stacks-project/tags/tags.

Read the trace-formula chapter and sk-i-curve-zero unit records and the current blueprint/latest statement and proof of lem-trf-local-term-locality (current snapshot 7284bb09daf97437d544c51882b325f9c52cd345). This item is a subordinate commutative-algebra input extracted along the existing semistable-modification/dualizing-line route, not the unit's key node. Its exact existing blueprint.from.place and via chain are preserved; the two higher-level records need no change. The current ancestor proof does not itself state this algebra lemma. Whole-blueprint searches for cotangent, homotopy, localization and formally etale yield no equivalent blueprint assertion. same_as remains empty. No SGA source is used.

## Search and reuse

DAG searches by 00S1, 04EG, homotopy presentation, difference derivation and square-zero lifting found the existing leaves lem-trf-conormal-semilinear-difference-homotopy and lem-weil-pbc-localization-square-zero-lifting. Opened their entire statements. The polynomial-only lem-weil-pbc-nl-presentations-homotopy-equivalent does not apply to P and is deliberately not used to supply the localized assertion. Read def-weil-pbc-mv-polynomial-ring and def-weil-pbc-kahler-differentials in full. Also read the parent lem-trf-lci-naive-cotangent-model statement and dependencies and def-trf-naive-cotangent-comparison-data: neither can be used as an input, and neither is needed.

Ran five searches through the required msearch command: two LeanFinder phrasings, LeanSearch, Loogle and grep. All were available. Read the hits, particularly Extension/Cotangent/Basic.lean:142-319 (chain maps and difference homotopy), Extension/Cotangent/LocalizationAway.lean:188-219 (a conormal decomposition for principal localization), Extension/Basic.lean:465-504 (conormal maps) and Smooth/Basic.lean:195-230,482-499 (infinitesimal lifting and localization). homInfinitesimal is a map modulo square ideals; equivOfFormallySmooth concerns H1 alone. Neither it nor the principal-localization decomposition provides the requested full two-term chain homotopy inverse in one specialization. The matching ingredients already have DAG leaves, so no duplicate leaf is created. The original search records are historical inherited records; all five newly added entries correspond exactly to searches.jsonl.

## Not duplicates

No new nodes. The split reuses the two existing Mathlib leaves instead of duplicating 04EG or 00S1. The polynomial-only presentation equivalence is a special case of the item; it is not a duplicate of a new node and cannot replace this item's localized assertion.

## Review by Q113

I checked the statement against 00S1 and 04EG with the source open. Both variable sets may be infinite; the polynomial universal property is stated for a set, and all subsequent differential expressions use finite sums only. The only localization input is lifting across a square-zero ideal; no finite-presentation, noetherian, regular-sequence or invertibility hypothesis on B has been added. The statement is unchanged. I checked delivery-errors B1-B10, C1-C8, D1-D5 and E1-E7 individually against the actual steps. There are no new nodes to audit under B1/B2/B5/B6; notions and source tags are explicit. The argument is not a move into another node or a circular use of the parent. All non-elementary inputs are the cited statements, rather than their proofs. Citations.json has one verbatim excerpt for each step-node pair. No proof step exceeds 2000 characters.

Step 1 uses precisely the polynomial node's existence and uniqueness of evaluation maps and the semilinear-difference leaf's assertion that any map between arbitrary surjections induces the stated chain map. I checked that the leaf explicitly does not require polynomial rings, and specializes to the identity coefficient maps. Surjectivity of P to B gives the chosen variable preimages.

Step 2 uses the same evaluation universal property to make D an A[E]-algebra; I checked this change of base explicitly because the localization lifting leaf is a relative lifting assertion. Its statement assumes a localization of the base ring and an ideal of square zero in the target, exactly A[E], P, D and M here. The identities ker(D to B)=I/I² and M²=0 are quotient calculations, not an appeal to formal smoothness of the composite A to P. Consequently that cited leaf really produces ell. It is a Mathlib leaf, so its off-unit location is a generic tool and does not replace the unit's geometric route.

Step 3 is the explicit Leibniz calculation from the definition of differentials: every generator xy of I² has zero differential after tensoring with B. The same calculation is written for J². This supplies the two quotient derivations and identifies their restrictions with the displayed conormal differentials without assuming an unproved comparison theorem.

Step 4 uses the cited differential universal property, which actually states the bijection between linear maps and derivations. The square-zero property proves ell kills J² and the scalar equation proves B-linearity of g in degree -1. Applying the universal property with the P-action through B gives the degree-zero map after tensoring. The chain equation is checked on a representative h. These are elementary consequences of the stated universal property and step 2, not a hidden inverse-map theorem.

Step 5 uses the polynomial universal property again, this time only for R, so a genuine t:R to R lifting ell a exists. The generator computations show N(t)=gN(a), since the quotient derivation kills I². The semilinear-difference leaf then applies to the genuine maps t and id_R. Its statement supplies both identities with the sign t-id, giving the correct sign gN(a)-1. I checked the component notation: superscript -1 means degree, not an inverse. No map P to R is claimed.

Step 6 is the difference-derivation calculation in 00S1 written directly in P/J², because a lift to the actual ring P is unavailable. Both maps have the same reduction to B, so their difference lies in J/J². Expanding the product makes its extra quadratic difference term zero. Thus the differential universal property cited here is sufficient to construct H_P. This is the elementary square-zero calculation, not a separate presentation-equivalence lemma.

Step 7 verifies both homotopy equations on the conormal and differential generators. The semilinear-difference leaf supplies the formula for the forward map N(a); its degree -1 map is exactly [i] mapped to [a(i)], and its degree-zero map is exactly dr mapped to d(a(r)). It is not cited for an actual ring map P to R or for a homotopy modulo squares. The identity between quotient derivations is proved by evaluating every element q_R(r), so no naturality theorem is concealed by a word such as 'transport'. These equations, with step 5, are precisely the definition of a homotopy equivalence of the given two-term complexes.

I tested the degeneracies explicitly. If W={1}, ell is simply polynomial-variable lifting. If a unit of B comes from an element of W not invertible in R, only its image modulo I² must be invertible; the 04EG input proves exactly that and no impossible inverse ring map is used. If B=0, then I=R and J=P and all terms vanish, so every formula is zero. This also covers 0 in W, which forces P=B=0. Empty variable sets cause no problem for evaluation; choosing preimages is then vacuous. In characteristic two the subtraction formulas still satisfy the displayed additive identities. No cancellation or division by an integer occurs. Infinite variable sets require no finite free module assumption. The square-zero kernel and the two scalar actions were verified at the exact steps where used.

No statement correction was needed. I corrected the only potential ambiguity in the draft proof, placing parentheses around the degree -1 component (gN(a))^{-1}; the item's original statement and all metadata outside split-owned fields remain intact. The completed dry-run result is recorded below after the server checks finish.

## Validation

Server dry run exited successfully: OK (not pushed) at f9a79e196f8, preflight passed, including the server DAG and split checks. Local read-only comparison also confirmed an unchanged statement, exactly the union of step citations in proof_deps, 11 valid verbatim excerpts and zero new nodes. This report-only validation entry is followed by the final dry run and direct delivery.
