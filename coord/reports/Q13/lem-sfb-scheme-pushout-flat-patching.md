# Stage-1 report: lem-sfb-scheme-pushout-flat-patching

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-scheme-pushout-flat-patching.json: item, split into four complete steps; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-infinitesimal-pushout-affine-charts.json: statement-only supporting geometric lemma, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-fibre-product-algebra-flat-presentation.json: statement-only commutative-algebra lemma, unsplit; no Mathlib match.
- citations.json: each proof-step citation audited against the exact cited statement (the full statement is quoted verbatim).
- searches.jsonl: actual search-command log. write_split.py is the sandbox-local assembly script.

## Attachments

None. Searches of lean/WeilConjectures by the item tag, thickening pushouts, fibre-product algebra and patching found no declaration giving this item. The affinePushoutSection declarations concern a pushout of scalar rings and a scheme pullback, rather than a scheme pushout and a pullback of coefficient rings. Their presence does not attach this item.

## WANTED

None: all sources used are available in literature/stacks-project/. No SGA source is used.

## Corrections and scope

The item statement is correct as written and has not changed. Its arbitrary-thickening and non-finitely-presented-flat-W clauses are essential. A finite-order induction would be insufficient: a nil ideal need not have a uniform nilpotence exponent. The proof instead uses the algebra lemma for an arbitrary surjection. No Noetherian or quasi-compactness hypothesis has been introduced.

The imported blueprint reference has from.node null: tools/blueprint_refs.py ancestor lem-sfb-scheme-pushout-flat-patching prints None. I retained that computed ancestry and the complete inherited via chain, and gave precise source places in both new nodes. This is a broken upstream created.item chain, not an invented ancestor. The current route text was read from literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, proof (3). The latest unit and the imported dag/units/sk-thm-sf-ctf-stability.json differ, but this supporting scheme lemma does not replace any unit-level step or alter its theorem.

No unfinished proof remains in the item at stage 1. The two new supporting statements deliberately have no proof, proof dependencies or proof sketch in their statements. They enter the next splitting queue.

## Searches and reuse

Before creating either node I searched the entire DAG for Stacks 07RT, 07RV, 07RU, 08KH, 08KQ, the module-over-fibre-product labels, and patching/fibre-product titles. The existing ring-spectrum nodes supply topology/localization; they do not supply algebra flatness or finite presentation. Blueprint-wide searches with tools/blueprint_refs.py for pushout, fibre product, 07RV and 08KQ found no duplicate blueprint statement. I read the actual statements of all cited nodes, not their proof sketches. I inspected relevant Lean source hits and Mathlib source for the candidate directions.

The command log contains LeanFinder, Loogle, LeanSearch and source grep searches, with second natural-language phrasings for each new statement. LeanFinder's flat-module results are flatness under scalar extension and faithful-flat descent, which do not imply gluing over a ring pullback in one line. Its algebra results include Algebra.FinitePresentation.baseChange, a tensor-product pushout rather than the desired fibre-product patching theorem. Mathlib/RingTheory grep found no Milnor/patching/fibre-product result. The source Flat/Basic.lean:27 and Flat/Tensor.lean:14 comments only say that flat tensor preserves finite limits.

For the geometric node, Scheme.GlueData.gluedScheme is gluing along opens and AffineScheme.hasColimits only asserts colimits within affine schemes. Neither recovers input schemes by base change over a nil pushout. The corrected Loogle query uses CategoryTheory.IsPushout; the earlier Limits.IsPushout query had an unknown identifier, explicitly recorded in results. I read AlgebraicGeometry/Pullbacks.lean:794: isPullback_SpecMap_of_isPushout reverses a RING PUSHOUT to a SCHEME PULLBACK, the opposite construction to the desired geometric claim. Grep for thickening pushouts/patching in AlgebraicGeometry found no match. All recorded query texts were actually run through the prescribed msearch.py command; inherited item searches are preserved.

## Not duplicates

lem-sfb-infinitesimal-pushout-affine-charts vs lem-sfb-scheme-affine-thickening-pushout: the existing 07RT node states existence, cartesianness and the thickening of the base; the new lemma states recovery of an arbitrary compatible triple, compatible affine charts with their coordinate algebra identifications, and restriction of the pushout to opens. Those clauses are not in the existing statement.
lem-sfb-infinitesimal-pushout-affine-charts vs lem-sfb-scheme-pushout-flat-patching: the new lemma has no flatness or finite-presentation assertion and applies to arbitrary triples; it supplies geometry needed to reduce the item to algebra.
lem-sfb-infinitesimal-pushout-affine-charts vs lem-sfb-flat-lfp-space-pushout-gluing: the existing lemma is for algebraic spaces and flat local finite presentation; the new statement concerns affine charts and component recovery for schemes without flatness.
lem-sfb-infinitesimal-pushout-affine-charts vs lem-sfb-ring-fibre-product-spectrum: the existing statement is spectrum topology and principal localization of rings, not base-change recovery or affine charts for arbitrary scheme triples.
lem-sfb-infinitesimal-pushout-affine-charts vs lem-sfb-fibre-product-spectrum-topology: the existing statement is the topology of an affine ring pullback, not recovery of schemes or restriction of geometric pushouts.
lem-sfb-fibre-product-algebra-flat-presentation vs lem-sfb-scheme-pushout-flat-patching: the new lemma is commutative algebra for any surjective ring map, without a nil-kernel assumption; the item is a scheme theorem, with Zariski localization, arbitrary schemes and global reconstruction. The algebra lemma is the actual smaller source input of 07RX, namely 08KQ, rather than a renamed scheme conclusion.

## Review by Q13

I read more-morphisms.tex, Tag 07RX (lemma-equivalence-categories-schemes-over-pushout-flat), including its final flat-counit assertion and its proof referring to More on Algebra. I then read Tag 07RV (lemma-equivalence-categories-schemes-over-pushout), whose last paragraph supplies the two base-change identifications through 07RU, and Tag 07RT (lemma-pushout-along-thickening), whose ringed-space construction gives the sheaf fibre product and compatible affine open cover. I read more-algebra.tex, Tag 08KQ (lemma-properties-algebras-over-fibre-product), parts (2), (3), final assertion and their proofs, as well as the explicit module gluing statement 07RU and the flat-module statement 0D2I. These are the sources of the two new nodes, which are narrower than the whole scheme theorem.

Step 1 uses the new geometric statement for exactly its asserted affine coordinates and component recovery. In applying it the overlap is the supplied isomorphism X times_S T = Y times_T+ T, and the maps U to Y and U to X are respectively a thickening and an affine map. Its conclusion has no flatness assumption, so it is valid before either implication. No circular appeal to the item is involved.

Step 2 uses the affine-flatness criterion on the actual chart maps B to D and A' to C', and uses the existing lfp-affine-opens lemma to obtain finite presentation on EVERY such chart, rather than only an originally chosen presentation chart. The new algebra lemma assumes a surjection A' to A and precisely the comparison D tensor_B A = C'/IC', all supplied by Step 1. It yields finite presentation and flatness for R to E. The existing affine criterion turns the latter into flatness of the scheme morphism; the pointwise definition of local finite presentation gives the former on the covering. The definition node is used only for that definition, never for a preservation theorem.

Step 3 uses the component recovery from Step 1 for the base-change flatness lemma. For local finite presentation it instead works explicitly with E tensor_R B and E tensor_R A': the existing finite-presentation base-change-composition lemma really states the needed tensor base-change preservation, and the lfp-affine-opens lemma provides its hypothesis. The chart identifications really give D and C'. Existence of affine neighbourhoods is in the existing affine-opens-basis statement; the inverse-image opens cover without assuming intersections of affine opens are affine.

Step 4 uses the geometric node's open-restriction clause for epsilon inverse(W0). It does not assume that an arbitrary base change preserves a scheme pushout. The affine-spectrum fibre-product lemma supplies the three tensor rings and their canonical projection maps; the affine closed-pinching lemma supplies the pushout spectrum of the ring fibre product. Surjectivity of the middle map follows directly from the quotient A' to A, even after tensoring. Flatness of L over R follows from the affine-flatness criterion, and the algebra lemma's final assertion states exactly the canonical map whose spectrum is epsilon. Its inverse is therefore the inverse of the actual counit, not an unrelated abstract isomorphism. Local inverses coincide on overlaps by uniqueness of inverses after an affine refinement, and the existing scheme-morphism-gluing statement supplies their global morphism and verifies both identities. This needs no finite presentation of W.

For edge cases I checked T empty (A=0, the ring product case), the identity thickening, X and Y empty, and zero rings. The two new statements permit all of these, and the fibre-product and tensor expressions retain their meanings. For the algebra node A' to A can have non-nil kernel: it is genuinely the more general source assertion. For arbitrary thickenings, nilness is used only to identify underlying spaces and transfer opens; no power of the whole ideal is used. The item contains no proof step exceeding 2000 characters; the longest step is the explicit affine reconstruction and local-inverse gluing. I checked B1-B10, C1-C8, D1-D5 and E1-E7 against the node files and sources: statement-only new nodes, self-contained objects, named notions, correct tags and directions, exact citations, no clauses hidden as definitions or anonymous standard comparisons, no circular dependency, no route replacement, and no extra hypotheses.
