# Stage-1 delivery: lem-sfb-abelian-level-coarse-moduli

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-abelian-level-coarse-moduli.json: item, split into seven steps; statement unchanged. No project declaration states this result: searched the blueprint tag and coarse-moduli, abelian-level and curve-level terminology throughout lean/WeilConjectures.
- dag/nodes/sec-six-functors-basics/lem-sfb-coarse-moduli-open-restriction.json: statement-only general input, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-dm-open-finite-etale-permanence.json: statement-only general input, unsplit, no Mathlib match.
- citations.json: exact statement quotations for all 17 step/node citations.
- searches.jsonl and search-results.jsonl: actual command log and complete search outputs, respectively. write_split.py is sandbox-only drafting support; the JSON files are the delivery.

## Attachments

None.

## Literature wanted

WANTED: M. Pikaart and A. J. de Jong, Moduli of curves with non-abelian level structure, arXiv:alg-geom/9501003, Sections 2.3 and 2.3.3, for lem-sfb-abelian-level-coarse-moduli. The item already records this missing local PDF. Read the primary author PDF online at https://arxiv.org/pdf/alg-geom/9501003, printed pp.9–10: paragraphs before Theorem 2.3.2, Theorem 2.3.2(1), and the frame definition in 2.3.3. No document was downloaded or repository literature list edited.

## What was wrong and what changed

There was no proof. The imported statement and its non-symplectic level convention agree with the source; no statement correction or dispute is needed. I supply an agent-written proof using the local Stacks sources and existing DAG inputs. The chapter and unit route is unchanged: this is the coarse-scheme prerequisite of the level-moduli input for de Jong's stable-curve extension in the alteration reduction, below unit sk-thm-sf-ctf-stability. The item is not the unit key statement, so no unit realization file changes.

I initially considered adding stable-stack diagonal and coarse finite-cover inputs, but the refreshed DAG already contains lem-sfb-stable-isom-finite-unramified and lem-sfb-inertia-free-finite-cover-coarse. They are reused. Neither new node is a clause about curve moduli. One isolates general coarse localization, and one isolates atlas/descent permanence for arbitrary finite-diagonal stacks. The frame-cover argument and the curve-specific faithfulness application remain in the item's proof.

A potentially hidden extra premise has been removed: the finite-cohomology local-system theorem does not state rank 2g. The proof needs only that the frame sheaf is finite locally constant. Locally it is the finite set Isom_A(A^(2g),B), which can be empty. Consequently no rank theorem or surjectivity of the frame cover is asserted or needed. I do not cite the parent smooth-curve rigidification theorem, which depends on this item, or stable abelian-level normalization.

## Not duplicates

lem-sfb-coarse-moduli-open-restriction vs lem-sfb-stable-abelian-level-normalization: shared Tag 0DUT; the existing statement constructs a compactified normalization of curve moduli, whereas the new statement restricts any finite-diagonal stack's coarse scheme to an open substack. No normalization occurs in the new node.

lem-sfb-coarse-moduli-open-restriction vs lem-sfb-inertia-free-finite-cover-coarse: shared Tag 0DUT; the existing statement concerns an inertia-free finite cover of an already coarse-schemed stack, whereas the new statement produces the coarse scheme of an open substack, which is generally not finite over the original stack. The latter is needed to meet the former's base hypothesis.

lem-sfb-dm-open-finite-etale-permanence vs lem-sfb-unpointed-stable-coarse-projective: the existing node asserts smoothness/DM/projective coarse moduli for stable curves; the new node is the general representable-map and open-substack permanence theorem, not a theorem about stable curves.

lem-sfb-dm-open-finite-etale-permanence vs lem-sfb-stable-and-smooth-family-open-loci: the existing node constructs particular open loci of families, not preservation of smoothness, finite type, finite diagonal and the stack condition for arbitrary finite-etale decorations.

lem-sfb-dm-open-finite-etale-permanence vs lem-sfb-smooth-curve-abelian-level-rigidification: the existing node is the parent curve-level theorem and depends on this item; the new node has no curve, genus, cohomology, frame, coarse-space or representability-by-a-scheme conclusion.

Whole-DAG statement/key-word searches and blueprint_refs.py searches for coarse moduli, open substack, and finite etale were read before creation. The broad finite-etale blueprint search finds scheme-cover results, not either new stack theorem. The ancestor command reports blueprint.from.node = None for this chain, which is retained, along with the complete inherited via list. Source-tag searches found precisely the two shared-0DUT pairs listed above; the permanence tags have no existing node.

## Review by ND

I read the item, its definition of level groupoids, the chapter and unit, both new node statements, every statement cited by each proof step, and delivery-errors B–E in full (including the duplicate historical copy). The original item is the coarse theorem of Pikaart–de Jong with the exact full frame convention of 2.3.3, not a symplectic-level convention, a pointed curve, or a level compactification. The proof is marked agent-written because it assembles a different sequence of general lemmas and its source PDF is not local.

For the first new node I read stacks-more-morphisms.tex, theorem-keel-mori (0DUT) and lemma-etale-separated-over-keel-mori (0DUV), including the displayed cartesian square and the automorphism-isomorphism hypothesis. An open substack is full and therefore preserves stabilizers. The coarse map is a universal homeomorphism; its corresponding open and flat localization give exactly the claimed coarse universal property. The node requires finite diagonal, hence finite inertia, and makes no false assertion about nonflat base change.

For the second new node I read stacks-morphisms.tex, lemma-composition-finite-type (06FT), lemma-composition-smooth (075V), lemma-open-immersion-etale (0CIP), and lemma-locally-closed-in-noetherian (0CPM), and algebraic.tex, lemma-open-fibred-category-is-algebraic (05UN) and lemma-representable-morphism-to-algebraic (05UM). Its chart hypothesis supplies representability on all schemes, so the fibred category really satisfies effective descent. Pulling back an etale atlas gives a scheme atlas of the decoration. Open substacks of the finite-type stack over a field are quasi-compact by Noetherianity; finite morphisms are quasi-compact, so finite type is global. For finite-etale decorations the relative diagonal is open and closed, hence finite; composing with the base-changed finite diagonal proves finite diagonal. These are genuine general permanence inputs, left as statement-only nodes rather than hidden inside the item.

Step 1 uses exactly the smooth/DM/open assertions of unpointed-stable-coarse-projective, the finite-type/finite-diagonal assertions of stable-isom-finite-unramified, and open permanence. The first cited node alone does not assert finite type or separatedness of the stack; this is why the second is explicitly cited.

Step 2 uses projective-bundle-proper for precisely the projectivity convention in the groupoid definition, smooth-proper-finite-cohomology-local-system for q=1 and F the constant rank-one finite module, and prime-proper-base-change for the actual exchange isomorphism under arbitrary base change. Smoothness, properness and invertibility of the prime are present, and no Noetherian-base premise is added.

Step 3 uses flc-representable for exactly its second clause and inverse-image-representable for arbitrary base change of a represented etale sheaf. Trivializing the finite module sheaf makes its frame sheaf a finite constant set, even if empty. The explicit two functors on the 2-fibre product retain the isomorphism alpha; their formula transports lambda by the inverse of alpha-star, and the condition on an arrow forces uniqueness. Thus it proves the scheme-chart hypothesis on all T-schemes and does not confuse equality of coarse points with an actual isomorphism.

Step 4 applies just the second new node to those charts. This establishes all stack properties independently of the later scheme claim.

Step 5 cancels the frame to obtain identity on H^1, then invokes precisely the statement of geometric-curve-level-faithfulness. All its genus, projectivity, smoothness, algebraic-closure and prime-to-characteristic premises are verified on the geometric fibre. It does not infer trivial inertia on nonreduced schemes from geometric point sets without a DM theorem.

Step 6 uses the stable coarse scheme, stable finite diagonal/type, the new open-restriction theorem, and inertia-free-finite-cover-coarse. The latter's input is the smooth open stack with its own coarse scheme V; the level cover is not claimed finite over the stable compactification. Its conclusion explicitly supplies scheme representability of the level stack, including in wild characteristic. No parent-node or normalization cycle is introduced.

Step 7 is elementary: the equivalence to a represented discrete groupoid has the coarse universal property by composition, and gives the geometric bijection. The identity atlas of the representing scheme translates step 4 to the scheme's smoothness, finite type and separatedness. This does not transfer properties along an arbitrary coarse morphism; the morphism here is an equivalence.

Small cases checked: empty open and empty frame sheaf; nonreduced test schemes; characteristic 2 with level prime 3; genus 2 with the hyperelliptic involution (its -1 action is nontrivial at odd level); disconnected fields of definition or multiple level components. The two general new inputs require no tameness or characteristic-zero assumption. The prohibited cases g=0,1 or level 2 are never fed to curve faithfulness. Each new node introduces its own objects and inline meanings of open/finite diagonal, carries no proof and has exactly the search outputs actually obtained. LeanFinder and LeanSearch used distinct phrasings, and Loogle plus source grep had no matches. The hits are scheme-level restriction/morphism results and ordinary functor representability, not a one-line theorem about DM stacks. All proof steps have fewer than 2000 characters. No Lean, compiler, git command, launcher edit, repository write, or subagent was used.

## Unfinished work

The two new inputs are intentionally unsplit as required for one-level stage 1. No other mathematical work is deferred in this item's argument. Server dry run and push are the final required checks.
