# Stage-1 report: lem-sfb-deformation-marked-lift-torsor

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-deformation-marked-lift-torsor.json: statement, split following Stacks Tags 06JI–06JJ, unchanged statement; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-rs-marked-lift-pullback-bijections.json: statement-only supporting lemma, unsplit; no Mathlib match. It states the general marked-lift restriction bijections of Tag 06JH, with no small-extension hypothesis, tangent space or torsor conclusion.
- citations.json: one verbatim statement quotation for each step/node citation.

## Attachments

None. Searches in lean/WeilConjectures by the blueprint tag, Schlessinger and marked-lift terminology found no declaration of the item or supporting lemma. The item has no upstream Lean attachment/audit indicating a completed proof.

## WANTED

None. All proofs and statements used here are available in literature/stacks-project/formal-defos.tex.

## What was wrong or incomplete

The item was statement-only. Its statement is correct, including the marking condition, so it is preserved. In particular the kernel is allowed arbitrary finite dimension, not just one. The inherited blueprint ancestor command returns None; the item's existing from.node=null and its detailed alteration/deformation provenance are retained, and the new node carries the same ancestry with this item prepended to via. The current blueprint was read in literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/: its direct-images proof (3) is the parent route. This generic deformation calculation supports that recorded route below its units; it does not change any unit step.

The Stacks lift definition is read with the correctly typed marking equation alpha' composed with f_*u equals alpha, as already written in the item. No inference here uses unmarked object classes as a replacement for marked lifts over A. Only over k does contractibility justify forgetting the marking.

## What remains

The new Tag 06JH supporting lemma remains statement-only for a later stage-1 worker. There is no unresolved part of the present split. No Lean file was written and no build or compiler was run.

## Not duplicates

lem-sfb-rs-marked-lift-pullback-bijections vs lem-sfb-deformation-marked-lift-torsor: the former concerns restriction of marked lift classes in any surjective fibre square; the latter constructs an additive tangent action for a small-kernel extension and proves equivariance. The supporting node has neither a tangent space nor a group action.

lem-sfb-rs-marked-lift-pullback-bijections vs lem-sfb-ring-deformation-smoothness-test: the latter is a smoothness criterion for flat algebra deformation groupoids from tangent surjectivity and existence of lifts; it does not state the general marked (RS) pullback bijections.

Searches of the whole DAG by Tag 06JH, remark-lift-bijections, marked lifts and (RS), followed by reading matching statements, found no existing node stating the new lemma. The blueprint searches "torsor", "marked lifts", and "lift bijections" produced no equivalent blueprint statement (the torsor search found other geometric torsors). The new node's same_as is therefore empty. The nearest ancestor query returned None, agreeing with the existing item's from.node.

## Mathlib searches read

All searches were run through the required msearch.py command and are recorded exactly in searches.jsonl and the node records. Two semantic phrasings were used for each mathematical question. The item searches find derivationToSquareZeroEquivLift and cotangent modules. The former, read at Mathlib/RingTheory/Derivation/ToSquareZero.lean:116, classifies lifts of a fixed ring map relative to a scalar tower, not marked objects of an arbitrary (RS) groupoid. It does not prove the item by specialization.

For the supporting lemma, PreGaloisCategory.fiberPullbackEquiv (Mathlib/CategoryTheory/Galois/Basic.lean:258) has a finite-set-valued fibre functor as hypothesis. It does not handle a groupoid pseudofunctor or markings. CategoricalPullback.functorEquiv (Mathlib/CategoryTheory/Limits/Shapes/Pullback/Categorical/Basic.lean:354) is an equivalence on functor categories, and Pseudofunctor.DescentData.pullFunctorEquivalence (Mathlib/CategoryTheory/Sites/Descent/DescentData.lean:373) changes a descent presentation. I read these declarations and their surrounding documentation. Neither states the two marked-fibre bijections or specializes to them in one line. The grep searches for markedLift, marked_lift, Schlessinger and lift-bijections gave no hits. All services answered; no unavailable result was represented as absence.

## Review by Q156

I read formal-defos.tex definition-lifts, remark-tangent-space-lifting (06JG), remark-lift-bijections (06JH), lemma-free-transitive-action (06JI) and remark-free-transitive-action-functorial (06JJ), together with the tangent-space tensor and morphism lemmas. The new node is exactly the two general comparisons in 06JH, including naturality of restriction. It has no proof or hidden proof sketch in its statement. The item's proof follows the difference-map construction in 06JI, with the action argument and the functorial calculation written out rather than hidden in that new node.

For step 1 I opened def-sfb-artin-deformation-test-category and lem-sfb-artin-rs-tangent-tensor. The definition supplies k[V], (RS), and the contractible fibre condition. The tensor lemma supplies the finite-dimensional square-zero identification and its compatibility with linear maps; no finite-dimensionality of the tangent space is assumed. I verified finite-dimensionality of I separately using the descending chain condition on its subspace ideals, rather than assuming every Artinian ring has the needed property without argument. I checked the fibre rings stay local Artinian with residue k by the ideal-chain argument. Forgetting a marking over k is valid because there is a unique arrow between any two objects there.

For step 2 I checked the new node's fixed-lift clause against each use: the first square is A' -> A <- A', and the second is A' -> k <- k[I]. In each case both displayed maps to the base are surjective. I verified the difference ring map by multiplication, including the vanishing product of two kernel elements, and wrote its inverse. The comparisons are between lifts marked to a fixed representative z, so their naturality under marked isomorphisms is precisely what makes delta_z depend only on the marked class. This is a general fibre-square input, strictly smaller than the torsor result.

For step 3 I checked the new node's first bijection glues a triple of marked lifts, and that the repeated fibre-product projection remains surjective. The two pairwise differences are the two coordinates of h. Their sum is the third difference by a literal equality of ring maps. I opened the tangent-tensor statement and verified it explicitly states the compatibility with every linear map, hence covers coordinate projections and the sum map. This gives the cocycle identity without a new cocycle lemma. Step 4 then uses only bijectivity of delta_z and cancellation in an additive group; it spells out both action identities and unique translation parameters.

For step 5 I checked the supporting node actually states naturality under pseudofunctor morphisms, not just base-object isomorphisms. Coherent transport squares commute after taking isomorphism classes. The tensor map is identified by a basis of I, not a basis of the potentially infinite-dimensional tangent space. The zero-dimensional case uses the singleton value at k. I also wrote why dH is linear: it commutes with the maps defining addition and scalar multiplication, so the tensor expression is well typed. The final equivariance follows by uniqueness of the translation parameter. Each cited node was opened and its relevant statement was copied verbatim into citations.json. During this check I corrected the source tag for lemma-morphism-tangent-spaces to 06ID and refreshed the quote of the live deformation-category definition after it gained explicit definition references.

Small cases checked: I=0 gives A'=A and a singleton marked lift set, with zero acting identically; A=k gives exactly the square-zero tangent-vector translation; the terminal constant deformation groupoid gives a singleton and zero tangent space; nontrivial automorphisms over A' do not spoil the argument, because the fixed-lift bijections take marked isomorphism classes. An empty lift set triggers no torsor assertion. The induced map H need not be faithful, injective or surjective: naturality and uniqueness on the target are sufficient. I checked the B–E delivery criteria: self-contained statements, correct tags and typing, no duplicate, no use of a cited proof instead of its statement, no missing non-elementary comparison, no relabelling of the item into a new node, and no hidden long-step lemma. Every proof step is under 2000 characters.
