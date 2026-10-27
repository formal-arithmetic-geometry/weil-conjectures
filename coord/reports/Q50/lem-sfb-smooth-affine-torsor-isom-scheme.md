## Worker report

Item: lem-sfb-smooth-affine-torsor-isom-scheme. Group Q50. Stage 1 only, 2026-10-24.

### Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-affine-torsor-isom-scheme.json: seven-step split, using existing nodes throughout. The mathematical statement is retained verbatim; the fibre-product definition is added to its statement dependencies.
- citations.json: 23 step/node pairs, each quoting the cited statement verbatim.
- report.md and searches.jsonl: this reading and the actual search records.

New nodes: none. New Mathlib leaves: none. There was no previous sandbox split or report to retain.

### Attachments

None. The project search under lean/WeilConjectures found no blueprint-tag declaration and no theorem giving this whole arbitrary-group-scheme Isom statement. EtaleTorsor.lean concerns finite constant groups and does not attach this node. The already recorded project declaration for lem-pc-proper-base-change is used only through that existing node's independent smooth-base-change clause.

### Literature and searches

I read Stacks examples.tex Tag 04AG, section-not-algebraic-stack, specifically the paragraph identifying the affine diagonal with Isom(P_1,P_2). That paragraph assumes a field and does not itself supply all of this item's generality. I therefore mark the proof agent-written: it spells out the arbitrary-base construction, including the transition and descent equations. Its inputs are the local Stacks texts descent.tex Tag 0245 (lemma-affine), 023Q (lemma-fpqc-universal-effective-epimorphisms), 02L5 (lemma-descending-property-affine), 02VL (lemma-descending-property-smooth); topologies.tex 022B (definition-fpqc-covering), 022D (lemma-fpqc); morphisms.tex 01SD (lemma-base-change-affine), 01VB (lemma-base-change-smooth); categories.tex 001P (lemma-yoneda). No SGA source is used.

No WANTED input is required for this proof. The author-hosted Iwahori paper mentioned as WANTED in the item's inherited source is not present locally and is not used: smoothness follows from the available Stacks base-change and descent statements. Its inherited source metadata is retained.

The item's existing search records are preserved. Five new msearch calls are logged: LeanFinder with the whole Isom representability statement, LeanSearch with the principal-bundle formulation, Loogle with torsor and Isom, and two Mathlib greps, over AlgebraicGeometry and GroupScheme. Both semantic services answered. The Loogle result is a normed additive-torsor instance. LeanFinder gives affine-space and affine-property results. LeanSearch gives generic representability transport and Scheme.LocalRepresentability.isRepresentable. I opened that module: its hypotheses require relatively representable open immersions and Zariski local surjectivity, which are not this fpqc trivialization problem. The generic Yoneda lemmas transport an already supplied representing object and do not construct this one. Neither grep found a scheme-torsor Isom declaration. None is a one-line match.

The DAG was searched for fpqc affine effectivity, affine and smooth descent, morphism descent, covering axioms and Yoneda, and every reused statement was opened. Blueprint searches included torsor, Isom, affine descent and smooth fpqc. The latest blueprint unit and its direct-images proof were read at literature/blueprint/latest/ (main-20261024). No imported blueprint node supplies this item directly. The ancestor command returns null, as in the live item's blueprint.from.node; the existing detailed supporting-place and via chain are retained. This continues the supplied prerequisite route before infinitesimal lifting and changes no unit or chapter.

### Faults found and changes

The item had no proof. Its assertion is correct as stated. It needs no commutativity, constant relative dimension, field hypothesis, properness, Noetherianity or global triviality. An important pitfall would have been to call Isom(P,Q) an H-torsor for the untwisted group when H is noncommutative; the proof instead descends H by the explicit double-translation cocycle. I also avoid using effective affine descent as though its statement already promised an affine descended morphism: affineness is separately reflected using the existing 02L5 node.

Nothing remains unfinished in this one-level split; existing non-leaf inputs remain the project's existing obligations.

## Review by Q50

I checked delivery-errors B through E with the item, its cited statements and the Stacks passages open. There are no new statements requiring separate definition dependencies, searches or duplicate comparisons. The item retains all its hypotheses and clauses, and its extra fibre-product statement dependency supplies a notion it was already using.

Step 1 uses the actual represented-right-torsor definition: it explicitly includes flatness, surjectivity and quasi-compactness in finite presentation, and gives the torsor isomorphism used later. The fpqc definition requires finite affine subcovers over each affine open; the text supplies them rather than assuming that a surjective flat map alone is fpqc. The covering-axioms statement gives precisely base change and composition. The qcqs-permanence statement gives base-change preservation of quasi-compactness and quasi-compactness of a source above a quasi-compact target, exactly what establishes quasi-compactness of U over Y. The fibre-product statement provides U and its projections. No global qcqs assumption on Y is introduced.

Step 2 uses the cartesian torsor square stated in the right-torsor definition, not any theorem hidden in its proof. Pulling that isomorphism along the section p gives the map h to ph and its inverse. Evaluating an equivariant morphism at p gives c, and the inverse formula is written. This is elementary from the group diagrams and the two trivializations, and is stated as a scheme-morphism calculation on every test scheme, not only on geometric points.

Step 3 uses those same division isomorphisms and fibre products to construct a and b as morphisms. I checked the right-action order: p_1=p_0 a_01 and q_1=q_0 b_01 give c_1=b_01^{-1}c_0 a_01. On triples the products are a_02=a_01 a_12 and b_02=b_01 b_12, so the two transition maps compose in exactly the order required by the effectivity node. The inverse and cocycle are explicit; there is no unproved comparison lemma in this elementary step.

Step 4 cites affine-morphism permanence for base-change affineness of H_U and the singleton version of 0245 for effectivity. I opened the latter statement: it gives a model and an isomorphism respecting the specified descent datum, which is exactly what is used. The cover is the singleton U to Y, so there is no need for a family/coproduct conversion. Affineness of the descended map is deliberately proved in the next step.

Step 5 cites independent clause (2) of lem-pc-proper-base-change, whose statement assumes only smoothness for that clause. This is why the lack of properness of H is harmless. The 02L5 statement reflects affineness along an fpqc family and applies to our singleton. The smooth-descent statement assumes flat, quasi-compact, surjective base change, all supplied by step 1; it imposes no field, dimension or finite-presentation hypothesis on that cover. Affine-morphism permanence also explicitly gives affineness of the source over an affine target. Thus the stronger absolute assertion is made only when Y is affine.

Step 6 uses representable fpqc descent exactly as stated: compatible morphisms into a fixed scheme descend uniquely. Apply it first to maps into I, then to the local maps on P_T into Q_T and their inverses on Q_T into P_T. The covering-axioms statement supplies each pullback cover, including that on P_T times_T H_T. The identities, structure-map equations and equivariance descend because they are equalities of maps into fixed schemes and uniqueness detects them. This proves naturality as well as bijectivity; it does not cite Yoneda full faithfulness as though it were the more general Yoneda evaluation theorem.

Step 7 uses the fibre-product universal property for both Hom sets and all three pulled-back objects. The same original smooth affine group H over S can be used with the new S-scheme Y', so applying the construction introduces no new group hypothesis. The torsor property persists: covers base change by 022D, finite presentation by the qcqs-permanence node, and the cartesian action square by fibre-product identities. Yoneda full faithfulness is used only for natural transformations between two representable functors; its actual statement gives that bijection, and applying it to both inverse transformations makes the canonical map an isomorphism. The section clause is direct evaluation of the already proved representing bijection at Y.

The off-unit general tools are declared in split_report.tool_uses: affine effectivity, affine-property descent, and the independent smooth-base-change clause. They supply scheme-descent machinery for the unit's existing geometric input; no unit route is replaced. Other off-unit citations are definition nodes or Mathlib leaves.

I tested Y empty (the cover and all represented objects are empty over it), the trivial group (I is Y, even when Y is not affine), trivial torsors for a noncommutative group (the order-sensitive transition above), and a pair of torsors without a global isomorphism (local nonemptiness does not assert a section). I also checked an arbitrary nonflat Y' to Y: the argument uses base change of the cover and the fibre-product universal property, never flatness of Y' to Y. No statement dispute or correction was necessary. All seven proof steps are below 2000 characters, and none conceals a new non-elementary lemma: the substantive effectivity, descent and Yoneda facts are existing cited nodes.
