# Stage-1 report: lem-sfb-cm-closed-fibre-regular-slice

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-cm-closed-fibre-regular-slice.json: item, split by uniform strong induction on the dimension of the fibre local ring. No Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-regular-immersion-composition.json: new statement-only node, composition of regular immersions for arbitrary schemes. No Mathlib match.
- citations.json: one verbatim statement quotation for each node citation of each numbered proof step.
- report.md: this report. The search command maintains searches.jsonl.

One new node, zero Mathlib leaves. No Lean files, compilers or builds used. Only the sandbox is written.

## Attachments

None for the item. Searches in lean/WeilConjectures found no blueprint tag or declaration giving the CM slice with all its regularity and singleton-fibre clauses. Slicing.lean is a smooth/etale construction with stronger hypotheses, and the CM flat quasi-finite chart declarations do not give this slice.

AlgebraicGeometry.IsRegularImmersion.comp (lean/WeilConjectures/AlgebraicGeometry/Morphisms/RegularImmersion.lean, line 532) is related source material for the new node, not an attachment: its class requires a globally closed immersion and fixed codimension, with equations imposed at every ambient point. The new node permits general immersions, open inclusions, and varying local sequence lengths. The theorem's proof is useful evidence for the concatenation argument, but is not its full statement.

## WANTED

None. The needed Stacks .tex sources and current blueprint are available.

## Corrections and scope

The statement is retained. In particular the global base need not be Noetherian, and the empty regular sequence is allowed. The existing weaker slice lem-trf-cm-closed-point-flat-quasifinite-slice deliberately forgets regularity, so applying it would not prove this item. Likewise lem-trf-cm-fibre-hypersurface-dimension-drop gives a principal cut with the required actual fibre local ring and flatness but does not say its equation is regular in the ambient ring. Step 5 explicitly recovers that missing assertion by the existing specified fibre-sequence neighbourhood theorem. No new node duplicates the weaker cut or slice.

The latest blueprint direct-image proof, literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, now expresses the upper constructibility argument by compactification. This item is a generic geometric prerequisite below the retained historical alteration/groupoid route recorded in its blueprint.from.place. Its Stacks proof does not replace a unit step. The existing blueprint.from.node is null; the prescribed ancestor tool also prints None. I preserve that binding and give an exact proof place for the new input through this item. Searches of all imported blueprint nodes for slice, Cohen, regular slice, regular immersion(s), regular sequences, composition of regular, 067Q and 063W found no equivalent general composition or CM slicing node.

## Not duplicates

lem-sfb-regular-immersion-composition vs lem-per-regular-lci-geometric-calculus: the latter explicitly asserts its calculus only for Noetherian schemes and regular closed immersions with codimension data; the new node applies to arbitrary schemes and general regular immersions, including open immersions. The item's arbitrary base does not imply its ambient schemes are Noetherian.
lem-sfb-regular-immersion-composition vs def-per-regular-closed-immersion-codimension: the latter defines a regular closed immersion with a codimension function; it contains no composition theorem and excludes general nonclosed immersions.
lem-sfb-regular-immersion-composition vs def-per-stalk-regular-closed-immersion: the latter defines a stalkwise condition for closed immersions, identifies it with regularity only on Noetherian schemes, and contains no composition theorem.

lem-sfb-regular-immersion-composition vs def-sfb-relative-finite-hilbert-groupoids: the latter defines relative Hilbert groupoids and an lci subcategory for finite locally free maps; it does not assert composition of regular immersions of arbitrary schemes.
lem-sfb-regular-immersion-composition vs lem-pur-smooth-pair-regular-immersion: the latter proves regularity of one closed immersion between schemes smooth over a common base; neither smoothness hypothesis is available here, and it states no composition law.
lem-sfb-regular-immersion-composition vs sk-def-purity-conv: the latter fixes coefficient and purity conventions and defines regularity for closed immersions, without a general composition theorem.
lem-sfb-regular-immersion-composition vs lem-pur-smooth-pair-local-coordinates: the latter constructs etale coordinate charts for a closed immersion between smooth schemes over a common base, without a composition theorem for arbitrary regular immersions.
lem-sfb-regular-immersion-composition vs lem-pur-noetherian-etale-section-specialization: the latter proves a normalized derived specialization comparison for smooth sections over Noetherian schemes, not a composition law for arbitrary regular immersions.
lem-sfb-regular-immersion-composition vs cor-amb-affine-space-adjunction: the latter is an adjunction for etale compact supports of affine space over a Noetherian base; its statement contains no immersion-composition assertion.
lem-sfb-regular-immersion-composition vs thm-amb-etale-exceptional-adjoint: the latter is existence of an ordinary etale exceptional adjoint for a compactifiable map between Noetherian schemes; its statement contains no regular-immersion composition.
lem-sfb-regular-immersion-composition vs lem-pur-smooth-codimension-one-cartier: the latter proves one equation generates a codimension-one smooth closed pair over a field; it has additional hypotheses and no composition assertion.

## Review by Q46

I read the full statement and proof of Stacks Tag 0570 (more-morphisms.tex, lemma-slice-CM), the preceding Tags 056Y (lemma-slice-given-element), 056Z (lemma-slice-once), and 06LI (lemma-slice-given-elements), and Tag 063W (divisors.tex, lemma-fibre-quasi-regular). For the new composition node I read Tag 067Q (lemma-composition-regular-immersion), assertion (1), and Tags 063G (lemma-regular-ideal-sheaf-scheme) and 063J (definition-regular-immersion). The new node records only a statement, no inline proof or proof dependencies. The source of composition uses concatenation of regular equations and makes no Noetherian assumption. Merely citing the existing Noetherian geometric calculus would have introduced a missing hypothesis, so I avoided that citation.

For step 1 I opened lem-weil-pbc-noetherian-local-finite-krull-dimension: it explicitly states finite nonnegative dimension for a Noetherian local ring. The fibre stalk is a nonzero local ring because it is a stalk at a point. The induction assertion is uniform in all scheme and morphism data and requires depth at least dimension, matching the output used later, rather than silently assuming an equality that the cut node does not state.

For step 2 I read the complete statement of lem-trf-zero-dimensional-closed-fibre-open-slice. It gives an open immersion with singleton fibre, local finite presentation and local quasi-finiteness; its conditional flatness applies to our globally flat g. The regularity addition is elementary from the open-immersion and regular-sequence definitions, also read and cited: choose an affine open inside the open image and use the empty list in its nonzero ring. This is not a new lemma or a circular use of the main item.

For step 3 I opened lem-trf-cm-fibre-hypersurface-dimension-drop and checked all its hypotheses: closed fibre point, flat lfp morphism, Noetherian local ring, finite d>0 and depth at least d. Its statement supplies the actual fibre stalk isomorphism and its Noetherianity, dimension d-1 and depth bound; I do not take those from its proof or identify an abstract quotient without its assertion. The section lies in the maximal ideal and its fibre germ is a nonzerodivisor.

For step 4 I read lem-trf-flat-affine-chart-prescribed-germ: it gives precisely a flat finitely presented affine ring map and a section with prescribed germ, on charts inside the current open U. The module-stalk definition gives equality on a neighbourhood for equal germs. The basic-open basis provides the further principal neighbourhood. Localization flatness and the Mathlib-leaf transitivity node justify flatness of the retained algebra; a finite presentation acquires just one variable and relation tq-1 after localization. I added explicit citations for transitivity and equality of germs during self-review, so neither is hidden behind the chart definition.

For step 5 I opened lem-weil-pbc-fibre-product-affine-spectra and lem-weil-pbc-affine-open-stalk-localization, then lem-pur-fiber-regular-sequence-neighbourhood. The first two provide exactly the affine fibre and stalk identifications used. The last requires only a flat finitely presented ring map and a specified list regular at the fibre prime: step 4 supplies that map, and the image of b is the nonzerodivisor in the maximal ideal from step 3. Thus its singleton quotient is nonzero. Its conclusion really gives regularity of the SAME list after a principal localization; no change of generators or Noetherian-base assumption is inferred. Restricting the prior cut to that principal open keeps its fibre point and fibre stalk. Closedness of the point remains true under restriction. The flatness definition uses unchanged stalks; local finite presentation follows by the explicit localization presentation and the definition's affine charts. The entire restricted cut is defined by one regular equation, so regularity is proved everywhere on that cut, not just at the distinguished point.

For step 6 I opened the new composition statement, which explicitly has no Noetherian assumption. Both input regular immersions are available: the principal regular cut from step 5, and the slice supplied by the smaller-dimensional induction assertion. The smaller dimension is a nonnegative integer since d>0; in particular d=1 gives the verified d=0 case. The final structure morphism is exactly the induction morphism, so its three properties and singleton fibre need no morphism-property composition lemma.

For step 7 I read the fibre-product definition and wrote the universal-property comparison by its two projections. This identifies the induced fibre map and proves the required point image, with fibre projections made explicit. No informal identification of a point of Z_s with a point of Z is used without its projection.

I checked delivery-errors B--E: statements introduce all objects and define regular immersion inline with appropriate definition dependencies; source labels and tags were verified in tags/tags; citations use statements, not proofs; proof_deps is exactly the union of uses; new node proof is empty; no split is moved into a renamed clause; dimension induction has a base and a strictly smaller uniform application. All steps are under 2000 characters, and the longer regularity step is one application of an existing lifting statement with its explicit identifications. New-node Mathlib searches are recorded exactly from searches.jsonl, including two semantic phrasings; returned ordinary immersion composition and algebraic concatenation lemmas do not state general scheme regular-immersion composition. The project comp theorem is narrower, as noted above.

I tested d=0, d=1, empty sequences, and non-Noetherian bases. A zero-dimensional nonreduced fibre is allowed: singleton is topological and does not assert a reduced rational point. In positive dimension the nonzerodivisor in the maximal ideal has nonzero quotient, so no empty principal cut can remove the point. For composition, identities and open inclusions use empty lists, empty sources are vacuous, and there is no fixed-codimension or regular-scheme hypothesis. Tool uses from other units are generic geometric/local algebra inputs, explicitly declared in split_report.tool_uses; they do not supply an alternate unit route.

## Unfinished work

No unfinished work on this split. The one new node is intentionally unsplit, as required for a one-level stage-1 delivery. The existing input nodes remain owned by their respective workers. Server review_split and check_dag have passed. The first delivery dry run requested explicit same-tag comparisons for two additional nodes; I opened those statements and added them (and the other definition-tag overlaps) above. The second dry run rejected the phrase "as in the item" in the final step; I removed it and expanded the induction assertion to list its conclusions explicitly. Final delivery preflight is run by the direct-delivery tool.
