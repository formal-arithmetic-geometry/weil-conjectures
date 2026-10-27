# Stage-1 delivery: lem-sfb-smooth-model-reductive-neutral-lift

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-model-reductive-neutral-lift.json`: the item, split into six steps; mathematical statement unchanged; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-reductive-torus-fibre-openness.json`: new statement-only generic openness theorem, Conrad Proposition 3.1.9(1),(2), with (2) restricted to split tori; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-split-torus-etale-subgroup-lift.json`: new statement-only lifting theorem for a split torus subgroup, over an arbitrary affine base at a point with algebraically closed residue field; no Mathlib match.
- `citations.json`: one verbatim statement excerpt for every node used by every proof step.
- `searches.jsonl`: unmodified command-generated search log. `write_split.py` is a sandbox-only preparation script; it is not a library or launcher modification.

## Attachments

None. I searched the live project's WeilConjectures tree for the blueprint tag and for neutral, reductive, identityComponent, and the proposed subgroup-lifting notions. The existing field-valued identity-component and Hopf-ideal declarations do not provide this relative DVR-model theorem. No exact finished project declaration was found. No Lean file was written and no compiler, Lake, or build tool was run.

## WANTED

WANTED: Gopal Prasad and Jiu-Kang Yu, *On quasi-reductive group schemes*, https://arxiv.org/pdf/math/0405381, locally as `literature/prasad-yu-on-quasi-reductive-group-schemes.pdf`, Lemma 3.5, Section 3.6 and Proposition 4.3 first paragraph, printed pp.6-8, for lem-sfb-smooth-model-reductive-neutral-lift. I read these places online; the paper is absent from the local literature directory.

WANTED: Brian Conrad, *Reductive group schemes* (2014), https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, locally as `literature/conrad-reductive-group-schemes.pdf`, Proposition 3.1.9(1),(2), printed pp.85-88, for lem-sfb-reductive-torus-fibre-openness; Proposition 3.1.6, printed pp.83-84, and Proposition B.3.4, printed pp.290-292, for lem-sfb-split-torus-etale-subgroup-lift. I read the statements and relevant proofs online. This is Conrad's independently developed exposition, not an SGA source. No SGA volume is used as a source in this delivery.

These requests are reported here because the repository and its literature list are read-only. Accordingly the item's proof_origin is agent, with the source places named, rather than document.

## What needed repair in the imported item

The item was statement-only, without a proof. Its reference indicates the right Prasad--Yu neutral-component argument, but an open subscheme of an affine scheme need not be affine, and reductivity of one fibre alone cannot be treated as the definition of a reductive group scheme. The split supplies an actual affine-coordinate calculation and states the separate generic openness input. It also proves the existence and fibrewise maximality of the split torus rather than merely writing that a strictly henselian reductive group is split.

There is no statement dispute, no added hypothesis, no residue-characteristic restriction and no route change. In particular, the proof does not invoke the parent quasi-reductive special-connectedness theorem or Proposition 4.3 as an opaque replacement for the item. Those would obscure the reason the parent can use this lemma.

## Not duplicates

lem-sfb-reductive-torus-fibre-openness vs lem-sfb-smooth-model-reductive-neutral-lift: the new theorem is about open loci on an arbitrary base for a given smooth affine group and a given split torus. It neither constructs a neutral open nor proves its affineness, lifts a torus, or asserts splitting over a henselian ring.

lem-sfb-split-torus-etale-subgroup-lift vs lem-sfb-smooth-model-reductive-neutral-lift: the new theorem lifts an arbitrary specified split torus subgroup of a fibre, without assuming reductivity, connectedness or henselianity; it neither constructs the neutral component nor asserts that the lifted torus is maximal.

lem-sfb-reductive-torus-fibre-openness vs lem-sfb-split-torus-etale-subgroup-lift: the former concerns persistence for already existing objects; the latter constructs an embedding on an etale neighborhood and supplies no maximality conclusion.

lem-sfb-split-torus-etale-subgroup-lift vs lem-sfb-split-torus-subgroups-diagonalizable: the existing theorem classifies closed subgroups of a split torus over an algebraically closed field. The new theorem deforms an embedding of a torus into a smooth affine group over a relative base.

lem-sfb-split-torus-etale-subgroup-lift vs lem-sfb-etale-nil-ideal-map-lift: the existing theorem concerns a ring map across a nil ideal, not multiplicative torus subgroup embeddings at a residue-field fibre.

lem-sfb-reductive-torus-fibre-openness vs lem-sfb-locally-algebraic-group-identity-component: the existing theorem supplies the identity subgroup and its smooth reduction over a field; it does not make reductivity or maximality persist across a base.

Before writing either node I searched all DAG statements (not just the item's ancestry) for relative torus lifting, multiplicative type, reductive loci, and maximal tori over henselian bases; searched by the Conrad proposition numbers; ran blueprint_refs searches for reductive, torus, multiplicative type, and reductive fibre; and searched the project Lean source. The blueprint searches returned zero matching imported nodes. The field-theory nodes and the original item are the nearest candidates, and are distinguished above. No new Stacks-tagged node is created, so there are no same-Stacks-tag pairs to reconcile.

## Mathlib searches read

For each new node the actual msearch.py results contain LeanFinder in two phrasings, LeanSearch, Loogle, and source grep. For openness, the semantic hits were smooth/etale/unramified loci, affine neighborhood reduction and generic open immersions. These concern different predicates and cannot specialize to reductivity or maximal tori. For lifting, the hits were residue-field ring-map lifts, standard etale presentations, affine transition limits and abstract Galois-category lifting. None asserts that a subgroup morphism remains multiplicative or a closed immersion. The broad torus grep matched substrings in functoriality and toRingHom; a second grep with word boundaries returned zero. I retained both actual searches and described the false positives. The new nodes remain unsplit; no candidate is marked a Mathlib leaf. The item was also searched with this group's commands, in addition to retaining its inherited searches. All recorded queries are exactly those in the command log, and none of the executed services reported unavailable.

## Review by Q13

I read Prasad--Yu's neutral-component paragraph, Lemma 3.5 including its alternative dilatation explanation, Section 3.6 and the first paragraph of Proposition 4.3. I also read Conrad's Proposition 3.1.6 and its Artin-approximation proof, the statement and proof of Proposition 3.1.9, and Proposition B.3.4's etale-splitting assertion. The two new nodes expose the genuine general deformation/openness inputs used below the blueprint route; they do not package this item's conclusion. For local tools I read Stacks groupoids.tex proposition-connected-component (0B7R), algebra.tex lemma-disjoint-decomposition (00EE), algebra.tex lemma-smooth-syntomic (00TA), more-algebra.tex lemma-lift-smooth-henselian (0H74), and the basic-open and smooth-open/composition source places (01I3, 01VC, 01VA). I opened and read the statement of every node actually cited in the six steps.

Step 1 uses lem-sfb-finite-type-group-identity-subgroup for precisely the clopen subgroup structure of H, with its finite-type-over-a-field hypothesis satisfied by the special fibre. The open-immersion definition gives factorization through an open when the topological image lies there. This is safe here because the target is an open subscheme; no analogous factorization through a closed subscheme is asserted. The generic and special restrictions of the group maps put their images in the chosen open and the diagrams are inherited. The two fibres are equal as open subschemes, not merely equal sets.

Step 2 uses the affine smooth comparison for the smooth R-algebra E, the smooth-ring-map-flat theorem for its flatness, and the flat-module-torsionfree theorem over the domain R. These statements really provide the injection into E[1/pi]; it is not smuggled in from a definition of smoothness. The clopen-idempotent theorem is applied to the complement of H, so H is V(a-bar), with the correct sign. No idempotent lift in E is assumed: only a-bar is idempotent and a(1-a)=pi b is all that is used.

Step 3 uses the basic-open localization statement for the actual structure sheaves. The equalities B_pi=E_pi and B_(1-a)=E_(1-a) are proved by the displayed fractions, with injectivity supplied by Step 2. The identity 1=(1-a)+pi t proves the two charts cover Spec B. Their overlaps are the same localization inside E[1/pi,1/(1-a)], so the chart identifications give precisely the required open immersion and affineness. This is a short explicit localization calculation, marked elementary, not an uncited general affineness theorem. Adjoining t to the already finitely generated E proves finite type. It is not inferred merely because an open lies in a finite-type scheme.

Step 4 uses the open-immersion/smooth-composition statement to retain smoothness. The new openness theorem is applied to an affine smooth group of finite presentation: affineness is Step 3, and the affine smooth comparison supplies finite presentation. The special identity component is the specified reductive H. Openness at the closed point of Spec R gives the entire base, by the explicit unit argument. The generic fibre is geometrically connected by the original hypothesis and the special fibre is the connected H, so reductivity of their neutral components is reductivity of the full geometric fibres. I do not assume connectedness or reductivity for any missing fibre.

Step 5 takes existence of a split maximal torus from the actual statement of lem-sfb-reductive-borel-pair-structure. It applies over the algebraically closed field F to the reductive H, so neither the characteristic-zero comparison lemmas nor their stronger coefficient assumptions are involved. The new lift theorem gives an affine etale neighborhood with an F-point and a closed split torus embedding there. Its proof source lifts the multiplicative-type subgroup and then makes it split etale locally; since F is algebraically closed a point over the chosen special point has the same residue field, and the torus rank is r. I used the existing smooth-affine comparison and 0H74 lifting with S=C, target A=R and I=(pi), not with an arbitrary higher ideal. Etaleness implies smoothness as explicitly included in def-sbc-smooth-morphisms. The resulting map C to R is over R and lifts the specified residue map, hence is the required section through u. Pullback of the closed immersion is justified by tensoring a surjective coordinate-ring map; its special fibre is the chosen T_0.

Step 6 uses only the maximality part of the new openness theorem, under its verified reductive special-fibre hypothesis and the chosen maximal T_0. It promotes maximality on that fibre to all of the local base. Thus the constructed split torus is maximal in every geometric fibre, exactly as the item's definition requires.

I tested the statements on the trivial group and r=0, on a split torus, and on a split semisimple group in arbitrary characteristic. The torus-lifting statement also works for the trivial subgroup of G_a, which is allowed because no reductivity or maximality conclusion is built into it. For the affine charts, a-bar=0 permits a=0 and returns B=E; a-bar=1 gives the generic open and B=E[1/pi]. The latter cannot describe the identity component in this item but tests the algebraic sign and chart construction. I also checked that a lift a need not itself be idempotent; the relation with b is sufficient. No smoothness or dimension inference relies on excluding characteristic 2. The only two points of Spec R are its generic and closed points, and geometric generic connectedness is explicitly present in the item. No step exceeds 2000 characters.

The current latest blueprint is main-20261024. I read the chapter and unit records and the latest sk-thm-sf-ctf-stability section and direct-images proof (3). The inherited extended place records this prerequisite beneath that route. blueprint_refs.py ancestor reports a null imported root for this created-node chain; the new nodes preserve that value and prepend the item to its via list. I did not alter the unit or chapter. The off-unit citations declared in split_report.tool_uses are only generic algebra and scheme tools, not alternate proof routes. I checked that the Borel-pair citation has no dependency path back to this item, so it does not make the parent's use circular.

## Unfinished work and validation

Nothing remains unfinished in this one-level split. The two new nodes are intentionally statement-only and join the stage-1 queue; there are zero new Mathlib leaves. Both server checks have passed: review_split reports PASS, and check_dag reports no finding introduced by the sandbox or on its nodes. The required full delivery dry run and push follow this report.
