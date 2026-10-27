# Stage-1 worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-locally-ringed-etale-topos-reconstruction.json: item, statement, split in nine steps; no Mathlib match.
- lem-sfb-scheme-ringed-etale-reconstruction: new statement-only node; no Mathlib match.
- lem-sfb-ringed-topos-slice-functoriality: new statement-only node; no Mathlib match.
- lem-sfb-space-etale-pullback-chart-comparison: new statement-only node; no Mathlib match.
- lem-sfb-space-etale-conservative-geometric-points: new statement-only node; no Mathlib match.
- citations.json: one verbatim statement quotation for every node used in every step.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, locally ringed topoi, ringed etale reconstruction and AlgebraicSpace. The only broad ringed-topos hits were module pullback prose and etale section reconstruction; neither states this theorem. No compiler, Lean writer or Lake command was used.

## WANTED

None. All sources are in literature/stacks-project.

## Findings and corrections

The item was an unsplit statement with earlier Mathlib searches and a search-only sandbox. I retained its statement, source, provenance, blueprint chain and existing searches. The sandbox had no proof or report, so no completed split was discarded. The source exactly supports the statement over Spec Z. In particular, uniqueness is uniqueness up to ring-compatible two-isomorphism, and rigidity proves that this isomorphism is itself unique.

The original source omits the descent detail and the coordinate embedding compatibility. Steps 5 and 7 supply them explicitly. In the rigidity proof inverse image is not assumed to preserve infinite products: each coordinate map is pulled back individually. This avoids an invalid shortcut for an infinitely generated affine algebra.

I initially bundled existence and composition of space ringed morphisms into the new chart input, then found the existing enlarged-site model, chart normalization, site density and composition/localization nodes. I removed those clauses from the new node and cited the existing ones in the item. Its remaining content is representable/stalk inverse image and the compatibility of relocalization with a general chart square, which those existing statements do not assert. No new node restates a clause of the algebraic-space reconstruction theorem. The scheme theorem is the smaller, independently sourced input used on all chart squares. No generator node is needed: affine coordinates and rigidity are proved in steps 7--8. The auxiliary generator searches remain in the log as research history.

The blueprint ancestor command returns None, matching the existing null from.node and its explicit provenance chain. I retained that chain and filled each supporting place by the exact 04KL/04M6 proof location it serves. I read the current latest blueprint direct-images proof (3); this is a deep foundation prerequisite for that route, not a change to the unit or a key-node realization. No older blueprint snapshot was used as a source.

## Unfinished work

The four new nodes are deliberately unsplit, with statements only and no proof sketches in their statements. They join the queue after delivery. The item itself has a complete assembly proof. No stage 2 or 3 work was undertaken.

## Review by Q33

For the item I read spaces-properties.tex Tags 04KH, 04KJ, 04KK, 04M6 and 04KL, including the full chart and relation construction and the omitted descent paragraph. For the scheme input I read etale-cohomology.tex Tags 04I7, 04IJ, 04LW and the surrounding locality results: these apply to arbitrary schemes, so neither atlas needs to be separated or quasi-compact. For relocalization I read sites-modules.tex Tag 04J8 and all locality clauses of 04IH, and the fibre-product formula used in 04M6. For the chart input I read spaces-properties.tex Tag 04K2, the ringed localization equation and both 04M4/04M5. For points I read 04K5 and its chart proof; the statement uses geometric points of X, correcting the evident S-for-X typo in its abelian-sequence sentence without changing the item.

Step 1 uses the strict-local-flatness node only for nonzero local chart stalks and locality of the induced stalk map, which its statement explicitly gives; no flatness conclusion is used. The new points statement supplies finite-limit/colimit preservation and set-sheaf detection, not merely module exactness. Units are the finite-limit equation ab=1, so the unit square is checked stalkwise without an uncited local-ring-topos criterion. The existing model constructs the ringed morphism and the existing composition node supplies identity and composition coherence.

Step 2 uses exactly the slice statement's locality and natural comparison square, the chart statement's ringed equivalences, and scheme reconstruction plus scheme rigidity. Uniqueness in the scheme input identifies the two composites; its rigidity makes the comparison isomorphisms agree on restrictions. This last point is essential to the descent in step 5.

Step 3 uses the algebraic-space definition to choose atlases and make both relation overlaps schemes. Fibre-product cover stability and chartwise etale permanence supply the covers and their composites. Epimorphisms are kernel-pair coequalizers by the cited statement, so a left adjoint preserves them; the local-surjectivity statement then supplies the local sections of g^{-1}h_V. No finite cover is chosen.

Step 4 uses the atlas presentation statement exactly as a sheaf quotient, and the sheafification universal property to map that quotient into Y. It does not use any representability or new-quotient theorem hidden in the source. Step 5 applies the set-sheaf map-gluing statement on the enlarged site: the site-density statement supplies its terminal object and finite limits, the model supplies the equivalence and covering. Applying map gluing also to the inverse produces an isomorphism; uniqueness proves global naturality and equality of the ring maps. Thus both details omitted by 04KL are accounted for.

Step 6 uses chart pullback of representables, Yoneda evaluation, slice transport of the given two-isomorphism, scheme uniqueness, and the atlas quotient. Each is stated by its citation; in particular full faithfulness of representable Yoneda alone would not supply arbitrary-presheaf evaluation, so I cited the evaluation node. Step 7 uses the normalized structural ring map statement and the affine-scheme/global-sections bijection. On every scheme test, equality on algebra generators gives equality of ring maps and hence of maps to Spec B. This proves monicity rather than citing 04KK itself. Step 8 uses the affine-basis and open-etale statements, chartwise composition, subcanonicality, and the general representable coequalizer presentation to extend identity from affine generators to every sheaf. Step 9 is elementary composition and inversion of isomorphisms, after the preceding rigidity proof. Every use was checked against the full cited statement and is quoted verbatim in citations.json.

Small cases checked: empty source (the degenerate one-object topos), empty target (a geometric morphism into its topos forces the same degeneration), identity morphisms and identity charts, nonseparated scheme charts, arbitrary infinite affine generator sets, and an atlas requiring infinitely many scheme opens. Slice formulas also work for initial and terminal A or B whenever the specified map s exists. Nonzero ring stalks are required only where geometric points exist. No finite-type, separation or quasi-compactness hypothesis is introduced. Every step is below 2000 characters, and each longer argument is one explicit construction rather than a hidden independently quantified lemma.

Mathlib searches reuse the logged earlier five-query passes for each new node, including two semantic phrasings, Loogle and source grep; the exact saved outputs were read. I read Etale.forgetFullyFaithful at Mathlib/AlgebraicGeometry/Morphisms/Etale.lean:177 and Scheme.fullyFaithfulForgetToLocallyRingedSpace at Mathlib/AlgebraicGeometry/Scheme.lean:290: the first forgets to an over-category, the second retains a locally ringed space, and neither reconstructs from an etale topos. I also read Sites/Over.lean:427: overMapPullback is restriction along a morphism of objects of one site; it does not assert arbitrary-sheaf relocalization or locality for ringed geometric morphisms. Other hits are ordinary slice pullbacks, structure sheaves on topological spaces, and unrelated algebraic/probabilistic localizations. No hit is an exact match or one-line specialization of a new statement.

## Not duplicates

lem-sfb-space-etale-conservative-geometric-points vs lem-sfb-space-stalk-ideal-pullback: The new node concerns arbitrary sheaves of sets, their point functors, and detection of mono/epi/isomorphisms; the existing node concerns module stalks and square-zero ideals or derived Tor-amplitude, and does not state set-sheaf point exactness.

lem-sfb-space-etale-conservative-geometric-points vs lem-sfb-space-ring-sheaf-tor-amplitude-stalk-test: The new node concerns arbitrary sheaves of sets, their point functors, and detection of mono/epi/isomorphisms; the existing node concerns module stalks and square-zero ideals or derived Tor-amplitude, and does not state set-sheaf point exactness.

lem-sfb-ringed-topos-slice-functoriality vs lem-sfb-space-locally-ringed-etale-topos-reconstruction: The new node is the arbitrary-topos fibre-product relocalization construction, its locality, and its functorial two-isomorphism transport. The existing item reconstructs algebraic-space maps; it does not state that general slice construction.

lem-sfb-space-etale-pullback-chart-comparison vs lem-sfb-space-stalk-ideal-pullback: The new node states representable/stalk pullback and the ring-compatible comparison for an arbitrary commutative scheme-chart square. The existing node states module or enlarged-site operations, or a square-zero ideal calculation; it does not state these general chart-square relocalization comparisons.

## Off-unit tools

- lem-a1-etale-atlas-presentation: Generic An etale atlas presents an algebraic space as its relation quotient used in the Stacks 04KL/04KK/04M6 foundation argument; no statement of this unit supplies it, and the alteration/direct-image route is unchanged.
- lem-pe-set-sheaf-cover-descent: Generic Effective descent and morphism gluing for sheaves of sets along a covering used in the Stacks 04KL/04KK/04M6 foundation argument; no statement of this unit supplies it, and the alteration/direct-image route is unchanged.
- lem-trf-space-chartwise-etale-permanence: Generic Chartwise etale permanence for algebraic spaces used in the Stacks 04KL/04KK/04M6 foundation argument; no statement of this unit supplies it, and the alteration/direct-image route is unchanged.
- lem-trf-space-enlarged-chart-ringed-morphism: Generic Chart-normalized ringed morphism on enlarged etale sites used in the Stacks 04KL/04KK/04M6 foundation argument; no statement of this unit supplies it, and the alteration/direct-image route is unchanged.
- lem-trf-space-enlarged-etale-ringed-site-model: Generic Enlarged etale ringed-site models of algebraic spaces used in the Stacks 04KL/04KK/04M6 foundation argument; no statement of this unit supplies it, and the alteration/direct-image route is unchanged.
- lem-trf-space-enlarged-ringed-composition-localization: Generic Composition and etale ringed localization for enlarged sites used in the Stacks 04KL/04KK/04M6 foundation argument; no statement of this unit supplies it, and the alteration/direct-image route is unchanged.
- lem-trf-space-enlarged-site-scheme-density: Generic Scheme-density comparison for the enlarged etale site used in the Stacks 04KL/04KK/04M6 foundation argument; no statement of this unit supplies it, and the alteration/direct-image route is unchanged.
- lem-trf-space-fibre-products-etale-covers: Generic Fibre products of algebraic spaces and pullback of etale coverings used in the Stacks 04KL/04KK/04M6 foundation argument; no statement of this unit supplies it, and the alteration/direct-image route is unchanged.
- lem-weil-pbc-sheaf-covering-representable-coequalizer-presentation: Generic Sheaf presentation by a covering set of sheafified representables used in the Stacks 04KL/04KK/04M6 foundation argument; no statement of this unit supplies it, and the alteration/direct-image route is unchanged.
