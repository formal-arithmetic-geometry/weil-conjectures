## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-relative-lci-source-locus.json`: item, split into five steps; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-scheme-relative-lci-base-change-points.json`: new statement-only scheme theorem, Stacks Tag 06B8; unsplit, no Mathlib match. One new node, zero Mathlib leaves.
- `citations.json`: every citation in every item step, with its verbatim statement. Full statements keep all clauses of the presentation and open-subspace tools visible together.
- `searches.jsonl`: actual msearch records, retained unchanged; `write_split.py` is sandbox-only preparation material, not part of the delivery.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact item tag, relative lci loci, Koszul-at-a-point and local complete intersection terminology. The available algebraic and Koszul declarations do not state the relative source-locus theorem for algebraic spaces. No Lean was written, compiled, or built.

## Wanted

None. All proof sources are present under `literature/stacks-project/`.

## Corrections and route

The item was unsplit and the sandbox contained no earlier node or report. The mathematical statement is retained. Doubled TeX backslashes in the imported statement were reduced to single TeX commands; this is a rendering correction, not a hypothesis or conclusion change.

Read the chapter and unit records and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` unit and direct-image proof. This is the inherited auxiliary source-locus input below that route; neither a unit nor a chapter is changed. `blueprint_refs.py ancestor` returns `None`, as already recorded in this item's ancestry. I preserved that value and the full inherited place/via chain, and added the precise 06CA chart-reduction place for the new node. Whole-blueprint searches for `lci`, `06B8`, `complete intersection`, and `Koszul` found no equivalent blueprint theorem; the Koszul hits concern complexes, signs, or coefficients.

The proof follows spaces-more-morphisms.tex Tag 06CA. Its nontrivial input is more-morphisms.tex Tag 06B8, not the fibrewise complete-intersection locus for a structural map. The new node is the scheme pointwise base-change theorem, leaving the passage to arbitrary algebraic spaces, the pointwise chart equivalence, construction of the open, and the global lci criteria in the item's argument. It is not the item relabelled: the item must construct and identify opens for nonrepresentable spaces under an algebraic-space base change, none of which is supplied by the new statement.

The generic tools from other units are declared in `split_report.tool_uses`: the three a1 point/open nodes, the trace-formula fibre-product node, and the scheme etale-composition node. Their statements are general topology or atlas tools; no proof route of their host chapters is used. The presentation and locality nodes are already in this item's unit.

## Not duplicates

lem-sfb-scheme-relative-lci-base-change-points vs lem-sfb-space-relative-lci-source-locus: the new node supplies only the pointwise theorem for a map of schemes over a scheme and a scheme change of base (06B8); the item carries the compatible-chart reduction, open-subspace construction and global criteria for algebraic spaces (06CA).

lem-sfb-scheme-relative-lci-base-change-points vs lem-sfb-space-fibrewise-lci-source-locus: the existing node concerns complete-intersection fibres of a structural flat map; the new node concerns an arbitrary map between two flat families, whose fibres themselves may be singular non-complete-intersections. The identity of such a family is still lci everywhere.

lem-sfb-scheme-relative-lci-base-change-points vs lem-trf-syntomic-locus-base-change: the existing statement concerns syntomic/fibrewise-complete-intersection points of a flat structure map; it cannot test a possibly nonflat map between two flat families.

lem-sfb-scheme-relative-lci-base-change-points vs lem-sfb-space-relative-lci-parameter-open: the existing node requires a closed source projection and constructs an open in the parameter base; it uses the item and cannot be cited here without a cycle. The new node imposes no closedness and makes a pointwise scheme assertion.

lem-sfb-scheme-relative-lci-base-change-points vs lem-sfb-space-lci-base-open: the existing node requires a closed structural projection and tests whole fibres in a base open. The new theorem is pointwise on the source of a relative map and is needed even for the identity of a non-lci fibre.

lem-sfb-scheme-relative-lci-base-change-points vs lem-sfb-scheme-lci-etale-locality: that node supplies etale locality for an arbitrary scheme map, not preservation and reflection under an arbitrary parameter change for two flat families. It is reused in the item rather than duplicated.

The DAG source/tag search found no node sourced at 06B8. The four nodes referring to `lemma-base-change-lci-fibres` in their sources are the item's 06CA family and its structural/base-open specializations discussed above. Name and concept searches also inspected the existing scheme lci locality, pointwise field-lci invariance, and Koszul immersion flat ascent/descent statements. None states 06B8. In particular flat ascent for an immersion cannot justify the arbitrary nonflat base change here.

## Review by Q17

I read the complete statement and proof of spaces-more-morphisms.tex Tag 06CA (`lemma-base-change-lci-fibres`), the definition and preceding locality explanation at 06C4, the statement and proof of more-morphisms.tex Tag 06B8, and its `definition-lci`. I also read the presentation criterion 03MJ and the open-subspace results 03BZ, 03IE and 03IR in the Stacks files. The only new node is precisely the pointwise interpretation of 06B8. Its hypotheses are those of that source: both structural maps flat and locally finitely presented, but neither the relative map nor the base change assumed flat. Its statement defines lci and Koszul at a point explicitly and introduces every scheme and projection; it contains no proof sketch.

For step 1 I opened both the scheme-lci-locality and algebraic-space-presentation-criterion nodes. The former explicitly gives etale source-and-target locality; the latter tests all presentations or a single presentation with surjective source, without requiring the target chart to be surjective. These are exactly the assertions used. I opened the etale-open-image and open-factor-scheme-tests nodes: they respectively provide an open image and a surjective etale factorization onto it. This proves the pointwise criterion in both directions on each chart lift. An existential good lift alone would not suffice for step 5, so the stronger per-lift equivalence is written out.

For step 2 the point-open-calculus statement identifies each open subspace with an open subset, and etale-open-image includes the inclusion-preserving bijection between all such opens. The open-factor statement identifies their inverse images on a scheme presentation. The existing presentation criterion then gives lci on each inverse-image open; the explicit local factorization definition in scheme-lci-locality glues this cover on the source. Thus the restriction is actually lci, not merely a union of points called good. This also proves the global criterion without requiring the families to be flat in this step.

For step 3 I checked the algebraic-space definition gives the required scheme atlases and the fibre-product node gives preservation of surjective etale families and the needed scheme products. Etale composition is taken from the scheme composition/cancellation node after scheme tests, rather than being asserted for spaces from a scheme-only citation. The five-properties locality node explicitly includes flatness and local finite presentation. Its combination with the general presentation criterion makes the scheme maps D to W and V to W flat and locally finitely presented. These are exactly the two hypotheses of 06B8; no flatness of D to V is asserted.

For step 4 the atlases and composite maps are checked by the same fibre-product, definition, and scheme-composition statements. The actual parameter map in the scheme application is W-prime to W, not B-prime to B or V-prime to V. The scheme products give D-prime = D times_W W-prime and V-prime = V times_W W-prime. The new node's quoted statement applies to that diagram and gives the equivalence at every D-prime point. I checked that these pulled-back chart maps still surject onto A-prime and C-prime even when the original base change is not surjective.

For step 5 the chart criterion from step 1 applies to each of the two diagrams, and the surjective source atlas supplies a lift of each A-prime point. The open-factor node explicitly states the inverse-image point formula for arbitrary algebraic-space maps. The open-subspace correspondence identifies the two subfunctors, and the full-point-image clause of point-open-calculus gives the last equivalence. These statements, not their proofs or unquoted definitions, are what the step uses. Every citation has its actual statement in citations.json; the proof dependencies equal the union of uses. No new dependency reaches back to the item.

I tested the assertions on the empty source and an empty base change; the pointwise statements are vacuous, the locus is the entire empty source, and the restriction is lci. On the identity of a singular flat family, the locus must be the entire source, even if the fibre is not a complete intersection; this rules out substituting the existing fibrewise structural-locus lemma. On the zero section B to affine one-space over B, the relative map is lci but generally not flat, and remains so after the nonflat base change Spec(k) to Spec(k[t]); its ideal is the single polynomial variable, which stays regular. On the map Spec(k) to Spec(k[e]/(e^2)) at e=0, both structure maps to Spec(k) are flat and finitely presented but the relative map is not lci, as the nonzero square-zero generator is not Koszul regular; extension of the field does not remove that defect. Empty fibres of an open immersion after base change also obey the claimed equality. These tests expose neither a missing hypothesis nor a statement dispute.

I checked delivery-errors B through E point by point. The new node is self-contained, statement-only, sourced by the verified tag and label, and searched by all required methods with a second semantic phrasing; no search was invented and none was unavailable in this run. The hits concern flatness, smoothness, generic stable properties, differentials, and smooth or etale loci, which do not prove the lci equivalence. The proof has no step longer than 2000 characters, and the local chart comparison is an explicit application of the existing general presentation criterion rather than an uncited comparison theorem. The new node is a substantial scheme input used in the source's reduction, not an elementary observation, a whole-item replacement, or an existing DAG specialization. No SGA source is used.

## Unfinished work

None within this one-level stage-1 split. The new scheme theorem is intentionally unsplit and enters the queue with its verified source and searches. Server dry-run and delivery results are recorded below when available.
