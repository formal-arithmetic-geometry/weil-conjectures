# Stage-1 delivery: lem-trf-descended-resolution-smooth-comparisons

## Files written

- dag/nodes/sec-trace-formula/lem-trf-descended-resolution-smooth-comparisons.json: statement, split; nine proof steps, no statement change. Current Mathlib searches find no theorem about this labeled ordinary-resolution descent statement.
- No new nodes; no new Mathlib leaves. The proof reuses the existing flat-blowup theorem, its affine-chart formula and scheme-morphism gluing rather than introducing copies or new names for clauses of the item.
- citations.json: one entry for every node used by each proof step; each quote is the full verbatim statement read from the current repository. searches.jsonl is the search command's record, not hand-authored. ilo-viii.txt is the extracted source for review. write_split.py records the sandbox-only JSON construction.

## Attachments

None. I searched lean/WeilConjectures/ for the exact blueprint tag, descended/ordinary resolution, contracted towers and blowup comparisons. The homological ordinary-resolution hits concern complexes, not resolution of schemes. The blowup library contains individual-step constructions (including AlgebraicGeometry.Scheme.IdealSheafData.blowupFlatBaseChangeIso and hom_ext_comap_blowup), but none states the assigned theorem with all tower, label, cover and deletion clauses. Therefore ATTACH is inapplicable. Existing individual-step nodes are cited, not re-created.

## Sources and searches

I read ILO, Travaux de Gabber, Expose VIII, printed pp.87--93: 2.1.4--2.1.9 (ordinary towers, empty-stage contraction and flat pullbacks), 2.3.1, 2.3.4, and all of Remark 2.3.5 (especially disjoint-union synchronization and surjective nondeletion). These are available in literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, PDF pages 93--99. The source states the basic functoriality and synchronization observations, not this entire explicit conditional theorem. Consequently proof_origin.by is agent, and the induction, chart calculations and counts are supplied in the split.

I also read Stacks divisors.tex, Tags 0804 (lemma-blowing-up-affine) and 0805 (lemma-flat-base-change-blowing-up), and the empty-center calculation in 0807. I read morphisms.tex Tags 01VF (lemma-smooth-flat), 01U9 (lemma-base-change-flat), 01S1 (lemma-base-change-surjective) and the smooth open-restriction characterization, and the mapping property in schemes.tex, Tag 01JA (lemma-glue). No forbidden SGA source is used.

I read the live item and its parent ordinary-resolution split, the synchronized-Zariski-descent sibling, the ordinary-resolution definition, the chapter and unit records, and the latest blueprint chapter/unit and lem-trf-local-term-locality.proof.md. The current snapshot is main-20261023-1620 (7284bb09daf97437d544c51882b325f9c52cd345). The assigned item is explicitly an existing conditional tool on the historical nearby-duality/alteration branch. The newest local-term proof uses contracting correspondences. I have not rerouted that unit or changed its realization fields.

Whole-DAG searches covered ordinary/labeled towers, contracted pullbacks, unit stages, blowup base change, chart tensors, uniqueness, gluing and ideal extension. tools/blueprint_refs.py ancestor returned lem-trf-local-term-locality; whole-blueprint searches for blowup, resolution tower, contracted pullback and tensor base change found no imported node stating this conditional theorem. Existing synchronized-resolution descent constructs R and does not prove its smooth comparisons; existing maximum-history deletion concerns histories on embedded pairs and is not used as a substitute. The existing ordinary chart-restriction node supplies the precise reusable formula needed here.

The wrapper was run with LeanFinder twice (second phrasing: ordered sequences, flat pullback and contraction), Loogle, grep of Mathlib/AlgebraicGeometry and LeanSearch. I read the returned types: the hits concern smoothness, affine refinements, normalization, ideal comap composition and flatness composition. They do not state the theorem for finite centered blowup towers. The item keeps its original Q27 search records and appends exactly the Q09 wrapper queries and results. There are no new nodes needing separate search logs.

WANTED: none.

## Corrections and limitations

The item arrived statement-only and had no sandbox split/report to preserve. Its statement is consistent with ILO's ordinary-tower conventions; no STATEMENT-DISPUTED correction was necessary. The proof does not assume identity/composition laws for A: it proves them for the canonical ordinary blowup maps using the existing tensor chart formula. In particular, nonempty Cartier centers that yield isomorphic blowup morphisms are retained; contraction is by the unit-ideal test, not by whether a transition is an isomorphism.

The lem-sfb-flat-pullback-blowup-chart-restrictions citation is a generic geometric tool from another unit. Its whole statement was read; only the ordinary flat chart, localization and ideal clauses are used. Its etale-point and residue-field clauses are not needed. This use is declared in split_report.tool_uses for maintainer review. All other off-unit proof results are existing Mathlib leaves or Lean-closed nodes.

No mathematical part of the requested split remains unfinished. This is a natural-language stage-1 proof, not a new Lean proof or a claim that every cited unsplit node is formalized.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs.

## Review by Q09

I checked delivery-errors B--E with the item, every cited statement and the sources open. There are no newly stated mathematical facts in separate nodes: elementary sheaf equalities, deletion counts and fraction equalities remain proof steps. The existing chart lemma provides the non-elementary tensor isomorphism, including localization on overlaps; it is not inferred from a definition of blowups. Every step is shorter than 2000 characters, so there is no hidden long subproof moved into a new node or a replacement node restating the theorem.

Step 1 uses sbc-lem-smooth-criterion for flatness of the actual smooth h, lem-weil-pbc-flat-morphism-base-change for the level projections and thm-nagata-blowup-flat-base-change for the ordinary blowup isomorphism. I opened the latter's statement dependency def-nagata-blowup-flat-base-change-map: its target puts Y first and it is the actual chart-preserving canonical comparison, so the fibre-product factor order agrees. def-pc-fibre-product supplies projection-preserving identifications, and def-nagata-extended-ideal defines exactly the inverse-image center ideal. The induction starts with T and applies flat base change once at each original stage; no smoothness of an intermediate center is required.

Step 2 uses exactly the chart isomorphism and overlap clause in lem-sfb-flat-pullback-blowup-chart-restrictions. I checked the displayed B/C/D tensor formula on coefficients and fractions, including the direction from the tensor chart ring to the extended-ideal chart ring. Two successive coefficient maps give the identical fraction as the composite. At a unit ideal, the chart with denominator 1 is the base. The morphism-gluing node expressly supplies uniqueness of morphisms from an open cover, which promotes those equalities to scheme maps. Thus the equality of canonical maps is proved, not called natural without an argument.

Step 3 uses finite type only for quasi-compactness and the finite affine cover specified in def-weil-finite-type-morphism. A finite family of affine neighbourhoods subordinate to inverse-image opens follows by the finite-subcover property. lem-weil-pbc-smooth-restrict-open-subschemes says exactly both the restriction to U_a and the composite into U are smooth; lem-weil-pbc-smooth-local-on-source then handles the disjoint union V. The ordinary-resolution definition supplies the count and embedding format. The assumption on A applies to V -> U as whole embeddable inputs; the assumed uncontracted affine-cover identifications retain the full label list on both unions. A label absent on one component is not asserted absent globally.

Step 4 uses the given equal-ideal gluing hypothesis on R, the explicit chart calculation of Step 2 and lem-weil-pbc-scheme-morphism-gluing. That node states existence and uniqueness for arbitrary open covers. Affine intersections need not be affine: both source and target overlap are further covered by affine neighbourhoods. The induction starts at the base identity, treats every original label and inserts unit identity stages locally. Local inverses agree because they invert the same map on an overlap. This gives actual inverse global maps and the cartesian level identifications; both global schemes already exist, so no unproved effectivity of scheme descent is invoked.

Step 5 uses the same gluing uniqueness for transitions and the definition of a contracted comparison for the required data. Ideal equality is sheaf equality on a genuine cover; the lifts of V_b cover each pullback level and each R(T) level. The comparison for A(V) deletes an index exactly when its ideal is unit on the entire disjoint union, equivalently unit on every component. A retained center is nonempty, so it cannot be unit. The increment equations for c are cardinality identities for the surviving subsequence. This is elementary assembly of proved local isomorphisms and the given assumptions.

Step 6 compares arbitrary cover choices on common affine neighbourhoods of the type constructed in Step 4. The hypothesis supplies the cover-comparison cocycle; Step 2 supplies equality of the ordinary blowup maps. Morphism-gluing uniqueness proves independence of covers and restriction to the specified A comparison. Step 7 checks the identity formula by the nonempty-center hypothesis and the identity chart formula; no stage disappears merely because its blowup is an isomorphism.

Step 8 proves composition with the same indexed stages and ideals. Both iterated extensions are generated locally by images of the original ideal generators; the definition via inverse-image closed subschemes gives the same assertion from fibre-product associativity. A unit ideal stays unit. Induction identifies the surviving embeddings as r_h composed with r_g and the counts as c_g composed with c_h, including repeated count values at deleted stages. Direct and successive chart maps have the identical coefficient/fraction formula of Step 2. The fibre-product definition identifies the associator by projections, and gluing proves equality of global level maps. A composition law for A is not assumed circularly.

Step 9 uses lem-weil-pbc-surjective-base-change, whose statement allows any scheme base change of a surjective morphism. It is applied first to S_i and then to its nonempty closed center, so every pulled-back center is nonempty and cannot have unit ideal. The extended-ideal definition identifies precisely that inverse-image closed subscheme. The empty-input claim comes from the assumed uncontracted cover identification, not from surjective nondeletion on an arbitrary empty source.

I tested length-zero towers, identity h, empty source, empty target (forcing empty source), an open map meeting only the regular locus, disjoint unions where a center misses some components, a nonempty Cartier center, and a composite making a previously retained center empty. The survivor and count formulas give the expected results. Nonseparated S is allowed throughout: overlap checks use affine refinements, not affineness of intersections. Relative dimension may vary, since only smoothness, flatness and canonical base change are used.
