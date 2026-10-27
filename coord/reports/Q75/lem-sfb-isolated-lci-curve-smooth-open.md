## Worker report

Files written in this sandbox only:

- `dag/nodes/sec-six-functors-basics/lem-sfb-isolated-lci-curve-smooth-open.json`: item, split into six steps, statement unchanged.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-lci-base-open.json`: statement, no Mathlib match; universal base open for lci fibres of a flat closed lfp algebraic-space family.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-flat-smooth-locus.json`: statement, no Mathlib match; relative smooth locus for flat lfp algebraic spaces, with arbitrary base change.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-closed-subset-finite-fibre-open.json`: statement, no Mathlib match; finite geometric fibres of a closed subset in an arbitrary proper algebraic space.
- `dag/nodes/sec-six-functors-basics/lem-sfb-isolated-lci-curve-unobstructed.json`: statement, no Mathlib match; unobstructed deformations of separated finite-type isolated-lci curves, without properness.
- `dag/nodes/sec-six-functors-basics/lem-sfb-curve-smooth-locus-deformation-test.json`: statement, no Mathlib match; full curve-stack smooth-locus criterion, without lci or isolated-singularity assumptions.
- `citations.json`: a verbatim statement quotation for each of the six node citations in the item's proof.

All five new nodes are statement-only, unsplit, with no proof dependencies. No Lean, repository, launcher, literature, or unit file was written. The item is not a unit key node. Ancestor lookup returns `None`, as in the inherited blueprint record; each new node retains that ancestry and prepends the item to `via`.

Attachments: none. The exact blueprint tag and the notions `unobstructed`, `DeformationCategory`, `syntomicLocus`, `curveStack`, `lciLocus`, and the relevant tags were searched in `lean/WeilConjectures/`. No project declaration states the item or the new nodes. Sorry-bearing upstream declarations are not treated as proofs.

WANTED: none. Every source used is present under `literature/stacks-project/`.

The imported item is correct. It is the entire isolated-lci open of 0DZX, not merely the nodal locus, and no connectedness or nonemptiness condition is appropriate. The original proof was empty. Its statement and statement dependencies were retained. The unit route through curve moduli is unchanged.

Nothing mathematical is left unfinished at this split level; the five inputs remain queued as unsplit statements. Server dry run and delivery results are recorded below when available.

## Search evidence

All new-node and fresh item Mathlib searches were run with the prescribed `msearch.py Q75 lem-sfb-isolated-lci-curve-smooth-open` command, two LeanFinder phrasings per question plus LeanSearch, Loogle and grep. The actual outputs are preserved in `search-results.json`, the command log in `searches.jsonl`, and the exact tool/query/output triples in the node records. Existing item search records were retained.

The lci-base searches returned flatness, `UniversallyOpen.of_flat`, and open-immersion results, not syntomic or lci moduli statements. The smooth-locus searches returned `Algebra.isOpen_smoothLocus` and scheme smoothness results. I opened Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean lines 296–343: `Scheme.Hom.smoothLocus` is a scheme open, and `preimage_smoothLocus_eq` assumes an open immersion; neither is the arbitrary-base-change algebraic-space assertion. Loogle rejected the bare identifier `AlgebraicGeometry.IsSmooth` as unknown in its index, so an additional quoted `"smoothLocus"` search was made successfully; it again returns ring and scheme loci. The finite-fibre searches returned scheme `IsProper`, finite morphisms, and finite fibres of already finite maps, not a finite-fibre base open for closed subsets in algebraic spaces. The two deformation questions returned smooth rings and schemes, with no deformation-category or stack criterion. Therefore none is a Mathlib leaf.

Before creation I searched the entire DAG by tags 06CE, 06CA, 0A4Y, 0ACK, 03IQ, 0DZI, 02V4, 0DZQ and 0DZU and by the lci/open, finite-fibre, smooth-locus, and unobstructedness concepts; existing nearby nodes were opened. `tools/blueprint_refs.py search` was run for complete intersection, local complete, syntomic, deformation, unobstructed, finite fibre, smooth locus, and the principal tags. It found no equivalent blueprint statement. New ids did not exist in the repository.

## Not duplicates

lem-sfb-space-flat-smooth-locus vs lem-weil-pbc-fibre-of-base-change: both source records mention 02V4, but the existing node only identifies scheme-theoretic fibres under base change; it gives neither a smooth locus nor its openness or invariance, and has no algebraic-space assertion.

lem-sfb-space-lci-base-open vs lem-trf-syntomic-locus-base-change: the existing node is a source locus for a morphism of schemes; the new node is a universal base open for a closed flat lfp morphism with algebraic-space source, with no dimension bound. Etale descent and pushing the bad locus down a closed map are not a one-line specialization of the scheme-source statement.

lem-sfb-space-closed-subset-finite-fibre-open vs lem-trf-proper-finite-fibre-finite-near: the existing node is a scheme morphism and gives a finite restriction near one point; the new node is a base-change-compatible open for a closed subset of an algebraic space. Reducing an algebraic space to the scheme case is not available from that node.

lem-sfb-space-closed-subset-finite-fibre-open vs thm-sc-proper-finite-fibre-finite-neighbourhood: likewise the existing node concerns schemes, not a closed subset of an algebraic-space source.

lem-sfb-isolated-lci-curve-unobstructed vs lem-sfb-isolated-curve-formal-lifting: the latter constructs compatible formal deformations over k[t]/(t^n) from prescribed local deformations; it does not assert lifting across arbitrary Artinian coefficient-ring surjections and does not assume lci. The former is 0DZQ's unrestricted unobstructedness conclusion.

lem-sfb-curve-smooth-locus-deformation-test vs lem-sfb-curve-openness-versality: openness of versality for a parameter family is not the criterion that an arbitrary curve point is smooth over Z iff its deformation category is unobstructed.

lem-sfb-space-lci-base-open vs lem-coef-left-cone-restriction-cocartesian: the existing result is about restriction of quasicategorical cones and cites Kerodon 01UF, not Stacks 01UF; it makes no assertion about schemes or algebraic spaces.

lem-sfb-space-lci-base-open vs lem-trf-complete-intersection-fibres-limit-descent: the existing result descends scheme syntomicity along an affine inverse system; it does not produce a universal base open for a fixed closed flat algebraic-space family.

lem-sfb-space-lci-base-open vs lem-trf-syntomic-geometric-fibres-affine-criterion: the existing result compares affine-chart and geometric-fibre formulations for a scheme morphism; it gives no universal base open and does not cover algebraic-space sources.

## Review by Q75

I read moduli-curves.tex Tag 0DZX (lemma-big-smooth-part-curves), its full statement and proof, and its cited 0DZV, 0DZW and 0DZU. These establish exactly the item's smooth open and field-point characterization. The direct construction follows their intersection route. The chapter record, the assigned unit record, and the inherited supporting-node chain were read; no unit step is replaced.

For the lci input I read spaces-more-morphisms.tex 06CE (lemma-where-lci), 06CA (lemma-base-change-lci-fibres), 06C9 (lemma-flat-lci), and the fibre criterion 01UF on scheme charts. Taking Y=Z=S and q the identity in 06CE supplies the universal open; flatness identifies lci with syntomic, and 01UF identifies its fibres with the affine-cover lci condition. This is a general geometric input, rather than a new lci substack clause of the item. For the smooth-locus input I read spaces-morphisms.tex 0DZI and morphisms.tex 02V4, including case (1) and the displayed fibre calculation. I corrected the potential source overclaim by recording explicitly that 0DZI's listed invariance alone concerns flat base changes; arbitrary base change here uses flatness and local finite presentation of f and 02V4 on etale charts.

For the closed-subset finiteness input I read spaces-more-morphisms.tex 0A4Y, spaces-properties.tex 03IQ (and definition 047X), and decent-spaces.tex 0ACK. Here is why the source supports the stated consequence. Endow the closed subset T with its reduced closed subspace Z. The composite Z -> S is proper. Over an algebraically closed field its finite fibre is a zero-dimensional finite-type space, hence quasi-finite at all its points (0ACK, for this separated/decent space). 0A4Y gives a finite morphism over a neighbourhood. The union of such neighbourhoods is precisely the claimed open. Finite-type zero-dimensional fibres stay zero-dimensional with finitely many points under field extension, and the converse follows after a field extension as well; this proves the stated inverse-image equality. Reduction itself need not commute with base change: only the underlying closed subset is used. This argument is queued below the new statement, not silently assumed in the item.

For the unobstructedness input I read examples-defos.tex 0DZQ and its proof through affine gluing and affine lci unobstructedness, as well as example-schemes and section-general. The node quantifies over Noetherian local coefficient rings with residue field exactly k, a permitted special case of the source's coefficient category. It writes out objects, isomorphisms, and the lifting condition, not just the word unobstructed. For the smooth-point criterion I read moduli-curves.tex 0DZU, including the preceding Cohen-ring choice and the proof's comparison of scheme deformations with proper algebraic-space deformations. The node is for all proper dimension-at-most-one curves and gives the full iff criterion, not the isolated-lci clause of the item. It includes existence of the coefficient ring, so no uncited choice-of-Cohen-ring step is needed. In characteristic zero Lambda=k; in positive characteristic it is a Cohen DVR. Both choices are Noetherian local with the prescribed residue field.

Step 1 cites precisely the lci-base node's universal open and arbitrary-base-change statement. The family is proper, so its map is closed, and it is flat and finitely presented as required. Step 2 cites precisely the smooth-locus node to form the closed complement and identify its fibres, and the closed-subset finite-fibre node to obtain the open and check it over arbitrary fields. It never applies a schemes-only finite-neighbourhood lemma to an algebraic space. All three quoted statements have been read; citations.json contains verbatim text from them.

Step 3 is elementary from the two constructed base opens and the definition of a full substack: I wrote out locality, inherited descent, and the test-object fibre-product representation. No quotient-stack theorem or unrecorded algebraization theorem is used. Step 4 is the explicit two-way one-point-base check, using steps 1 and 2. Step 5 cites the existing separated dimension-at-most-one algebraic-space scheme theorem: its statement really grants scheme representability and does not require reducedness or connectedness. Properness provides its separated/lft hypotheses. It then cites exactly 0DZQ's lifting conclusion and 0DZU's criterion, with the same coefficient ring. Thus *all* field objects of the open are checked, including objects initially presented as spaces; merely checking the schemes already named in the item's conclusion would not suffice. Step 6 is elementary from the open M supplied in step 5: the pullback open contains every residue-field point, so it is the whole base; restricting a smooth atlas proves the required smoothness in the item's convention.

I checked B–E against the finished JSON. Statements introduce all their objects and define the Artinian, local, lci, proper-space and deformation conventions; there are no hidden proof sketches in new statements, no source tag used instead of a meaning, and no new node equivalent to the item or to one of its moduli clauses. Every non-elementary step cites its input statements, with full verbatim quotations. None of the six steps exceeds 2000 characters. New nodes have no proofs or proof dependencies, so no cycle can be introduced from them back to the item. The sole reused off-unit theorem is actually in the same assigned unit.

Small cases checked: an empty family has the whole good base; a smooth disconnected curve has empty nonsmooth subset; a disjoint union with a zero-dimensional nonreduced lci component is allowed and has only finitely many nonsmooth points; a curve generically nonsmooth on a positive-dimensional component is excluded; a non-lci isolated singularity is excluded by the first open. The finiteness lemma handles T empty, T=X with a finite fibre, and proper positive-dimensional fibres without assuming flatness. The lci lemma does not require pure dimension. The unobstructedness and criterion nodes allow the empty scheme, disconnected schemes, and imperfect positive-characteristic fields. These cases agree with the source, and no statement dispute remains.

The first server dry run stopped at the same-tag gate before preflight. I opened each of its three additional source matches. The affine syntomic criterion and the limit-descent theorem are scheme results, and the cone theorem is a Kerodon tag collision. Their exact differences are now recorded under Not duplicates; the mathematical construction does not change.
