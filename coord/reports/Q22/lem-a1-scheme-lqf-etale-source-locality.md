# Q22 stage-1 repair: lem-a1-scheme-lqf-etale-source-locality

1. Files written (all node paths under dag/nodes/sec-purity-real-sheaves/):
   - lem-a1-scheme-lqf-etale-source-locality.json: existing statement unchanged, now a five-step assembly (2525 characters).
   - lem-a1-etale-open-restriction.json: statement, Mathlib leaf, AlgebraicGeometry.Etale.instResLE, Mathlib/AlgebraicGeometry/Morphisms/Etale.lean:95–97.
   - lem-a1-scheme-lqf-composition.json: statement-only, unsplit; no exact Mathlib match for the scheme notion that includes local finite type.
   - lem-a1-etale-affine-finite-fibre-refinement.json: statement-only, unsplit; no exact Mathlib match for finite affine refinement followed by descent of finite fibres.
   - report.md and citations.json: self-review, complete argument preservation, and verbatim statement quotations for each parent citation. searches.jsonl is the unedited msearch output log.
2. Attachments: none. Searched the item tag and notions in lean/WeilConjectures/. The live Sheaf theorem AlgebraicGeometry.Scheme.Hom.isLocallyQuasiFinite_etale_source is still proved by sorry. Mathlib's Etale.instResLE is recorded as a leaf, not claimed as a project attachment.
3. WANTED: none. All sources needed here are present in literature/stacks-project/.
4. Fault repaired: the released repair note dated 2026-10-22 reopens the previously reviewed seven-step, 5139-character proof. The initial sandbox contained only dispatcher markers, not the previous node or report. I copied the live node, whose proof exactly matches the seven returned step lengths, and retained its statement, stmt_deps, metadata, existing searches and accepted tool uses. The first required dry run exited before preflight because report.md was missing. This repair creates two separately claimable unsplit arguments and one exact Mathlib leaf; it does not simply shorten the former prose. No statement dispute was found.
5. Unfinished: the proofs of the two new unsplit statements are deliberately left for other stage-1 workers, as the human's re-split order requires. No Lean file was written and no compiler, Lake or build tool was invoked.

## Repair of the return

The argument allocation is as follows. The complete former text, including its citations, is preserved verbatim at the end of this report so that no work is lost by the extraction.

- Old step 1 (1438 characters) belongs to lem-a1-etale-open-restriction. Its flat local-ring identification, D(r)/D(a) shrinking, finite-presentation localization/base-change calculation, and restricted open diagonal remain the source argument in the appendix. The extracted statement is exactly the result that argument establishes, and Mathlib Etale.instResLE states it directly. The point-surjectivity sentence is still explicit in parent step 4.
- Old step 2 (914 characters) belongs to lem-a1-scheme-lqf-composition. This is generalized from the special first map being etale to any locally quasi-finite scheme map. The same affine charts Z,W,A, finite-type/quasi-finite ring maps, ring composition and pullback functoriality establish the generalized conclusion. Parent step 1 retains the separate affine argument showing that an etale p is locally quasi-finite using the existing etale-ring-map node; parent step 2 invokes the new general composition node. Thus the new node is not a restatement of the parent's forward clause.
- Old step 3 (457 characters) remains parent step 3, an assembly of the existing local-finite-type consequence and flat/lfp/surjective source descent. It is already a short application of an existing independently assigned node and needs no duplicate extraction.
- Old steps 4–6 (1423 characters together) belong to lem-a1-etale-affine-finite-fibre-refinement. That statement exposes the actual finite affine opens A_j, their quasi-finite maps to Z, finite fibres, the fibre-union equality, and finiteness after taking images. This preserves the non-quasi-compact-source refinement argument and the m=0 case, rather than hiding them behind a statement identical to local quasi-finiteness descent. Parent step 4 only restricts p and the composite, verifies surjectivity, and applies this node.
- Old step 7 (907 characters) remains parent step 5: apply the already existing affine-pair finite-type criterion, affine-implies-quasi-compact, finite-type definition, finite-fibre quasi-finiteness criterion and affine-cover gluing. It is assembly of existing cited results; no comparison or new independent lemma is hidden there. References to old Step 6 are updated to Step 4, its new location.

The two open nodes represent comparable arguments: the affine ring-composition/local-to-global construction (old step 2), and finite affine refinement plus finite images (old steps 4–6). Neither proves the whole item, neither has a proof array, and both may be assigned independently. The source-restriction work has an exact Mathlib leaf. Each parent step is below 2000 characters and total text is below 3000.

## Searches and source checks

Read Stacks Descent Tag 03X4, label lemma-locally-quasi-finite-etale-local-source, descent.tex:6964 onward, in full. Its proof uses etale precomposition, descent of finite type and finite fibres. Read Tag 02KL, lemma-flat-finitely-presented-permanence, descent.tex:4385 onward, to verify that source descent has no quasi-compactness requirement. Read Tag 02GJ, lemma-etale-characterize, morphisms.tex:8090 onward, including the compatible-open restriction conclusion; this is the source of the extracted leaf. Read Tag 01TL, lemma-composition-quasi-finite, morphisms.tex:3897 onward, and Tag 01TK, lemma-locally-quasi-finite-characterize, to check the generalized composition statement and its affine proof. Read Topologies Tag 0218, lemma-etale-affine, topologies.tex:766 onward, and Morphisms Tags 01TH, 01TJ and 02NH for the finite-fibre refinement. Read the local-finite-type affine characterization Tag 01T2, morphisms.tex:2673 onward, to check the retained affine restriction argument.

Ran the blueprint ancestor command: lem-a1-affine-hc0. Ran whole-blueprint searches for etale restriction, finite fibres, quasi-finite composition, locally quasi-finite, etale characterize, 03X4, 02GJ and composition of locally. No imported blueprint node states the extractions. Searched the whole DAG by these tags and key notions, then read candidate statements, especially lem-weil-pbc-etale-local-on-source, lem-trf-quasi-finite-composition, lem-weil-pbc-etale-covering-affine-refinement, pqf-lem-qf-finitefibres, and the proper-stack composition node. They supply parts of these arguments but do not duplicate them. The inherited main-20261015 ancestor and Rankin–Selberg chapter/unit route remain unchanged; these are the inherited schemehood tools beneath its auxiliary branch.

Every recorded new-node Mathlib query was run via msearch.py and its actual summary is in searches.jsonl and mathlib_searches. LeanFinder, Loogle, LeanSearch and grep all responded. I read the hits before verdicts. For composition and refinement, I tried the second semantic formulations recorded in the nodes, plus a second Loogle/grep search for refinement. For the restriction leaf, Loogle returned Etale.instResLE directly, and the pinned file at lines 95–97 gives exactly Etale (f.resLE V U e). The source notion is the existing etale definition, not a new one.

The composition candidate AlgebraicGeometry.instLocallyQuasiFiniteCompScheme (QuasiFinite.lean:85–87) is for Mathlib's notion. That file explicitly says at lines 19–24 and 55–60 that local finite type is not included. FiniteType.lean:68–70 separately gives finite-type composition. The bridge to the node's affine-neighbourhood predicate is a project theorem in WeilConjectures/AlgebraicGeometry/QuasiFiniteMorphismComparison.lean:62–76, not a Mathlib theorem. Thus no exact Mathlib leaf is claimed for this combined Stacks statement. Mathlib finite_preimage_singleton, QuasiFinite.lean:174–176, requires a quasi-compact map. The arbitrary X→Z in the refinement need not be quasi-compact, so that hit alone does not provide our finite-fibre descent or the required finite collection of affine opens. isFinite_iff is about finite morphisms and cannot replace it.

## Review by Q22

I checked B–E against the files and the sources, not just against the tool output. Each new statement introduces its schemes and all its maps. Affine schemes and open subschemes refer to def-pc-scheme; etale to def-weil-etale-morphism; the exact finite-type-containing local quasi-finiteness and set-theoretic finite fibres to pqf-def-quasifinite. The two open nodes have empty proof, empty proof_deps and null proof_origin. They contain conclusions, not proof sketches. Sources have tags and labels, and blueprint.from identifies the inherited schemehood branch and the particular extraction. No SGA source is used.

For parent step 1 I opened lem-a1-etale-open-restriction: it gives etaleness for precisely the compatible affine opens chosen there. I opened lem-weil-pbc-etale-ring-map-quasi-finite: its hypothesis is an etale spectrum morphism and its conclusion is finite generation and quasi-finiteness at every target prime, precisely the witnesses pqf-def-quasifinite requires. The affine scheme/spectrum identification and choosing affine neighbourhoods are structural scheme operations. Parent step 2 uses only the new composition statement, whose two local-quasi-finite hypotheses are the assumed g and p proved in step 1.

For parent step 3 I reopened lem-weil-pbc-lqf-locally-finite-type, def-weil-etale-morphism, and lem-a1-lft-flat-lfp-source-descent. The first gives local finite type of the composite. The definition supplies flatness and local finite presentation of p. The descent statement requires those and point-surjectivity, all available in the converse. It does not ask for quasi-compactness.

For parent step 4 I checked that the leaf gives the restriction over W, point-surjectivity follows by taking any p-preimage of a point of W, and lem-weil-pbc-lqf-restriction-to-opens gives the composite into the chosen target open Z. Both W and Z are affine and p^{-1}(W) is a scheme with no finiteness condition. Therefore every hypothesis of the new finite-fibre refinement node is in force. Its explicit conclusion says h^{-1}({z}) is finite, which is exactly what the next step uses. The underlying finite-image argument is recorded in its statement and fully retained below, not silently assumed as a new source-descent theorem.

For parent step 5 I reopened all seven cited nodes. lem-weil-pbc-lft-affine-pairs says the finite-type ring-map condition for every pair of affine opens, in both directions. Apply it first to g from step 3, then to its restriction W→Z: affine opens of W and Z are also affine opens of V and T. lem-weil-pbc-morphism-affine-schemes-affine applies because W and Z themselves are affine. Clause (3) of lem-weil-pbc-affine-morphism-permanence supplies quasi-compactness. def-weil-finite-type-morphism defines finite type as local finite type plus quasi-compactness. pqf-lem-qf-finitefibres has all its locally finite type, finite type, quasi-compact and finite-fibre hypotheses satisfied; its reverse implication gives quasi-finiteness. pqf-lem-qf-locqf-qc then gives local quasi-finiteness. Finally condition (3) of lem-a1-scheme-lqf-affine-criterion glues the affine restrictions. Each step has a verbatim supporting quotation in citations.json. The retained non-elementary tool uses are the already accepted etale-ring, lqf-to-lft, restriction-to-opens and qf/lqf/qc tools; the removed ring-composition use now belongs to the extracted composition node's future split.

Small cases: if the surjective source is empty then W is empty; m=0 is allowed and all the relevant fibres are empty. For an infinite disjoint union of copies of an affine W mapping by identity to W, q is etale surjective but need not be quasi-compact; finitely many affine pieces covering W still suffice, and no statement asserts that X→Z itself has finite fibres. A nonsurjective empty/open source cannot imply finite fibres below: the refinement statement therefore retains surjectivity. For h:A^1_k→Spec k the fibre is infinite for algebraically closed k, so it cannot admit the hypothesized locally quasi-finite composite under an etale surjective q. Composition does not assert preservation of global quasi-compactness. Restrictions allow empty A and B, with etaleness vacuous. No affine intersection is assumed affine and no Noetherian or separation hypothesis is used.

Corrections made were the actual extraction of the three separate pieces, the re-indexing of the final fibre reference, and the explicit distinction between the Stacks and Mathlib local-quasi-finite predicates when deciding the two open nodes. The parent statement and statement dependencies are byte-for-byte unchanged from the copied live node. No Lean or target statement was changed.

## Repair of the landing refusal (2026-10-22)

The return names delivered head 0a9e9f4ba91 and says the independent reader approved the mathematics, but side-project completion had not been promoted to the live DAG. I retained the delivered sandbox, its three new statements, all logged searches, citations, and complete seven-step argument appendix. The current read-clone sheaf-dag head inspected for this repair is b65fee8ec1497d642b6c70f40585e92e7a7b2abd. The required initial dry run rebuilt the retained delivery against the current server DAG and passed at bb20d6baadd. I then reviewed the live files before making this repair; the final dry run below supersedes that initial receipt.

The current live item still carries the seven-step proof and its original statement. Against that live node, the retained item differs only in proof, proof_deps and split_report. Thus the statement, stmt_deps, source, blueprint ancestry, existing search records, reviewed records, accepted tool uses and Lean binding are preserved exactly; no side-project metadata overwrites newer live metadata. All three extracted node ids are still absent from the live DAG. The live released stage-1 repair note, dated 2026-10-22 with keep_plan true, explicitly reopens this split despite its old reviewed record and requires at least two new work items and assembly at most 3000 characters. This is why the old side completion is not treated as an attachment or as permission to return the old seven-step proof unchanged. Promotion remains the maintainer's landing operation.

I reread every current statement used by all five steps, rather than assuming that the returned dependency versions still apply. In step 1 the etale ring-map theorem provides both finite generation and quasi-finiteness at each prime, as the scheme definition requires. Step 2 uses the general composition extraction, not a duplicate of the etale forward clause. Step 3's flat, locally finitely presented, point-surjective source-descent statement still has no quasi-compactness hypothesis. Step 4's restriction theorem still covers both chosen opens, and the new refinement supplies actual affine pieces, finite fibres and the fibre-union equality. I made that last use explicit in the repaired parent: the fibre downstairs is a finite union of images of the finite fibres upstairs, including the empty chart. This is a concrete proof edit in addition to rebasing and updating this report. Step 5's current affine-pair theorem, affine-morphism theorem and permanence clause (3), finite-type definition, both quasi-finiteness equivalences and affine-cover criterion each provide exactly the conclusions used. All 17 quote records remain verbatim and cover every step/citation pair.

For this repair I reopened Stacks descent.tex, labels lemma-locally-quasi-finite-etale-local-source (03X4) and lemma-flat-finitely-presented-permanence (02KL), morphisms.tex labels lemma-composition-quasi-finite (01TL) and lemma-etale-characterize (02GJ), and topologies.tex lemma-etale-affine (0218). These agree with the retained statements and the assembly. I reread the Mathlib restriction instance and the warning that Mathlib local quasi-finiteness omits finite type, along with the project's comparison theorem. The current project item theorem still ends in sorry, so it cannot be attached. I reused the recorded Mathlib searches after reading their returned hits, since none of the statements or search questions changed. Fresh whole-DAG and blueprint searches found no new duplicate for the three extractions. Empty sources, non-surjective opens, infinite disjoint-union covers and the affine-line test remain covered by the explicit hypotheses described in the review above. No step exceeds 2000 characters and total assembly remains below 3000 characters.

## Not duplicates

lem-a1-scheme-lqf-composition vs lem-a1-scheme-lqf-affine-criterion: the new node states composition for arbitrary locally quasi-finite morphisms of schemes, without properness or etaleness; the existing node states Affine chart criterion and Zariski locality for scheme local quasi-finiteness. Shared source tags: 01TK.

lem-a1-scheme-lqf-composition vs lem-trf-quasi-finite-composition: the new node states composition for arbitrary locally quasi-finite morphisms of schemes, without properness or etaleness; the existing node states Composition of quasi-finite ring maps. Shared source tags: 00PO.

lem-a1-scheme-lqf-composition vs lem-cbc-right-fibration-morphism-space: the new node states composition for arbitrary locally quasi-finite morphisms of schemes, without properness or etaleness; the existing node states Mapping spaces and transport in a right fibration. Shared source tags: 01TL.

lem-a1-etale-affine-finite-fibre-refinement vs lem-a1-scheme-lqf-etale-source-locality: the new node supplies finitely many affine opens of an arbitrary etale covering source, their quasi-finite composites, the fibre-union equality and finite fibres downstairs; the existing node states Local quasi-finiteness of schemes is etale local on the source. In particular the new conclusion stops at finite fibres on a single affine triangle; it neither descends local finite type nor concludes local quasi-finiteness of h, and contains neither whole clause of the parent. Shared source tags: 03X4.

lem-a1-etale-affine-finite-fibre-refinement vs pqf-lem-qf-finitefibres: the new node supplies finitely many affine opens of an arbitrary etale covering source, their quasi-finite composites, the fibre-union equality and finite fibres downstairs; the existing node states Quasi-finite = finite type + quasi-compact + finite fibres. Shared source tags: 02NH.

lem-a1-etale-affine-finite-fibre-refinement vs lem-weil-pbc-morphism-affine-schemes-affine: the new node supplies finitely many affine opens of an arbitrary etale covering source, their quasi-finite composites, the fibre-union equality and finite fibres downstairs; the existing node states A morphism between affine schemes is affine (Stacks 01SH). Shared source tags: 01SH.

lem-a1-etale-affine-finite-fibre-refinement vs lem-weil-pbc-quasi-finite-at-point-isolated: the new node supplies finitely many affine opens of an arbitrary etale covering source, their quasi-finite composites, the fibre-union equality and finite fibres downstairs; the existing node states Quasi-finite at a point implies isolated in the fibre. Shared source tags: 01TH.

lem-a1-etale-affine-finite-fibre-refinement vs lem-weil-pbc-affine-morphism-permanence: the new node supplies finitely many affine opens of an arbitrary etale covering source, their quasi-finite composites, the fibre-union equality and finite fibres downstairs; the existing node states Base change, affineness of the source, and quasi-compactness and separatedness of affine morphisms. Shared source tags: 01S7.

lem-a1-etale-affine-finite-fibre-refinement vs lem-weil-pbc-finite-over-separated-finite-type: the new node supplies finitely many affine opens of an arbitrary etale covering source, their quasi-finite composites, the fibre-union equality and finite fibres downstairs; the existing node states A scheme finite over a separated finite-type scheme. Shared source tags: 01S7.

lem-a1-etale-affine-finite-fibre-refinement vs lem-weil-pbc-isolated-fibre-point-base-change: the new node supplies finitely many affine opens of an arbitrary etale covering source, their quasi-finite composites, the fibre-union equality and finite fibres downstairs; the existing node states Points isolated in their fibre stay isolated after base change. Shared source tags: 01TH.

lem-a1-etale-affine-finite-fibre-refinement vs lem-weil-pbc-isolated-fibre-point-quasi-finite-affine-pairs: the new node supplies finitely many affine opens of an arbitrary etale covering source, their quasi-finite composites, the fibre-union equality and finite fibres downstairs; the existing node states A point isolated in its fibre is quasi-finite on every affine pair (Stacks 01TH, (2) implies (4)). Shared source tags: 01TH.

lem-a1-etale-affine-finite-fibre-refinement vs lem-weil-pbc-proper-smooth-connected-fibre-dimension-loci: the new node supplies finitely many affine opens of an arbitrary etale covering source, their quasi-finite composites, the fibre-union equality and finite fibres downstairs; the existing node states Clopen dimension loci in proper smooth connected families. Shared source tags: 01TH.

lem-a1-etale-affine-finite-fibre-refinement vs lem-weil-pbc-etale-covering-affine-refinement: the new node supplies finitely many affine opens of an arbitrary etale covering source, their quasi-finite composites, the fibre-union equality and finite fibres downstairs; the existing node states An etale covering of an affine scheme is refined by a finite family of affine opens of its members. Shared source tags: 0218.

lem-a1-etale-affine-finite-fibre-refinement vs lem-weil-pbc-discrete-field-base-change-artinian: the new node supplies finitely many affine opens of an arbitrary etale covering source, their quasi-finite composites, the fibre-union equality and finite fibres downstairs; the existing node states Base change of a discrete finite type scheme to a field extension. Shared source tags: 02NH.

lem-a1-etale-affine-finite-fibre-refinement vs lem-weil-pbc-lft-over-field-isolated-point-residue-finite: the new node supplies finitely many affine opens of an arbitrary etale covering source, their quasi-finite composites, the fibre-union equality and finite fibres downstairs; the existing node states An isolated point of a scheme locally of finite type over a field has residue field finite over the field. Shared source tags: 01TH.

lem-a1-etale-affine-finite-fibre-refinement vs lem-weil-pbc-finite-closed-map-finite-fibres: the new node supplies finitely many affine opens of an arbitrary etale covering source, their quasi-finite composites, the fibre-union equality and finite fibres downstairs; the existing node states A finite morphism is separated, universally closed and has finite fibres. Shared source tags: 02NH.

lem-a1-etale-affine-finite-fibre-refinement vs lem-weil-pbc-isolated-fibre-point-residue-finite: the new node supplies finitely many affine opens of an arbitrary etale covering source, their quasi-finite composites, the fibre-union equality and finite fibres downstairs; the existing node states An isolated point of a fibre of a locally finite type morphism has finite residue field extension. Shared source tags: 01TH.

lem-a1-etale-affine-finite-fibre-refinement vs lem-weil-pbc-lqf-restriction-to-opens: the new node supplies finitely many affine opens of an arbitrary etale covering source, their quasi-finite composites, the fibre-union equality and finite fibres downstairs; the existing node states Restriction of a locally quasi-finite morphism to open subschemes is locally quasi-finite (Stacks 01TH (4)). Shared source tags: 01TH.

lem-a1-etale-affine-finite-fibre-refinement vs lem-weil-pbc-etale-limit-tail-open-geometry: the new node supplies finitely many affine opens of an arbitrary etale covering source, their quasi-finite composites, the fibre-union equality and finite fibres downstairs; the existing node states Geometry of the explicit tail-open inverse diagram. Shared source tags: 01S7.

lem-a1-etale-affine-finite-fibre-refinement vs lem-weil-pbc-etale-qcqs-cofinal-finite-coverings: the new node supplies finitely many affine opens of an arbitrary etale covering source, their quasi-finite composites, the fibre-union equality and finite fibres downstairs; the existing node states Cofinal finite affine etale coverings of a quasi-compact quasi-separated etale object. Shared source tags: 0218.

lem-a1-etale-affine-finite-fibre-refinement vs lem-pur-parameter-chart-germ-criterion: the new node supplies finitely many affine opens of an arbitrary etale covering source, their quasi-finite composites, the fibre-union equality and finite fibres downstairs; the existing node states Parameter tuples characterize germs of flat quasi-finite affine-space charts. Shared source tags: 01TH.

lem-a1-etale-affine-finite-fibre-refinement vs new-etale-finite-affine-cech-basis: the new node supplies finitely many affine opens of an arbitrary etale covering source, their quasi-finite composites, the fibre-union equality and finite fibres downstairs; the existing node states Finite affine etale covers are cofinal and stable under intersections. Shared source tags: 0218.

lem-a1-etale-open-restriction vs lem-trf-etale-fitting-trick: the new node states preservation under simultaneous compatible source and target open restrictions; the existing node states Fitting ideal factorization after an etale localization. It does not give this general restriction assertion. Shared source tags: 02GJ.

lem-a1-etale-open-restriction vs lem-weil-pbc-etale-local-on-source: the new node states preservation under simultaneous compatible source and target open restrictions; the existing node states Etaleness is local on the source. It does not give this general restriction assertion. Shared source tags: 02GJ.

lem-a1-etale-open-restriction vs lem-weil-pbc-descend-etale: the new node states preservation under simultaneous compatible source and target open restrictions; the existing node states Etaleness descends to a finite stage of a limit. It does not give this general restriction assertion. Shared source tags: 02GJ.

lem-a1-etale-open-restriction vs lem-weil-pbc-affine-chart-directed-ring-model: the new node states preservation under simultaneous compatible source and target open restrictions; the existing node states Coordinate-ring comparisons for one affine triple. It does not give this general restriction assertion. Shared source tags: 02GJ.

lem-a1-etale-open-restriction vs lem-weil-pbc-etale-ring-map-conormal-criterion: the new node states preservation under simultaneous compatible source and target open restrictions; the existing node states Etale ring maps: the conormal map of a finite presentation is an isomorphism. It does not give this general restriction assertion. Shared source tags: 02GJ.

lem-a1-etale-open-restriction vs lem-weil-pbc-etale-algebra-finite-presentation-localization: the new node states preservation under simultaneous compatible source and target open restrictions; the existing node states An etale algebra is finitely presented, and its principal localizations are etale. It does not give this general restriction assertion. Shared source tags: 02GJ.

lem-a1-etale-open-restriction vs lem-weil-pbc-etale-algebra-flat: the new node states preservation under simultaneous compatible source and target open restrictions; the existing node states An etale algebra is flat. It does not give this general restriction assertion. Shared source tags: 02GJ.

lem-a1-etale-open-restriction vs lem-weil-pbc-etale-ring-map-iff-etale-affine: the new node states preservation under simultaneous compatible source and target open restrictions; the existing node states Spec of a ring map is etale iff the ring map is etale (finitely presented with H_1 = 0 and Omega = 0). It does not give this general restriction assertion. Shared source tags: 02GJ.

lem-a1-etale-open-restriction vs lem-weil-pbc-etale-over-normal-ring-normal: the new node states preservation under simultaneous compatible source and target open restrictions; the existing node states An etale algebra over a normal ring is a normal ring. It does not give this general restriction assertion. Shared source tags: 02GJ.

lem-a1-etale-open-restriction vs lem-weil-pbc-etale-near-prime-naive-cotangent-vanishing: the new node states preservation under simultaneous compatible source and target open restrictions; the existing node states Vanishing of H_1 and of the differentials at a prime gives an etale localization. It does not give this general restriction assertion. Shared source tags: 02GJ.

lem-a1-etale-open-restriction vs lem-sc-etale-coproduct-etale: the new node states preservation under simultaneous compatible source and target open restrictions; the existing node states A finite coproduct of etale morphisms is etale. It does not give this general restriction assertion. Shared source tags: 02GJ.

Additional concept comparisons (even without identical source tags):

lem-a1-scheme-lqf-composition vs lem-trf-quasi-finite-composition: the existing theorem is about commutative ring maps. The new theorem is the scheme-local-to-global argument on compatible affine charts, using that ring theorem; it is not a ring-map specialization.

lem-a1-scheme-lqf-composition vs lem-sfb-stack-proper-locally-quasifinite-composition: the existing theorem assumes proper morphisms of Deligne–Mumford stacks. Arbitrary locally quasi-finite scheme maps in the new theorem need not be proper.

lem-a1-etale-affine-finite-fibre-refinement vs lem-weil-pbc-etale-covering-affine-refinement: the existing theorem supplies affine etale pieces, but says nothing about h, their composite maps to Z, finite fibres of those composites, or fibre finiteness downstairs. Those are the additional work assigned to the new node.

lem-a1-etale-affine-finite-fibre-refinement vs pqf-lem-qf-finitefibres: the existing equivalence concerns one morphism with quasi-compactness and finite-type conditions. It does not construct a finite affine refinement of a non-quasi-compact cover or descend fibre finiteness through it.

## Original argument retained for the extracted work

The following is the complete seven-step live proof used for the re-split, with its original citations. It is working material for the next workers, not proof steps on the statement-only nodes.

### Original step 1 (1438 characters)

Open restrictions of the etale map $p$ remain etale: let $A\subseteq U$, $B\subseteq V$ be opens with $p(A)\subseteq B$, and $x\in A$. Flatness at $x$ is unchanged, since the local-ring map $\mathcal O_{V,p(x)}\to\mathcal O_{U,x}$ is the same for $A\to B$. For local finite presentation, [def-sbc-locally-finite-presentation] for $p$ gives affine opens $x\in U'=\operatorname{Spec}A'$, $V'=\operatorname{Spec}R$ with $p(U')\subseteq V'$ and $R\to A'$ of finite presentation. Choose $r\in R$ with $p(x)\in D(r)\subseteq V'\cap B$ and $a\in A'$ with $x\in D(a)\subseteq U'\cap A\cap p^{-1}(D(r))$. Then $A'_a\cong A'[t]/(at-1)$ is finitely presented over $R$; the image of $r$ is a unit in $A'_a$, so $A'_a=A'_a\otimes_RR_r$ is the base change of $R\to A'_a$ along $R\to R_r$, hence finitely presented over $R_r$. These affine opens $D(a)\subseteq A$, $D(r)\subseteq B$ witness finite presentation of $A\to B$ at $x$; a finite presentation has finitely many generators, so $A\to B$ is also locally of finite type. The diagonal of $A\to B$ is the restriction of the diagonal of $p$ to the open $A\times_B A=A\times_VA\subseteq U\times_VU$, so it is an open immersion [def-weil-open-immersion]. Thus [def-weil-unramified-morphism] and [def-weil-etale-morphism] apply to $A\to B$. In particular $p^{-1}(B)\to B$ is etale; if $p$ is surjective it is surjective on points, since a preimage of a point of $B$ automatically belongs to $p^{-1}(B)$.

Uses: def-weil-etale-morphism, def-weil-flat-morphism, def-sbc-locally-finite-presentation, def-weil-unramified-morphism, def-weil-open-immersion.

Source: literature/stacks-project/morphisms.tex, Tag 02GI (definition-etale), open restriction; the point-local definitions and restricted diagonal give the argument explicitly.

### Original step 2 (914 characters)

Suppose $g$ is locally quasi-finite and fix $u\in U$. Choose an affine open $Z\subseteq T$ containing $g(p(u))$, an affine open $W\subseteq g^{-1}(Z)$ containing $p(u)$, and an affine open $A\subseteq p^{-1}(W)$ containing $u$. By [lem-a1-scheme-lqf-affine-criterion], the ring map $\mathcal O_T(Z)\to\mathcal O_V(W)$ is of finite type and quasi-finite at every target prime. By Step 1, $A\to W$ is etale, so [lem-weil-pbc-etale-ring-map-quasi-finite] gives the same two properties for $\mathcal O_V(W)\to\mathcal O_U(A)$. Apply [lem-trf-quasi-finite-composition] to these two ring maps. Functoriality of structure-sheaf pullback identifies their composite with the map for $A\to Z$. It is therefore of finite type and quasi-finite at the prime representing $u$. These affine neighbourhoods witness quasi-finiteness of $g\circ p$ at $u$ in [pqf-def-quasifinite]; doing this at every $u$ proves the first assertion.

Uses: lem-a1-scheme-lqf-affine-criterion, lem-weil-pbc-etale-ring-map-quasi-finite, lem-trf-quasi-finite-composition, pqf-def-quasifinite.

Source: literature/stacks-project/descent.tex, Tag 03X4, precomposition paragraph; its ring-map composition argument is Tag 00PO, using the affine characterization Tag 01TK.

### Original step 3 (457 characters)

For the converse assume $p$ is surjective and $g\circ p$ is locally quasi-finite. By [lem-weil-pbc-lqf-locally-finite-type], $g\circ p$ is locally of finite type. The definition [def-weil-etale-morphism] supplies flatness and local finite presentation of $p$. Hence [lem-a1-lft-flat-lfp-source-descent], applied to the triangle $U\xrightarrow{p}V\xrightarrow{g}T$, shows that $g$ is locally of finite type. This use does not require $p$ to be quasi-compact.

Uses: lem-weil-pbc-lqf-locally-finite-type, def-weil-etale-morphism, lem-a1-lft-flat-lfp-source-descent.

Source: literature/stacks-project/descent.tex, Tag 03X4, finite-type descent; Tag 02KL (lemma-flat-finitely-presented-permanence), locally-of-finite-type alternative, packages the same Tag 0367 affine descent and finite affine refinement for non-affine source covers.

### Original step 4 (523 characters)

Fix an affine open $Z\subseteq T$ and an affine open $W\subseteq V$ with $g(W)\subseteq Z$. Step 1 gives a surjective etale map $p^{-1}(W)\to W$. Apply [lem-weil-pbc-etale-covering-affine-refinement] to this singleton covering of the affine scheme $W$. Obtain finitely many affine open subschemes $A_1,\ldots,A_m\subseteq p^{-1}(W)$ whose images under $p$ cover $W$. Each $A_j$ is also an open subscheme of $U$. By [lem-weil-pbc-lqf-restriction-to-opens], $A_j\to Z$, the restriction of $g\circ p$, is locally quasi-finite.

Uses: lem-weil-pbc-etale-covering-affine-refinement, lem-weil-pbc-lqf-restriction-to-opens.

Source: literature/stacks-project/descent.tex, Tag 03X4, affine reduction expanded using Topologies Tag 0218 (lemma-etale-affine); Morphisms Tag 01TK, restriction to opens.

### Original step 5 (406 characters)

For each $j$, both $A_j$ and $Z$ are affine, so [lem-weil-pbc-morphism-affine-schemes-affine] says that $A_j\to Z$ is affine; [lem-weil-pbc-affine-morphism-permanence], clause (3), makes it quasi-compact. With its local quasi-finiteness from Step 4, [pqf-lem-qf-locqf-qc] implies that $A_j\to Z$ is quasi-finite. By [pqf-lem-qf-finitefibres], every set $(g\circ p)|_{A_j}^{-1}(t)$, for $t\in Z$, is finite.

Uses: lem-weil-pbc-morphism-affine-schemes-affine, lem-weil-pbc-affine-morphism-permanence, pqf-lem-qf-locqf-qc, pqf-lem-qf-finitefibres.

Source: literature/stacks-project/descent.tex, Tag 03X4, finite-fibres paragraph; Morphisms Tags 01SH, 01S7, 02NH and lemma-quasi-finite-locally-quasi-compact.

### Original step 6 (494 characters)

For $t\in Z$, the set $\{w\in W:g(w)=t\}$ is the union, over $1\le j\le m$, of the images under $p$ of $\{a\in A_j:g(p(a))=t\}$. Indeed, the image is contained in that set, and conversely the covering of $W$ by the $p(A_j)$ supplies a preimage of every such $w$, which necessarily maps to $t$. Each source set is finite by Step 5, so its image is finite and the finite union is finite. Thus $W\to Z$ has finite fibres. The same argument covers $m=0$: then $W$ is empty and every fibre is empty.

Uses: none (elementary finite-set argument).

Source: literature/stacks-project/descent.tex, Tag 03X4, finite fibres descend through the surjection; the finite affine refinement replaces its single affine source.

### Original step 7 (907 characters)

The restriction $g|_W:W\to Z$ is locally of finite type: [lem-weil-pbc-lft-affine-pairs] for $g$ from Step 3 gives the finite-type ring map for every pair of affine opens inside $W,Z$, so the reverse direction of that criterion applies to $g|_W$. Since $W,Z$ are affine, [lem-weil-pbc-morphism-affine-schemes-affine] and [lem-weil-pbc-affine-morphism-permanence](3) also make $g|_W$ quasi-compact. It is of finite type by [def-weil-finite-type-morphism]. Now [pqf-lem-qf-finitefibres], using Step 6, makes $g|_W$ quasi-finite, and [pqf-lem-qf-locqf-qc] makes it locally quasi-finite. Take an affine open cover of $T$ and, over each member $Z$, an affine open cover by such $W$ of $g^{-1}(Z)$. Condition (3) of [lem-a1-scheme-lqf-affine-criterion] proves that $g$ is locally quasi-finite. All finiteness was used only on these affine charts, so there is no global quasi-compactness or separation requirement.

Uses: lem-weil-pbc-lft-affine-pairs, lem-weil-pbc-morphism-affine-schemes-affine, lem-weil-pbc-affine-morphism-permanence, def-weil-finite-type-morphism, pqf-lem-qf-finitefibres, pqf-lem-qf-locqf-qc, lem-a1-scheme-lqf-affine-criterion.

Source: literature/stacks-project/descent.tex, Tag 03X4, conclusion using Morphisms Tag 02NH; Zariski gluing is Morphisms Tag 01TK, condition (3).

