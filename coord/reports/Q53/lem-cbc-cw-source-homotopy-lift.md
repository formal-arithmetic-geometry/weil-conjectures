# Worker report

1. Files written:
   - `dag/nodes/sec-smooth-purity/lem-cbc-cw-source-homotopy-lift.json`: existing statement, now split into five steps. No exact Mathlib match or project attachment found.
   - `dag/nodes/sec-smooth-purity/lem-cbc-weak-equivalence-relative-disk-extension.json`: one new statement-only lemma, unsplit; no Mathlib match after two semantic phrasings, Loogle, LeanSearch and source grep.
   - `citations.json`: verbatim statement excerpts for all three node-citation occurrences in the proof (step 2 and steps 3, 5).
2. Attachments: none. Searches by item id, CWComplex, Whitehead, weak homotopy and homotopy lifting in `WeilConjectures/` of slopmaster2 returned no project declaration. The separate master reference is not evidence of a completed proof and gave no matching declaration either. The original item has no `lean_audit` entry; this is treated as no recorded Lean, not as a closed proof.
3. WANTED: archived Kerodon Lemma 3.6.3.11 (0140), especially its single-cell mapping-path lifting square, and Remark 3.6.3.4 (013T), for both this item and the new relative disk lemma. The online sources were read, but no archive was downloaded or written to the project. These are Kerodon tags, not Stacks tags. There is no identified Stacks source for this topological argument.
4. What needed repair: the item was statement-only. Its existing statement agrees with Kerodon 0140, with the conventional weak-equivalence condition expanded by 013T. It was kept verbatim. The reference suppresses the quotient/product continuity checks in its skeletal induction; those now appear explicitly using the existing Mathlib leaf `lem-cbc-quotient-cylinder-continuity`. No statement dispute or route change was needed. The blueprint ancestry is provenance, not an assertion that the compact-support blueprint literally contains a CW lifting theorem.
5. Unfinished: only the single-cell relative disk lemma is new and unsplit, as required for a one-level split. Its role and exact boundary conditions are recorded in its own statement. Nothing was compiled, no Lean was written, and no shared project or launcher file was edited. Delivery is intentionally left to the second reader.

## Sources and route

I read the chapter and unit records, `sec-smooth-purity` and `sk-prop-sf-cbc`, and the current ancestor proof at `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/thm-cbc-finite-level-proetale.proof.md`. The preserved via chain runs through the parent Whitehead theorem and realization/mapping-space lemmas. The ancestor opens with the choice of a compactification; it contains no literal topological lifting argument. This split only expands the foundational lemma already installed below that route and does not replace a unit step.

For the item I read https://kerodon.net/tag/0140, including its proof, and for the new node I read the paragraph that prescribes a map on the cell boundary, its specified boundary homotopy, the displayed singular mapping-path lifting square, and the conclusion by trivial Kan lifting. I also read https://kerodon.net/tag/013T to verify the component/group hypotheses, https://kerodon.net/tag/0101 for the singular path fibration, and https://kerodon.net/tag/00X1 for its boundary-lifting criterion. The new node states precisely the *local* extension problem used in that proof, in Euclidean disk coordinates. Its source field explains this extraction and the simplex/disk reparametrization. It contains no proof sketch or assertion about arbitrary CW source spaces.

The future proof of that new node can follow the displayed square: singular complexes of arbitrary spaces are Kan, the weak-equivalence test in 013T gives the homotopy equivalence on singular complexes, the path factorization is a fibration and a homotopy equivalence, and its boundary fillers give the specified cell map and homotopy. This explanation is in the report rather than in the unsplit node. In particular I did not cite the existing realization-testing or Kan-fibration-criterion nodes: their current dependency paths lead back through this item, so that route would create a cycle.

## Mathlib reading

All new search records correspond to commands actually run with `msearch.py Q53 lem-cbc-cw-source-homotopy-lift`; each grep record includes its exact query and subdirectory. None of the services was unavailable. The earlier searches already in the item's file were retained, and my five additional item searches were appended. The nine searches for the relative disk lemma are recorded in the new node.

I read `Mathlib/AlgebraicTopology/ModelCategory/Homotopy.lean:130-166`: postcomposition bijectivity assumes a model category, cofibrancy and fibrancy. It is not a one-line specialization to the arbitrary topological spaces in this item. `RightHomotopy.lean:183-191` is the abstract homotopy extension theorem, with a cofibration and good path object, not the required conclusion for a topological weak homotopy equivalence. `Topology/CWComplex/Abstract/Basic.lean:35-78` defines relative cell complexes and even records the still-missing comparison with the classical definition. These hits do not justify a Mathlib leaf.

For the new lemma I also read `Topology/Homotopy/Basic.lean:153-177`: `Homotopy.extend` clamps the time coordinate to the unit interval. It does not extend maps over cells. `Topology/Category/TopCat/Sphere.lean:43-64` defines the disk inclusion only. `Topology/Homotopy/Lifting.lean:171-176,218` requires a local homeomorphism or covering map. Those extra hypotheses cannot be imposed on the arbitrary weak equivalence here.

The existing leaf used by this split was independently checked at `Mathlib/Topology/CompactOpen.lean:584-598`. Its variables allow arbitrary topological source, quotient and target spaces; only the extra product factor must be locally compact. It says exactly that continuity after pulling back along the quotient times the identity implies continuity. Its ordinary product topology is the one needed here.

## Not duplicates

lem-cbc-weak-equivalence-relative-disk-extension vs lem-cbc-cw-source-homotopy-lift: the new lemma extends *specified boundary maps and specified boundary homotopies* across one finite-dimensional disk, fixing those data exactly; the item gives only an unrestricted lift up to homotopy for an arbitrary CW complex. The induction and the two gluing arguments remain in the item. The new lemma is not one of its stated clauses.

lem-cbc-weak-equivalence-relative-disk-extension vs lem-cbc-whitehead-cw-homotopy-inverse: Whitehead assumes CW homotopy type on both spaces and produces an inverse. The new lemma assumes no CW property on either space and concerns a single relative cell. The parent cites 0140 in its proof; it cannot be used below its own lifting input.

lem-cbc-weak-equivalence-relative-disk-extension vs lem-coef-serre-disk-lift-boundary-bijection: that existing node concerns a map already known to be a Serre fibration, a horn-fixed lift and the connecting-map bijection under a based contraction of the total space. The new lemma concerns an arbitrary weak equivalence, a prescribed entire sphere homotopy and no contraction or fibration hypothesis.

lem-cbc-weak-equivalence-relative-disk-extension vs lem-coef-sphere-mapping-weak-equivalence: that node concerns weak equivalence of compact-open sphere mapping spaces, not extension of a disk together with its fixed boundary homotopy. Its statement alone does not give the relative filler.

lem-cbc-weak-equivalence-relative-disk-extension vs lem-coef-model-right-homotopy-extension: the existing Mathlib leaf concerns abstract cofibrations and fibrant targets with a good path object. It supplies no realization of these hypotheses for arbitrary topological weak equivalences.

lem-cbc-weak-equivalence-relative-disk-extension vs lem-coef-space-path-fibration-replacement: the existing node factors maps of Kan simplicial sets and identifies their fibres. It does not give the continuous disk/sphere relative lifting conclusion for arbitrary topological spaces.

DAG searches covered the whole graph with `--hidden --no-ignore`, not only the target reach. The `0140` source match is the item itself; the Whitehead parent also discusses it. Other raw occurrences of that numeric substring are search digests or unrelated longer identifiers, not citations of this topological source. Whole-blueprint searches by CW, disk, 0140, homotopy extension and relative disk found no existing blueprint statement for the new lemma. The broad homotopy search was also read. No new definition or elementary gluing node was created.

The first dry run also flagged eleven numeric-tag collisions: Kerodon 013T in the new source field is unrelated to Stacks 013T. I opened and read every flagged statement. The following pairs record the distinction explicitly.

lem-cbc-weak-equivalence-relative-disk-extension vs lem-pc-abelian-cech-comparison-boundary: the existing statement is compatibility of Cech/sheaf-cohomology comparison maps with connecting homomorphisms, not extension of a sphere map and its boundary homotopy across a disk.

lem-cbc-weak-equivalence-relative-disk-extension vs lem-pc-abelian-cech-augmentation-boundary-squares: the existing statement constructs a homomorphism on total homology compatible with Cech and Ext boundary squares, not a continuous relative disk filler.

lem-cbc-weak-equivalence-relative-disk-extension vs lem-sp-horseshoe-prescribed-resolutions: the existing statement builds an injective resolution of the middle object of a short exact sequence with prescribed end resolutions; its objects are complexes in an abelian category, not topological spaces.

lem-cbc-weak-equivalence-relative-disk-extension vs lem-sp-cartan-eilenberg-rows-exists: the existing statement constructs a compatible injective row system for a cochain complex, not relative disk extensions.

lem-cbc-weak-equivalence-relative-disk-extension vs lem-sp-horseshoe-prescribed-row-construction: the existing statement constructs a cochain complex with exact rows and prescribed augmentation components; it has no disk, sphere or continuous-homotopy assertion.

lem-cbc-weak-equivalence-relative-disk-extension vs lem-sp-cartan-eilenberg-object-resolution-rows: the existing statement constructs injective resolutions of cycles, boundaries and homology with exact rows; the new statement instead extends specified continuous boundary data.

lem-cbc-weak-equivalence-relative-disk-extension vs def-sp-cartan-eilenberg-boundary-projection: the existing node defines image and kernel factor maps of a cochain differential; the new node is an existence theorem about maps of topological disk pairs.

lem-cbc-weak-equivalence-relative-disk-extension vs lem-weil-pbc-pushout-short-exact-sequence: the existing statement proves exactness after an abelian-category pushout; it does not concern a weak homotopy equivalence or a continuous homotopy.

lem-cbc-weak-equivalence-relative-disk-extension vs lem-weil-pbc-horseshoe-defect-factorization: the existing statement factors defects of maps between horseshoe resolutions and proves four chain-map identities; it has no topological disk extension content.

lem-cbc-weak-equivalence-relative-disk-extension vs lem-weil-pbc-horseshoe-delta-functor: the existing statement proves naturality and exactness of right-derived functors using horseshoe connecting maps; it is not the topological homotopy extension lifting property.

lem-cbc-weak-equivalence-relative-disk-extension vs lem-weil-pbc-injective-resolution-ses-complexes: the existing statement replaces a degreewise short exact sequence of complexes by injective complexes with exact rows; no continuous disk or sphere occurs.

## Review by Q53

I checked the statement hypothesis by hypothesis against 0140 and 013T. The map is a weak equivalence on all components and at every source basepoint. The CW assumption is only on the mapping source. Homotopies are unbased, and their direction is from the composite lift to the original map. Both the item and the new node allow empty spaces. I retained the item text exactly, including its inline CW convention and its explicit endpoint equations.

For step 1, the induction invariant specifies exact restriction of both the map and its homotopy; the empty skeleton is an actual base case. This is an instance of the CW construction already defined in the item's statement, with no unmentioned theorem. For step 2, I opened the new node and checked that it takes exactly the three maps actually available: the boundary lift, the disk map into B, and the *already chosen* boundary homotopy. The two endpoint equalities follow by restriction of the invariant. Every hypothesis on w is already in the item. This is stronger boundary control than merely lifting a disk up to some homotopy, which would not suffice for the induction.

For step 3, I opened `lem-cbc-quotient-cylinder-continuity` and verified its statement against the application: q_n is the quotient of the attaching construction, I is its locally compact extra factor and B is the arbitrary target. Agreement at every boundary identification follows from the two exact restriction clauses of the new lemma. The proof spells out why the maps on the coproduct are continuous, and why their pointwise descents are well-defined; it does not assume that an arbitrary infinite closed cover permits pasting. Endpoint identities descend by surjectivity. For step 4, exact compatibility gives well-defined maps on the union and their displayed restrictions on every characteristic disk. For step 5, the full coproduct q is a quotient by the weak-topology clause of the CW definition, and the same leaf gives continuity of the final homotopy in the ordinary product. This is the second occurrence of that citation, and it has a separate entry in citations.json. All cited quotes were copied verbatim from statements, not from their proofs. The proof dependency list equals the union of uses. There are no off-unit non-Mathlib theorem citations.

I tested the new statement at n=0: the boundary is empty, and surjectivity on path components supplies a point of A and a path to the prescribed point of B. At n=1 the boundary is two points and its two homotopies must be kept, which is exactly what the statement requires. For w the identity of an arbitrary space, the data extend by using the supplied homotopy on a collar and the disk map on the inner disk; thus it does not accidentally force every sphere map to extend. If A is empty, bijectivity of components forces B empty. Since D^n is nonempty for every n, the required beta then does not exist, so the implication is vacuous rather than a false nonemptiness assertion. If K is empty, the item's empty maps solve the problem. If K is a point, the item reduces to the n=0 case. Disconnected CW complexes require independent choices on their zero cells and cause no extra hypothesis. Infinitely many cells of a fixed dimension and unbounded dimension are handled by quotient topology, not by a finite-pasting claim. The covering R to S^1 was checked as a tempting false generalization: it lacks the pi_1 isomorphism and is correctly excluded.

Against delivery-errors B1-B10: the new node has a self-contained statement only, no proof or dependencies of a hidden proof, all required notion data inline or cited, single-escaped TeX, truthful source identifiers, exact recorded searches and complete blueprint ancestry. No Mathlib hit was promoted without its hypotheses. Against C1-C8: the only non-elementary local extension is a cited node, the only non-elementary continuity tool is a cited existing Mathlib leaf, all applications use their statements, and the circular realization/Whitehead candidates were excluded. Against D1-D5: the split carries the compatible induction and gluing, and its one new node is the strictly local relative-cell problem, not the CW-source conclusion with a different name. Against E1-E7: the hypotheses, objects, boundary conditions and empty cases were checked above; no false source assertion or silent statement correction was found. The correction during my self-check was to make both product-continuity applications explicit rather than leaving the final infinite gluing implicit.

Dry-run repair: I added the eleven pairwise explanations above after reading each statement flagged by numeric-tag collision. No node statement, proof step, hypothesis or citation needed alteration.

## Second reading by Q53

- Item statement: checked hypothesis by hypothesis against Kerodon 0140 and Remark 013T; verdict: agrees, including empty and disconnected cases.
- Step 1: checked the skeletal induction invariant and empty base case against 0140; verdict: elementary and complete.
- Step 2: checked the characteristic and boundary maps against the relative disk node and 0140; verdict: all domains, endpoint restrictions, and the $n=0$ case agree.
- Step 3: checked attaching quotient, boundary agreement, and cylinder continuity against `lem-cbc-quotient-cylinder-continuity`; verdict: cited statement supplies exactly the needed locally compact interval argument.
- Step 4: checked compatible definitions on the union against the induction invariant; verdict: elementary and well-defined.
- Step 5: checked the global characteristic-map quotient and product continuity against the same Mathlib leaf; verdict: cited statement applies to the full coproduct quotient.
- New node `lem-cbc-weak-equivalence-relative-disk-extension`: checked self-contained B1-B7 form, Kerodon 0140's single-cell assertion, all small cases, duplicate searches, and Mathlib searches; verdict: valid strict sublemma, statement-only, no exact Mathlib match.
- Citations: reread every quoted node statement and compared it with its use; verdict: quotes are verbatim and `proof_deps` is exact.
- Changes made: corrected step 2's boundary endpoint to the typed expression `\\beta_e|_{S^{n-1}}(s)` and appended this second-reading audit; no mathematical route or statement was weakened.
