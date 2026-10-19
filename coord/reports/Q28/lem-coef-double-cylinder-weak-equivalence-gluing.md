# Stage-1 report: lem-coef-double-cylinder-weak-equivalence-gluing

Group Q28; direct delivery; 2026-10-18.

## Files written

- `dag/nodes/sec-six-functors/lem-coef-double-cylinder-weak-equivalence-gluing.json`: existing statement, now split into six proof steps. The mathematical statement and statement dependencies are unchanged. Not a Mathlib leaf.
- `dag/nodes/sec-six-functors/lem-coef-open-cover-weak-equivalence.json`: new statement-only lemma for binary open covers of arbitrary topological spaces; unsplit, no Mathlib match.
- `citations.json`: verbatim statement evidence for every step's `uses` entry.
- `report.md`: this report. `searches.jsonl` was produced by msearch.py; `prepare.py` is sandbox-only preparation code, not a DAG delivery file.

One new node, zero Mathlib leaves. No unit or chapter file was changed.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint item tag, double/mapping cylinders, and weak-equivalence gluing produced no declaration stating this item. The upstream master source likewise has no double-cylinder declaration. Nothing was compiled and no Lean file was written.

## WANTED

WANTED: J. P. May, *A Concise Course in Algebraic Topology*, Chapter 10 section 7, final theorem and proof, printed pp. 80-82, for lem-coef-open-cover-weak-equivalence and the present item's open-cover argument. I read the author's online PDF at https://www.math.uchicago.edu/~may/CONCISE/ConciseRevised.pdf but no archival copy is present in the named literature tree. I did not download a document.

WANTED: an archived reference explicitly asserting the binary-open-cover weak-homotopy-equivalence gluing theorem for arbitrary topological spaces, without weak Hausdorffness or compact generation, for lem-coef-open-cover-weak-equivalence. May's Chapter 5 adopts compactly generated weak Hausdorff spaces; his Chapter 10 theorem is therefore a related reference, not a verbatim source for all the hypotheses of this new node. The node's source explicitly labels the arbitrary-space formulation as agent-supplied. Its later split can use the small-singular-simplex/subdivision argument on finite disks and their homotopies; that argument only uses open inverse-image covers of finite polyhedra. No Stacks tag for this homotopical assertion was found; I have not invented one.

## Problems found and corrections

The input is a true, self-contained statement but has no proof. It includes arbitrary topological spaces, so using the existing Serre model node (which assumes k-spaces), or merely quoting May under his global compact-generation convention, would miss its hypotheses. I retained the arbitrary-space statement and isolated exactly the requisite arbitrary-space open-cover theorem. The explicit exponential-law argument in Steps 3-4 avoids assuming that a product with an arbitrary parameter preserves quotient maps: only the locally compact interval is used, through the existing compact-open currying node.

The blueprint ancestor's Paragraph 2 is a derived-coefficient-adjunction calculation. I read its current main-20261015 proof in full. It supplies the use context for this long imported technical branch, not a proof of this topological lemma; the item's proof_origin is accordingly agent. I also read the chapter and sk-prop-sf-biduality-general unit records. This is a technical input below their route, and neither their statements nor their realization records are altered.

The existing item's older Mathlib searches were retained. I added only actual new searches from the msearch.py log, including two semantic phrasings for the item and two for the new node, Loogle and source grep. I read the generic Cylinder source and TopCat.GlueData source returned by the services. Generic model-category cylinder declarations assume an abstract weak-equivalence structure and do not instantiate the desired topological result. openCoverGlueHomeo, at Mathlib/Topology/Gluing.lean:430, says an ordinary open cover glues back to the space; it does not assert that maps which are weak equivalences on patches are globally weak equivalences. These hits are not one-line specializations of either statement.

## Not duplicates

lem-coef-open-cover-weak-equivalence vs lem-coef-double-cylinder-weak-equivalence-gluing: the new node concerns any continuous map with a binary target open cover. It says nothing about quotient cylinders, endpoint maps, functoriality, or retractions. The item's Steps 1-5 construct its map and cover and prove all three local hypotheses, rather than restating a clause as a new node.

lem-coef-open-cover-weak-equivalence vs lem-coef-sset-gluing-filtered-equivalences: the existing node is about degreewise pushouts of simplicial sets along monomorphisms and filtered colimits, not ordinary open covers of arbitrary topological spaces. A comparison of small singular simplices with a whole space would be additional mathematics, not a one-line specialization.

lem-coef-open-cover-weak-equivalence vs lem-coef-topological-serre-model: the existing node gives a model structure on k-spaces; it does not assert the open-cover criterion for arbitrary spaces.

lem-coef-open-cover-weak-equivalence vs lem-coef-homotopy-equivalence-weak: the existing node converts an explicitly supplied homotopy inverse into a weak equivalence. Local weak equivalences do not supply homotopy inverses, so that node does not give the new gluing theorem.

The full-DAG statement search for weak equivalences together with open/cover/excisive terminology and the blueprint_refs searches for weak homotopy equivalence, excisive, mapping cylinder and open cover weak found no duplicate. No new node carries a Stacks tag, so there are no same-tag pairs to explain.

## Review by Q28

I checked the split against delivery-errors B-E with the item, all four cited statements and the blueprint context open. The new node introduces its own arbitrary spaces, map, open subsets, subspace topologies and weak-equivalence convention; it has no proof, no proof dependencies and no disguised proof sketch. It depends on the convention node rather than on the item, so there is no cycle through its statement. No new definition is required: all extra terminology is defined inline. It is a genuine general gluing theorem, not an elementary retraction calculation or a renamed cylinder clause.

Step 1 uses only the quotient universal property and the two commuting equations already in the item. I checked the images of both generators of the equivalence relation, and checked the identity and composition laws on each representative. Continuity descends from a map on the disjoint union.

Step 2 uses no black-box fact: the displayed truncated-cylinder preimages are saturated and open. I explicitly wrote why the restricted quotient is quotient. The overlap is a homeomorphic copy of the open interior cylinder because it has no identifications; this rules out an unjustified identification of subspace and quotient topologies. Endpoint identifications cannot cross into the other endpoint summand. The coordinate formula also proves the exact inverse-image cover identities needed by the new theorem.

Steps 3 and 4 cite lem-coef-compact-open-currying. Its statement gives both the transpose and continuous evaluation for arbitrary A and Z with locally compact K. Here K is always the usual compact Hausdorff interval, so its hypotheses hold. Each deformation is defined continuously on the disjoint-union source times I, has identical paths on equivalent representatives, descends after transposing, and is then evaluated. The left deformation decreases t toward 0 inside [0,2/3); the right increases it toward 1 inside (1/3,1]. The middle deformation stays inside (1/3,2/3). Retractions are identity on the endpoint or middle sections. The primed construction is the same argument for the second given span. These steps contain explicit routine formulas, not a hidden general quotient-product lemma.

Step 5 cites lem-coef-homotopy-equivalence-weak, whose statement explicitly permits arbitrary spaces, nonstationary basepoints and empty spaces. The actual retractions have the continuous inverse maps and homotopies required by that statement. The three retraction squares commute strictly, since e_A f=f' e_C and e_B g=g' e_C. I checked the basepoints of the induced group equation: both right-hand target basepoints are literally equal. Cancelling isomorphisms at each source point and bijections on components therefore proves each restriction is a weak equivalence. This cancellation is elementary and does not silently use a separate change-of-basepoint theorem.

Step 6 cites lem-coef-open-cover-weak-equivalence. Its statement assumes precisely three inverse-image restrictions for a target binary open cover; Step 2 gives that cover and the inverse images, and Step 5 gives each hypothesis. It explicitly allows the topology and emptiness generality needed here. No other non-elementary input is taken from its proof or merely from a reference name.

For small cases I checked C empty (disjoint union A and B), an empty A or B (forcing C empty), both endpoint spaces points (unreduced suspension of C), and the point-to-point span (an interval). A weak equivalence from an empty space forces the target empty by the component bijection, so there is no concealed basepoint argument in those cases. The general open-cover node also passes the trivial-cover test U=Y, V empty and the empty-overlap/disjoint-union test. No connectedness or separation assumption enters any retraction or cancellation. Each non-elementary step is under 2000 characters; the only newly postponed assertion is the independent open-cover theorem. I found no statement dispute and changed no target or imported assertion. No prohibited source was used.

## What remains unfinished

The new general open-cover lemma is deliberately unsplit, as required for a one-level stage-1 delivery. Its exact arbitrary-space reference is WANTED above. The item itself has a complete proof relative to that cited statement and the two existing tool statements. Required server dry run and push results are reported by deliver.py.
