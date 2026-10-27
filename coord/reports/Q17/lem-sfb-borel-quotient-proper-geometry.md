## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-borel-quotient-proper-geometry.json: the item, now split into seven complete steps; its mathematical statement is unchanged. The item is not a Mathlib leaf.
- No new nodes and no Mathlib leaves. All geometric and representation-theoretic inputs already have nodes.
- citations.json: one entry for each step/node pair, quoting the cited statement verbatim. Whole statements are retained where a step uses several clauses.
- searches.jsonl: searches executed with the required msearch.py command. The script-generated log is unchanged.

## Attachments

None. I searched lean/WeilConjectures by the blueprint id, Borel/borel, homogeneous quotient, and quotient homogeneous. There is no declaration there stating the item. The hits concern graded polynomials and fraction constructions. Regular.lean contains regularity tools, not a homogeneous quotient or Borel properness theorem. Its existing DAG nodes are reused, not claimed as an attachment of the item.

## WANTED

None for this split: Milne iAG2017 and the relevant Stacks source files are available locally. The existing orbit-geometry node cites a corrected 2022 edition not locally present, but I read the orbit lemma and quotient-orbit statements in the available 2017 edition (1.66 and 7.11--7.12) used here.

## Corrections and scope

There was no proof in the item and no prior split/report in the sandbox. I copied the live item and retained its statement, citations, searches and origin metadata. The new proof follows the actual proof of Milne 17.9, rather than creating another node saying that Borel quotients are proper. The smooth projection is established separately by its kernel pair and fpqc base descent; smoothness of X uses flat source descent. Quotient uniqueness also explicitly supplies the separated finite-type geometry, rather than assuming it for an arbitrary map.

The source's Proposition 7.15 has the direction of the smoothness arrow reversed in one sentence; its cartesian square, proof and the final “in particular” give the correct assertion G -> G/H. The split uses that assertion, with its descent argument written out. The imported item's statement is correct and needs no STATEMENT-DISPUTED correction.

The chapter and unit were read, as were the current latest blueprint unit and the ancestry recorded in the item. This is the existing supporting algebraic-group input under the direct-image alteration route; no chapter/unit route is changed, and this is not the unit's key node. The ancestor command returns null, matching the inherited blueprint.from.node; its detailed from.place is already specified and is retained.

## Not duplicates

No new nodes. The whole DAG and blueprint were searched for Borel, homogeneous quotient and flags before selecting inputs. In particular, the existing solvable-subgroup-flag-realization is precisely the representation/flag input to Milne 17.9, and the existing smooth-group-orbit-geometry and homogeneous-orbit-quotient-geometry supply distinct orbit facts. The more general general-borel-flag-variety was deliberately not used as a black box to restate this item's properness clause.

## Review by Q17

I read Milne iAG2017 at printed pp.104--105 (quotient uniqueness, kernel pair, faithful flatness, torsor), pp.142--143 (the quotient projection square and smoothness), pp.146--147 (flags and projectivity), p.27 (orbit-boundary dimension), pp.352--354 (solvable fixed points and the full proof of 17.9). For regularity and field extensions I read Stacks varieties.tex, lemma-separably-closed-field-connected-components (0363), lemma-smooth-regular (056S), and the relevant smooth descent statements in descent.tex (02VL, 05B5). The proofs below use these sources through existing statement nodes. There are no new node sources to review.

I opened every cited node and checked its statement against the step, rather than relying on its title or its proof.

1. The homogeneous quotient node gives a separated finite-type quotient, the all-test-scheme coset equivalence and fpqc-local lifts. The representable fpqc descent node gives exactly gluing and uniqueness of compatible scheme morphisms. These suffice to compare the given quotient with that quotient, descend left multiplication and identify the kernel pair. The inverse ratio lands in H on every test scheme; this is stronger than checking geometric points and rules out a hidden infinitesimal-kernel issue. This is marked elementary relative to the two cited statements because the maps, compatibility, inverse and naturality are written out.
2. The smooth base-change clause of lem-pc-proper-base-change makes G x H -> G smooth. The fpqc base-descent node requires flatness, quasi-compactness and surjectivity of p, all given. The source-descent node instead requires flatness, surjectivity and local finite presentation of p, also given; it applies to the factorization of the already smooth structure map of G. Thus no claim about descent of smoothness along an arbitrary surjection is used.
3. The separably closed field node applies since F is algebraically closed; it supplies nonempty connectedness after all field extensions. Smooth base change plus the smooth-over-field regularity node and regular-connected-integral node give integrality at every extension, including transcendental extensions. Connectedness of X is proved by pulling back clopen sets along p. The finite-type-over-Noetherian statement applies over Spec F, and gives the stated global Noetherian conclusion, not merely local Noetherianity. I checked that the regularity node includes local Noetherianity, as required by regular-connected-integral.
4. Surjectivity and finite type survive the fibre base change by the two cited permanence nodes. Jacobson density gives a closed point in the nonempty finite-type Omega-fibre; the residue-field node makes it rational because Omega is algebraically closed. Translation and the kernel pair give an actual isomorphism of schemes with H_Omega. The algebraically closed extension criterion therefore proves geometric connectedness of each original residue-field fibre. The smooth-connected-fibre-integrality node applies to p with exactly these hypotheses and gives all extensions L/kappa(x). An L-rational point is never assumed.
5. The dimension-finiteness and affine dimension-drop statements bound the candidate subgroup dimensions. Step 3 supplies the integral affine variety hypothesis of dimension drop for G. The identity subgroup ensures that the set of dimensions is nonempty. The existing flag-realization node gives both the exact scheme-theoretic flag stabilizer B0 and the smooth connected solvable reduced identity subgroup of every other flag stabilizer with unchanged dimension. This latter clause is essential in positive characteristic; I did not assume that arbitrary flag stabilizers are smooth.
6. Projective-proper supplies separatedness of the flag scheme for the orbit lemma. The action on flags is specified by image of subbundles. The orbit statement gives the dimension formula and strictly smaller boundary orbits, while flag-realization bounds every stabilizer dimension by d0. A hypothetical boundary has an F-rational point by the cited Jacobson and residue-field statements, so the smaller-orbit contradiction is justified. The closed reduced orbit is proper by the explicit flag-realization clause, and the homogeneous-orbit node identifies it with G/B0 and supplies rational lifts. This proves properness first for B0 of maximal dimension, not for every Borel by assertion.
7. The fixed-point node applies to a smooth connected solvable H acting on the nonempty proper finite-type orbit. It gives a scheme-theoretic fixed point, so the resulting inclusion H <= g B0 g^-1 holds on all algebras. The given maximality, not any dimension assumption on H, turns this into equality. The two coset maps are written out with their change-of-representative formulas and descended using the exact gluing statement. Their inverse identities establish the needed isomorphism and hence properness of the given X.

I checked B--E of delivery-errors against the actual files. B: no undeclared new statements, proof sketches inside statements, invented sources or fabricated searches; the source metadata and imported statement are retained. C: all 27 step citations have verbatim evidence in citations.json; the two base changes, smooth source/base descent, field criterion, regularity, Noetherianity, rational-point existence, projective separatedness, dimension control and quotient-orbit identification are explicit node citations. Off-unit uses are declared as generic tools in split_report.tool_uses, without setting the maintainer's tool_uses field. D: no clause was moved into a new node and no conclusion is assumed; the minimum-orbit argument is carried by steps 5--6. E: I checked fields, residue fields, closed versus rational points, all-test-scheme stabilizers and the direction of every quotient map. I also traversed the chosen input dependencies and found no path back to the item. No non-elementary step exceeds 2000 characters.

Edge cases: G=1 and G=H give Spec F, including a zero-dimensional flag space. H=1 for G=Ga gives an affine nonproper quotient, correctly outside the conditional maximal-solvable clause. A connected nonsmooth subgroup alpha_p in characteristic p is excluded: its Frobenius quotient is not smooth, showing why H smooth is needed. A disconnected smooth subgroup can give disconnected fibres, showing why H connected is needed. For an L-valued torsor fibre with no L-point, the proof chooses a point only after algebraic closure and descends geometric connectedness, so it does not wrongly trivialize over L. No reductivity or characteristic-zero assumption was inserted.

## Unfinished work

None at the natural-language split level. The reused unsplit inputs remain their own DAG items. No Lean was written and no compiler, Lake or build tool was run.

## Validation

The required deliver.py --no-push command exited successfully: OK (not pushed) at 915078d1b50, server preflight passed. It checked the DAG, split, citations and delivery packaging. The final push uses the same sandbox proof.
