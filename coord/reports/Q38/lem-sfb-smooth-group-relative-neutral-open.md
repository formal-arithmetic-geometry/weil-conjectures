# Q38: lem-sfb-smooth-group-relative-neutral-open

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-group-relative-neutral-open.json: statement split in six steps; no full Mathlib match.
- citations.json: one verbatim statement quotation for each of the 17 step/node citations.
- report.md and searches.jsonl: review and actual search records. prepare.py is sandbox-only working material.

## New nodes

None. In particular, no new lemma restates a clause of the item. The general section-component results already exist in the DAG and are used directly.

## Attachments

None. I searched lean/WeilConjectures/ by the blueprint tag and by relative/neutral/identity-component terminology. GroupScheme/Basic.lean supplies identity components over fields; its Over(Spec k) hypotheses do not provide the relative trait statement. The item has no exact finished project declaration found by these searches. Mathlib searches were run through msearch.py with two semantic phrasings, Loogle, LeanSearch and source grep. They returned ordinary topological-group connected components, openness of smooth loci, and universally open morphisms. None constructs the relative subgroup scheme. Their actual records were appended to the inherited item searches.

## WANTED

WANTED: Bosch–Lütkebohmert–Raynaud, Néron Models, section 6.4, paragraph following Proposition 2, printed p.154, for the item's original bibliographical source. Its named PDF is absent locally. I did not rely on the unexamined scan or EGA quotation: the proof is an agent assembly from the locally available Stacks sources and existing DAG statements. No SGA source is used.

## What changed and why

The imported item was statement-only. Its statement is unchanged, including separatedness, finite type, every geometric fibre, arbitrary scheme base change, and absence of a commutativity assumption. I constructed the open as the union of fibre components through the identity section. Unlike a split consisting of a new relative-neutral-component theorem, the steps supply the passage from this locus to an actual group scheme. The blueprint ancestry tool reports null for the inherited auxiliary chain; I retained that null and its via list, supplied an explicit place in the direct-image alteration/Picard auxiliary chain, and searched all blueprint nodes for neutral/identity components and section components. The existing field algebraic-group blueprint statements do not state this relative assertion. I also read the current latest blueprint unit and direct-image proof: this auxiliary construction leaves its route unchanged.

The word “orbits” is read in its usual scheme-action sense: each component is a coset subscheme, with its full open-subscheme structure. On algebraically closed rational points this is the ordinary orbit statement. One must not interpret it as transitivity of rational translations on all underlying scheme points: a translation preserves whether a point is closed, for instance in the additive group. Step 6 supplies the precise coset isomorphism and checks the side of the multiplication action, without assuming commutativity.

## Not duplicates

No new nodes, so there are no new/existing same-tag pairs to distinguish. The item itself is not a duplicate of lem-sfb-locally-algebraic-group-identity-component or lem-sfb-group-neutral-component-translates: both are over an algebraically closed field. lem-trf-flat-reduced-section-component-open and lem-sbc-section-component-cartesian concern general schemes with a section; they do not furnish restricted group operations. The Néron-neutral-local-properties node assumes an existing commutative Néron model, which the present statement does not assume. I cite the existing general tools instead of recreating any of them.

## Review by Q38

I read coord/delivery-errors.md B–E, the item and its chapter/unit, and the cited statements themselves. For the mathematical source I read more-morphisms.tex's entire “Connected components meeting a section” section: Tag 055M (lemma-base-change-connected-along-section), Tag 055R (lemma-connected-along-section-open), and the proof's hypotheses in 055Q. I read Tag 057I (lemma-descent-connected-fibres), especially its last paragraph deriving quasi-compactness of the section locus over an affine base. I read varieties.tex Tag 04KV and groupoids.tex Tag 0B7R, as well as the smoothness lemmas in morphisms.tex. There are no new-node sources to audit. I corrected two draft source labels against tags/tags: 057I is lemma-descent-connected-fibres and base change of a closed immersion is 01QR.

Step 1 uses exactly the smooth criterion (flat and locally finitely presented), the finite-type definition (quasi-compact), separated-implies-quasi-separated, the finite-presentation convention, and smooth-geometrically-reduced. Each cited statement actually supplies that assertion. In particular smoothness alone is not silently treated as global finite presentation: the quasi-compact and quasi-separated hypotheses are checked separately.

Step 2 applies the existing openness and quasi-compactness statements to the identity section. Flatness, full finite presentation and geometric reducedness are established in Step 1. The affine-base hypothesis of the quasi-compactness node is satisfied by Spec C. The open-immersion definition gives the actual restricted structure sheaf; no reduced-subscheme replacement is made.

Step 3 uses the arbitrary cartesian-square section-component equality, not a theorem merely about flat or finite-type base changes. Its sole local-finite-type hypothesis is already part of the item's finite-type assumption. The definition of base change supplies the fibre-product and section universal properties. The rational-point geometric-connectedness node is applied to U_s only after its connectedness and the factorization of e_s have been established. The open structures agree, so this is scheme base change, not just an equality of point sets.

Step 4 uses the existing locally algebraic identity-component theorem over an algebraic closure of each source point's residue field. Its algebraic-closedness and local-finite-type hypotheses are verified, the latter by the affine tensor-product presentations. A geometric point over every ordinary source point tests inclusion of the image in an open. This avoids the invalid substitution of an ordinary topological-group theorem for a group-scheme theorem. Once inclusion is established, restricting the continuous and sheaf maps gives unique factorization through the open, and monicity gives all group identities. The text includes these arguments rather than hiding an extra lemma. This step is 1302 characters, not an oversized proof hiding a new abstract comparison.

Step 5 uses open-immersion smooth composition and closed-immersion base change. The diagonal pullback is the actual U/S diagonal: its domain is U, not G. The local finite-type argument uses principal restrictions of the original affine charts. For quasi-compactness over each affine open of the affine base, a finite principal cover and the finite affine cover of U give a finite union of affine principal preimages. Thus finite type follows from the definition and Step 2's quasi-compactness. No unproved Noetherianity assertion is needed.

Step 6 uses the component-translation node over the algebraically closed field of the geometric point. Finite type follows from tensoring the finite affine presentations, and no reducedness is required by this node. It gives left-coset component isomorphisms. For the actual left action of G^0 the orbit is a right coset, so I checked right translation separately: it is an automorphism with inverse translation by g inverse, hence sends the maximal connected identity component to the component of g. This resolves the possible left/right mistake for noncommutative groups. The group identities already proved in Step 4 justify the elementary translation inverse calculation.

All off-unit nondefinition tools are declared in split_report.tool_uses, with their exact roles. Every proof use is a proof dependency and has a verbatim quote in citations.json. No statement dependency is introduced by a proof-only object. The new proof has no null elementary markers and no step longer than 2000 characters. There is no new node for an elementary open restriction, an affine finite-generation calculation, or a clause of the conclusion.

I checked the trivial group, a finite constant group, the additive group, a smooth connected noncommutative group, and disconnected smooth groups: the construction respectively gives the whole group, the identity copy of S, the whole additive group, and the expected neutral open. The identity section makes the neutral fibre nonempty. No perfect residue field or henselian/excellent DVR hypothesis is used. Arbitrary non-Noetherian and nonreduced T are allowed in Step 3 because the cited compatibility theorem explicitly allows any cartesian square. The open need not be closed globally, even though each field-fibre neutral component is closed. Infinitesimal nonsmooth group schemes do not meet the smoothness hypothesis and are not incorrectly inferred to have an open relative identity component by this proof.

## Unfinished work

No mathematical part of the item remains to split. Existing unsplit prerequisites retain their own queue entries; no claim is made that their Lean proofs are finished. No Lean was written or compiled, no agents were started, and no repository or launcher file was changed.
