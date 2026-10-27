# Q72 stage-1 delivery

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-connected-group-frobenius-flat.json`: statement unchanged, split into seven proof steps; not a Mathlib leaf.
- No new nodes and no new Mathlib leaves. The existing DAG supplies every non-elementary input.
- `citations.json`: one verbatim statement quotation per cited node per step.
- `searches.jsonl`: actual Q72 search log produced by msearch.py.

## Attachments

None. Searches of `lean/WeilConjectures/` by the exact blueprint tag and by Frobenius/flatness and group-homomorphism terminology found no declaration giving this statement. Existing sorry declarations would not qualify.

## WANTED

None: Milne's book and the relevant Stacks source files are present locally.

## Audit and corrections

The imported statement is true as written. Its proof was empty. I supplied the affine-coordinate version of Milne's proof of Proposition 2.29: reducedness and the inverse field Frobenius make the relative Frobenius injective on coordinates; the existing reduced-target Hopf theorem gives faithful flatness. The iterated relative-Frobenius finiteness theorem and Noetherian-target finite presentation complete the claim. No statement was weakened, and connectedness is retained even though this argument does not need it.

The tensor twist is not silently identified with C as a k-algebra. The explicit isomorphism theta(c tensor a)=c beta(a) is an isomorphism of rings, with beta the inverse q-power automorphism of k; the Frobenius algebra map has the second-factor k-structure. This distinction is necessary for the injectivity and Hopf computations.

The blueprint provenance is inherited with `from.node: null`; following `created.item` ends at the absent record `Sheaf.SixFunctors.CtfStabilityDirectImages`, and the required ancestor command returns None. I preserved the existing provenance place and via list rather than inventing an ancestor. They explicitly identify det-thm-sf-ctf-stability-direct-images proof (3) and the finite-flat-Frobenius prerequisite before Frobenius-Borel induction. I read the latest unit `_section.md` and its direct-images proof, as well as the chapter and DAG unit records. No unit realization fields are changed because this is not the unit's key statement.

## Searches and existing inputs

The blueprint searches `Frobenius`, `Frobenius flat`, `relative Frobenius`, and `dominant homomorphism`, the whole-DAG statement searches, and the project Lean searches were read. Existing nodes `lem-trf-relative-frobenius-finite`, `lem-sfb-reduced-target-dominant-group-flatness`, and the affine Hopf conversion nodes cover the needed facts. The universal-homeomorphism and rational-point-image nodes were also read but are not required. I checked that the reduced-target flatness and finiteness dependencies do not reach this item.

For the item, Q72 ran msearch leanfinder, loogle, grep and leansearch, then a second semantic phrasing about injective reduced Hopf maps. Hits include Algebra.Smooth.flat, IsAlgClosed.perfectRing, iterateFrobenius_inj, bijective_iterateFrobenius, and faithfully flat ring-map statements. None states finite faithfully flat relative Frobenius of smooth affine group schemes or supplies all clauses in one-line specialization. Original item searches are retained; newly recorded queries are exactly those in the Q72 log. There are no service-unavailable results in these Q72 searches.

## Not duplicates

No new nodes. General Hopf flatness, affine Hopf operations, relative-Frobenius finiteness, and Noetherian finite presentation are reused, not recreated. In particular no clause of the item is moved into a new node.

## Review by Q72

I read Milne 2.24--2.29 on printed pp.46--49, including the proof on p.49, and 1.65, 1.69--1.71 on pp.26--28. For finiteness I read Stacks varieties.tex Tags 0CCD (lemma-relative-frobenius-finite) and 0CCG (remark-n-fold-relative-frobenius). I read Tag 056T (lemma-smooth-geometrically-normal), the tensor/affine-fibre-product inputs' statements, the localization exactness and flat-localization statements (00CS, 00HT), Noetherian permanence (00FN), and the Noetherian finite-type/presentation conversion (01TX). No new-node source is needed. Sources in proof steps name tags and source labels, not changing section numbers.

Step 1 uses exactly the four cited statements: finite-type affine coordinates are finitely generated; the spectrum of the tensor is the fibre product; smooth fibres are geometrically reduced; and an affine scheme is reduced exactly when its ring is. Over the one-point scheme Spec k the fibre is G itself. The generators of the twist are exhibited, not inferred from an unstated descent theorem.

Step 2 uses the cited tensor universal property and writes out the balancing and inverse formulas. The qth-root field automorphism follows directly from algebraic closedness and the characteristic-p binomial identity. Reducedness makes q-power injective on C, so phi is injective. The ring isomorphism theta is explicitly not k-linear for the second-factor structure. This is a short calculation for the actual objects in the item, not an independent unsplit comparison theorem.

Step 3 takes all three Hopf coordinate maps from the coordinate-Hopf node and checks their preservation on pure tensors. The base-changed counit is a epsilon(c)^q, so the scalar twist is accounted for. The spectrum-functor node states exactly that preserving these three maps gives a group-scheme homomorphism. These facts apply to noncommutative groups because their coordinate rings remain commutative; cocommutativity is not assumed.

Step 4 opens and uses the full statement of the existing reduced-target dominant-group flatness node, in its ring formulation. Its reduced algebra A is D, its target algebra B is C, and its injective Hopf map is phi. Algebraic closedness, finite generation, reducedness of D and Hopf compatibility are already established. No property of that node's proof is imported.

Step 5 uses the existing finite relative-Frobenius theorem with n=r, not merely its first-power special case. The two projection composites identify the map unambiguously; the affine fibre-product calculation is already in Step 1. Both the characteristic-p and local finite-type hypotheses are satisfied. I did not infer finiteness merely from a finite kernel or an isogeny.

Step 6 uses faithful-flat-surjectivity on spectra, and then verifies scheme flatness using the definition of faithful flatness, localization exactness, the explicit localization/tensor formula, and flatness over a localization. It also cites clause (1) of the affine-stalk localization node, whose statement introduces every commutative ring and prime, and writes the actual induced fraction map. Thus it does not confuse module flatness with an unproved claim about stalks. At a prime q of C, p is its contraction in D, so D_p to C_q is exactly the local homomorphism required by the flat-morphism definition.

Step 7 uses the existing finite-type affine Noetherian theorem on D; the single affine chart gives local Noetherianity by definition. The finite-over-locally-Noetherian theorem really concludes finite presentation, which includes the claimed local finite presentation. The affine permanence node really gives quasi-compactness. The fppf assertion is then precisely the definition spelled out in the item.

I checked the B--E delivery checklist: self-contained unchanged statement and notion dependencies; standard TeX; no speculative Mathlib claims; all uses recorded in proof_deps; every quoted statement read and copied verbatim into citations.json; no source-only theorem masquerading as a node citation; no new or clause-restatement nodes; and no hidden induction or unsupported transport. Every step is shorter than 2000 characters. Generic off-unit inputs are declared in split_report.tool_uses for review.

The trivial group gives C=k, where the map is an isomorphism; the calculation also covers p=2 and every r>=1. For G_a it is t to t^q with rank q, and for G_m it is t to t^q on the Laurent algebra, again finite flat. No surjectivity on arbitrary R-points is asserted: Frobenius on nonperfect R need not be onto. Smoothness is used for reducedness, so a nonsmooth group such as alpha_p does not satisfy the relevant hypothesis. No dimension-positivity, reductivity or group-commutativity assumption is introduced.

## Unfinished work

None within this one-level split. Required server dry run and delivery are performed after this report is written.
