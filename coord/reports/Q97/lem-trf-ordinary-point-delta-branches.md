# Q97 — lem-trf-ordinary-point-delta-branches

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-ordinary-point-delta-branches.json`: statement node, now split in eleven steps; its statement, statement dependencies, source, inherited Mathlib searches, created metadata, and blueprint ancestry are retained. No exact Mathlib match was found in the inherited search results.
- `citations.json`: one verbatim statement excerpt for each of the 25 proof-step/node citations.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No unit record changes.

## Attachments

None. I searched `WeilConjectures/` in the read-only slopmaster2 source for the exact item id and for ordinary point, ordinary node, delta invariant, seminormal, and curve-normalization terminology. There is no project declaration giving this local singularity statement. The curve normalization/cohomology declarations in `AlgebraicGeometry/Curve/Reductions.lean` concern constant sheaves, have sorry proofs, and do not state this item. The smooth affine normalization theorem in `Curve/Affine.lean` also does not characterize arbitrary reduced multibranch singularities. Upstream master was checked as reference material only; no master sorry is treated as a proof.

## WANTED

WANTED: local archival copy of Michael Temkin, *Stable modification of relative curves*, arXiv:0707.3953v3, Appendix B, printed pp. 56--57, for lem-trf-ordinary-point-delta-branches. I read the author-hosted primary PDF online at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf, including the ordinary-point definition and residue-map characterization before Lemma B.1. I downloaded nothing into the shared literature. The proof is marked `proof_origin.by = agent`: it supplies explicit local algebra for the sketched completion/gluing argument, using existing cited Stacks nodes.

## Findings and corrections

The imported statement is correct over the algebraically closed field specified here. It uses the semilocal normalization stalk, not a product of the uncompleted branch local rings. The latter need not be a product before completion, so the proof makes that product identification only after applying the finite-algebra completion theorem. This distinction is material for irreducible curves with several formal branches, including an irreducible nodal curve.

I did not use the source's pushout assertion as an uncited lemma. I replaced it with the explicit common-constant-term subring of the product of completed DVRs, a coefficientwise calculation of its power-series presentation, and a direct computation of that ring's integral closure. No curve contraction, projective completion, cohomology, properness, or separatedness hypothesis is introduced.

The current unit `sk-i-curve-zero` uses contracting correspondences, while this node retains its recorded historical semistable-alteration ancestry. I kept its maintainer-owned unit metadata and blueprint chain unchanged. The split serves exactly the already-existing Appendix B local algebra input of `lem-trf-curve-p1-tree-local-criterion`. All off-unit statements used here are generic normalization, local-ring, or power-series tools; their uses and the reason each is a tool are declared in `split_report.tool_uses`.

## Mathlib and duplicate searches

I retained and read the five inherited searches in the item, including their actual hit lists: the delta/branch and seminormal-equality natural-language searches returned Weierstrass discriminant/good-reduction declarations, while the complete-local-ring query returned Laurent/power-series equivalences and the power-series DVR/local-ring instances. These do not state the delta invariant of an arbitrary reduced curve, the semilocal normalization/completion comparison, or the equality characterization. Loogle's quoted AlgebraicGeometry/Seminormal query and the AlgebraicGeometry grep returned no hits. I did not claim to have rerun these searches, and did not invent search records.

Before considering new nodes I searched the whole DAG by statements and titles for normalization, completion, ordinary points, constant terms, complete local rings, and DVRs, and ran blueprint-reference searches including `ordinary n-fold` (zero blueprint matches), `normalization completion`, and `power series`. The relevant facts already have nodes. In particular I reused `lem-trf-normalization-singular-skyscraper`, `lem-trf-curve-normalization-completion`, and the existing finite-algebra completion, DVR-completion, power-series evaluation, and regularity tools. The nodal-normalization quotient nodes have stronger global hypotheses and are not used for arbitrary ordinary b-fold points. All remaining algebra is written in the item, rather than creating duplicate nodes or nodes that merely restate its clauses.

## Not duplicates

No new node/existing-node pairs: this delivery creates no nodes.

## Review by Q97

I checked the item against Temkin's Appendix B, before Lemma B.1, printed pp. 56--57. The local statement and residue-map proof do not require the surrounding proper connected curve once the local normalization finiteness is supplied. I also read the local Stacks source in `varieties.tex` for Tags 0C1R (`lemma-prepare-delta-invariant`), 0C3S (`lemma-pre-delta-invariant`), and 0C3V (`lemma-normalization-same-after-completion`), with its completed-product argument. For the generic tools I read `algebra.tex` at Tag 07N9 (`lemma-completion-finite-extension`), 0BI0 (`lemma-power-series-over-Noetherian-normal-domain`), 032C (`remark-Noetherian-complete-local-ring-universally-catenary`), and 00TV (`lemma-separable-smooth`), and `more-algebra.tex` at 0AP1 (`lemma-completion-dvr`), 07NY (`lemma-completion-regular`), and the universal-property passage in 07NL. There are no new-node sources to audit.

For Step 1, I read the statements of the reduced algebraic normalization, finite closed-map/finite-fibre, finite-morphism definition, closed-point residue-field, and finite-type Noetherianity nodes. They supply, respectively, restriction of normalization and its finite surjectivity, finite fibres, the actual affine finite-module meaning, structural residue-field identifications, and Noetherianity. The argument that a point of the finite fibre is closed uses the finite-dimensional-domain-is-a-field calculation written in the step. I checked that every component through the closed point has dimension one, so the local ring has dimension one; no global separatedness is used.

For Step 2, I read the normalization-singular-skyscraper statement carefully: its nonzero finite-length module and completed-quotient assertion are taken only at nonsmooth points. I checked the smooth case separately. The regularity/smoothness criterion applies because the residue field is k, hence separable; the dimension-one regular/normal criterion makes the smooth local ring normal. The normalization theorem actually states its isomorphism over the open normal locus, so B=A follows without taking a property from that node's proof.

For Step 3, the simple-filtration statement supplies only the filtration. I wrote why each simple factor over this local ring is its residue field k, so finite length gives finite k-dimension. The local-curve completion statement actually identifies the integral closure of the completion, while the finite-algebra completion statement identifies its tensor product with the completed semilocal algebra. The skyscraper theorem explicitly supplies M isomorphic to completed B/completed A for nonsmooth points. The comparison is k-linear because it is the natural A-linear map. At smooth points both quotients are zero, and the same assertion needs no extra finite-length completion theorem.

For Step 4, the finite-algebra completion statement is applied with the Noetherian local A and finite B already established, and its indices are the actual points of the normalization above x. The normalization-properties statement gives smoothness of each normalized integral component over the perfect field k. The smooth-connected-curve local-ring statement is applied on an affine open of that component containing the chosen point, so its separated, connected, nonempty, and dimension-one hypotheses all hold. The DVR-completion and local-completion residue-field statements supply exactly the complete DVR factors and the unchanged structural residue fields. No formal branch is lost by treating an irreducible original component as having only one branch.

For Step 5, the power-series adic-evaluation statement gives the continuous map for the already fixed coefficient embedding k into the complete DVR. The step itself proves surjectivity by successive residues and divisibility by the uniformizer, and proves injectivity by the first nonzero coefficient. It works in every characteristic and does not invoke an arbitrary Cohen coefficient section.

Steps 6 and 7 are explicit linear algebra and coefficient calculations and cite no black-box lemma. I checked surjectivity of the constant-term map, equality of the image of H with the diagonal, the exact description of its kernel modulo H, and the finite-dimensional equality criterion. In Step 7 I checked ideal membership for infinite mixed series by assigning each mixed monomial to its first two nonzero variables; a finite list of pairs then gives a finite ideal expression. This closes the gap that would result from checking only polynomial mixed monomials.

For Step 8, I read the finite-algebra integrality and power-series normal-domain statements. The former applies because the explicit coordinate idempotents generate D over P. The latter is applied to the Noetherian normal domain k, giving the integrally closed one-variable factors. The step writes the common total fraction ring explicitly using s=(t_i), explains which elements are non-zero-divisors, and projects the monic equation in every factor. These calculations give the normalization of the concrete axes ring without introducing a new lemma that restates the item. Step 9 explains precisely why a k-algebra isomorphism of local rings extends to total fractions and integral closures, and therefore to their quotient k-vector spaces.

For Step 10, I read the power-series regularity and completion-regularity statements and reapplied the separable-residue-field smoothness criterion. This establishes both directions of the b=1/smooth assertion. Step 11 uses only the completed-ring definition actually present in the nodal-point criterion's statement; it does not apply that criterion's Fitting-ideal/lci conclusion. The intrinsic primitive-idempotent count checks that a ring isomorphic to the two-axis ring has exactly two actual normalization branches.

I tested b=1 (the power-series DVR, quotient zero), b=2 (the node, quotient k), and the higher coordinate-axes ring (quotient k^b/diagonal k). A cusp k[[t^2,t^3]] has one branch but delta=1, so it correctly fails the equality criterion. A tacnode has two branches and delta=2, so the branch count alone does not make it ordinary. An ordinary plane triple crossing has delta=3 and b=3; it is not the three-axis ordinary point defined by this source (whose embedding dimension is three and delta=2). Irreducible nodal curves have two completed branches; the proof keeps both. The hypothesis x in X(k) rules out b=0 and the empty-curve case. No assumption about characteristic, properness, or global connectedness is added.

Every citation in every step has an exact statement excerpt in citations.json. All eleven steps are shorter than 2000 characters, and I checked the longer algebraic calculations for hidden outside lemmas: evaluation, integral closure, finite-algebra completion, and regularity are already cited statements; the remaining arguments are written out. The B--E review found no statement dispute, no new nodes, no missing proof dependencies, no clause-restatement split, and no SGA source. The local source PDF remains the WANTED item above; all requested stage-1 content is complete.

## Unfinished work

None in this one-level split. Dependencies remain their independently tracked DAG items. No Lean was written and no compiler, Lake, or build command was run. The shared repository, source checkouts, and launcher were only read; all files written are in the assigned sandbox.
