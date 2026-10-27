# Delivery report: lem-sfb-smooth-marking-normalization-twist

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-marking-normalization-twist.json`: item split into eight proof steps; no new nodes.
- `citations.json`: 22 step-to-node entries, each quote copied verbatim from the cited node statement.
- `report.md`: this report.

## Attachments

No exact sorry-free declaration was found in `lean/WeilConjectures/` or in the slopmaster2 source checkout. No attachment is claimed.

## WANTED

- WANTED: Temkin, *Stable modification of relative curves*, §1.2(b), pp. 2–3, for the normalization/residue description used by `lem-trf-nodal-normalization-adjunction`. The local literature copy is absent; the existing DAG node records the source URL and statement.

## Statement correction

STATEMENT-DISPUTED: the nodal-definition citation accidentally requires connectedness. For example, two disjoint smooth projective lines over an algebraically closed field, with the differential line on each, satisfy the intended item and every componentwise conclusion, but fail `def-trf-nodal-geometric-fibres` solely because they are disconnected. The repaired explicit nodal hypothesis preserves the intended componentwise statement and introduces no stability or positivity assumption.

## What was wrong or corrected

The imported item said “nonempty reduced nodal geometric fibres” while citing the project’s nodal-fibre definition, which also imposes connectedness. The item’s intended statement and the later componentwise conclusion do not require connected fibres, so I rewrote that hypothesis explicitly as nonempty reduced pure one-dimensional geometric fibres with completed nodal local rings and recorded that connectedness is not required. I also replaced the projective-only genus citation `def-pc-genus` by the existing proper smooth connected curve genus definition `def-sc-genus`. The source says the twist is assembled from the fibrewise adjunction identification, Cartier marking sections, and the standard degree calculation; the proof retains that route.

## Review by Q148

I read the item node, its unit record `sk-thm-sf-ctf-stability`, the current main blueprint section, and the relevant Stacks source passages. For the marking construction I checked `divisors.tex` Tag 067R and `pic.tex` Tag 0B9D: a section of a separated smooth relative curve is a closed immersion, and a finite locally free section is a relative effective Cartier divisor. Steps 1–2 cite the existing closed-section, smooth-relative-dimension, Cartier-criterion, relative-Cartier, divisor-line, tensor-invertibility, and point-Cartier statements; each quoted node actually states the fact used. I checked the local product-of-disjoint-ideals argument, including the empty case and the rank-(n) finite flat divisor over a base affine.

For base change and coherence, I read `divisors.tex` Tags 056Q and 0C4U and the existing nodes `lem-pc-recd-pullback`, `lem-pc-scheme-pullback-monoidal-existing`, `def-pc-divisor-line-bundle`, and `def-pc-module-pullback`. Step 3 uses the stated relative-divisor pullback and tensor comparison. Step 4 expands the canonical map in local Cartier frames, checks independence under changing a generator, checks tensor compatibility, and checks composition and family-isomorphism naturality by composing the underlying ring maps. The cited statements provide exactly the pullback and tensor facts used.

For a geometric fibre and component, I checked `curves.tex` Tags 0C4D and 0CBW, the existing `lem-trf-nodal-normalization-adjunction`, `lem-weil-pbc-proper-fp-permanence`, and the algebraically closed residue-field node. Step 5 verifies properness and finite type before applying the normalization-adjunction statement; it records the two branches of a self-node and rationality of branch points. Step 6 checks that a smooth marking lies on only one component, that normalization is an isomorphism there, that the pulled-back marking has multiplicity one, and that branch and marking supports are disjoint. I checked the finite-component input against the existing Noetherian-finite-components result and retained the existing point-Cartier statement rather than creating a duplicate.

For the displayed isomorphism, step 7 combines the fibre identification of `K`, the branch twist from normalization adjunction, and the marking divisor line via the existing strong monoidal pullback statement. The product-of-ideals calculation gives the divisor sum `B_C+M_C` locally, including the case where either divisor is empty. For the degree, I read `curves.tex` Tags 0C1A and 0BS6 and `varieties.tex` Tags 0AYX and 0AYY as represented by `lem-sfb-curve-differential-euler-degree` and `lem-pc-degree-base-change`; step 8 uses their exact degree statements and checks rational coefficient-one points, self-node branch counting, and the `n=0` case.

I ran the required LeanFinder, Loogle, grep, and LeanSearch searches for the item. They returned normalization, elliptic-curve, or meromorphic-analysis declarations and no marked nodal twist or degree formula, so the item remains a project statement rather than a Mathlib leaf. The server-side `review_split` preflight passed with zero new nodes and the declared generic tool use of `lem-trf-nodal-normalization-adjunction`.

## Dry-run repairs

The first dry run rejected two citation quotes because they were shorter than the required 40 characters. I replaced them by the full statements and expanded the other multi-clause quotations so their hypotheses and exact conclusions are visible. A final C1 rereading also added the existing Mathlib leaf `lem-weil-pbc-noetherian-finitely-many-components` explicitly to step 6; the earlier citation of finite-type-over-Noetherian alone did not state finiteness of the component set. No new node was created.
