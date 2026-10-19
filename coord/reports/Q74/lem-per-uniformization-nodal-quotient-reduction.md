# Stage-1 report: lem-per-uniformization-nodal-quotient-reduction

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-uniformization-nodal-quotient-reduction.json` — statement node, split; Mathlib searches found no match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-uniformization-complete-local-descent.json` — statement node, unsplit; Mathlib searches found no match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-prime-to-ell-marked-algebraization.json` — statement node, unsplit; Mathlib searches found no match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-proper-generic-curve-preparation.json` — statement node, unsplit; Mathlib searches found no match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-regular-pair-alteration-pullback.json` — statement node, unsplit; Mathlib searches found no match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-equivariant-marked-nodal-alteration.json` — statement node, unsplit; Mathlib searches found no match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-admissible-quotient-generic-degree.json` — statement node, unsplit; Mathlib searches found no match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-free-finite-action-torsor.json` — statement node, unsplit; Mathlib searches found no match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-nodal-quotient-normalized-base-refinement.json` — statement node, unsplit; Mathlib searches found no match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-alteration-cover-calculus.json` — statement node, unsplit; Mathlib searches found no match.
- `citations.json` — verbatim statement excerpts for every cited node in every proof step.

## Attachments

None. I searched the read-only `WeilConjectures` source for the item id and its geometric keywords; no sorry-free declaration states this item exactly.

## WANTED

None. The cited ILO PDF is present in `literature/` and gives the IX 1.3–1.4 route.

## What was wrong or corrected

The interrupted helper script retained the obsolete name `lem-trf-proper-birational-dimension`; the actual saved item already cited the existing `lem-trf-closed-dominant-dimension`. I verified that saved citation and its proper finite-function-field specialization, then added explicit citations of the same node for the dimension bounds in Steps 6 and 7. The Sylow reduction also needs the precise finite-etale-torsor-on-the-free-locus fact, so I recorded it as the separate statement node `lem-per-free-finite-action-torsor` instead of leaving that non-elementary assertion implicit. The remaining eight supporting nodes are proper subclaims of the item rather than restatements of its conclusion. No statement was changed.

## Review by Q74

I read the item source, ILO Exposé IX §§1.3–1.4 (pp. 131–133), and the blueprint ancestor `lem-per-artin-gabber-affine-curve`. The item is a conditional reduction: assuming the marked nodal quotient assertion, strong induction plus complete-local descent yields finite prime-to-ell regular alteration covers with strict normal-crossings boundary. Its hypotheses and conclusion are unchanged.

For Step 1 I opened `lem-per-uniformization-complete-local-descent` and `lem-weil-pbc-noetherian-local-finite-krull-dimension`. The first states both bounded and unbounded complete-local descent, and the second supplies finite Krull dimension of a Noetherian local ring; these are exactly the induction and final descent inputs. Step 2 was checked against `lem-sc-normal-dim1-dvr`, the DVR definition, regularity, the SNC-boundary definition, and alteration-cover calculus. The zero-dimensional field case and one-dimensional uniformizer boundary are elementary specializations of those statements.

For Step 3 I read `lem-per-prime-to-ell-marked-algebraization`, `lem-per-regular-pair-alteration-pullback`, and `lem-per-alteration-cover-calculus`. The algebraization node supplies the finite prime-to-ell map, the regular completion morphism, the relative curve, and the transported marking; the pullback node explicitly preserves regularity, SNC support, and covering families. Step 4 uses the complete statement of `lem-per-proper-generic-curve-preparation` and cover calculus: it supplies the proper marked curve, the prime-to-ell map to the original relative curve, the dimension bound on the new base, and the smooth generic fibre. I checked that a nowhere-dense marking cannot contain the generic point of the generic fibre, and that restriction to the dense open preserves regularity and the stated boundary.

For Step 5 I read `lem-per-equivariant-marked-nodal-alteration`, `lem-per-alteration-cover-calculus`, and `lem-trf-closed-dominant-dimension`. The nodal node supplies the equivariant model, admissible quotients, marking inclusion, and proper birational quotient maps. The dimension node states that a proper dominant finite-type map with finite function-field extension preserves dimension, which is the exact argument for the quotient base. The saved item correctly uses the existing dimension node; the older helper script was not rerun. Step 6 uses the Sylow prime-index statement, `lem-per-admissible-quotient-generic-degree`, alteration calculus, and the new `lem-per-free-finite-action-torsor`; these respectively justify the subgroup of prime-to-ell index, the generic degree `[G:H]`, covering composition, and the finite-etale torsor over the free locus. The dimension node is also cited explicitly for the finite intermediate quotient base. I removed the unnecessary suggestion to enlarge the boundary by a branch locus: the already free open gives the torsor directly. I checked the generic-freeness argument using dominance of the curve alteration and freeness on the dense base open.

For Steps 7 and 8 I read `lem-per-nodal-quotient-normalized-base-refinement`, alteration calculus, `lem-exc-finite-type-localization-excellent`, and `lem-sc-regular-connected-integral`. The normalized-base node states every clause used: decomposition subgroup, normalization in the connected torsor function field, preservation of the nodal and marking conditions, proper birational comparison, and covering. The excellence and regular-connected-integral nodes justify the affine connected refinement. The explicit dimension-node inequality for dominant generically finite maps also proves that these bases still have dimension at most d-1. The assumed item hypothesis is applied only after the induction cover has made each base regular and the boundary an SNC support. For Step 9 I checked the cited alteration-topology definition, cover calculus, regular-pair pullback, and complete-local descent statements; together they give finite composition, finite-type final arrows, exact SNC inverse images, and the unbounded descent conclusion.

I verified every citation quote in `citations.json` is a verbatim substring of the cited node statement, every proof `uses` entry is present in `proof_deps`, every new node is self-contained and unsplit, and every new node has the required LeanFinder/LeanSearch/Loogle-or-corrected-Loogle/grep search records. The search results were read; they concern unrelated algebraic-geometry or group-theory declarations and none states these scheme-theoretic reductions. No Lean file was written or compiled.

## Not duplicates

lem-per-proper-generic-curve-preparation vs lem-weil-pbc-geometrically-regular-finitely-generated-extensions: the existing node preserves regularity of a geometrically regular algebra under field extension; the new node constructs a proper marked relative curve, a finite new base, and a prime-to-ell alteration of the original curve.
lem-per-proper-generic-curve-preparation vs lem-weil-pbc-make-separable: the existing node constructs purely inseparable extensions of fields; the new node includes global compactification, Cartier marking, a smooth geometrically integral generic curve and a proper prime-to-ell comparison map.
lem-per-proper-generic-curve-preparation vs lem-sbc-generic-fibre-dominant-field: the existing node produces a field mapping dominantly to an affine generic fibre; it constructs neither a compactification nor a marked proper curve.
lem-per-proper-generic-curve-preparation vs lem-sbc-purely-inseparable-generic-base-spread: the existing node spreads a specified purely inseparable generic extension to a universal homeomorphism; the new node prepares both the curve and the marking and includes properness, smooth generic fibre and degree control.
lem-per-proper-generic-curve-preparation vs lem-sbc-radicial-reduced-flat-generic-fibre: the existing node makes a given flat affine family's reduced generic fibre geometrically reduced; it does not construct the proper smooth marked curve and Stein base of the new node.
lem-per-proper-generic-curve-preparation vs lem-sbc-radicial-separating-generic-field: the existing node produces a separably generated dominant generic field after a radicial base change; it states neither geometric smoothness nor proper compactification and Cartier marking.
lem-per-proper-generic-curve-preparation vs lem-sbc-reduced-generic-fibre-field-embedding-core-map: the existing node constructs a map from a specified field to a reduced generic fibre in a fixed affine setup; the new node constructs the global proper curve and new finite base.
lem-per-proper-generic-curve-preparation vs lem-sbc-reduced-generic-fibre-field-embedding-core: the existing node transports a dominant field embedding through specified affine base changes; the new node prepares a proper marked curve and controls its generic degree.
lem-per-proper-generic-curve-preparation vs lem-sbc-reduced-generic-fibre-field-embedding: the existing node transports an already supplied separably generated field map; the new node constructs the proper curve, finite base, etale marking and alteration comparison.
lem-per-proper-generic-curve-preparation vs lem-weil-pbc-normalization-geonormal-insep: the existing node makes normalization geometrically normal over a field after a purely inseparable extension; the new node constructs a global relative compactification, the Stein base and the Cartier marking, with prime-to-ell degree over W.
lem-per-proper-generic-curve-preparation vs lem-weil-pbc-perfect-closure-finite-normal-model: the existing node descends a normal model from a perfect purely inseparable field extension; the new node is a relative-curve preparation with a proper comparison and etale generic marking.
lem-per-proper-generic-curve-preparation vs lem-weil-pbc-reduced-normalization-over-normal-reduction: the existing node identifies normalization over an already normal reduced dense open; the new node prepares a global curve and marking and includes finite-base and degree assertions.
lem-per-regular-pair-alteration-pullback vs lem-weil-pbc-flat-over-regular-with-regular-fibre: the existing node is a local-ring regularity-ascent criterion; the new node additionally preserves global strict normal-crossings boundaries and finite alteration covering families under regular scheme base change.
lem-per-regular-pair-alteration-pullback vs lem-weil-pbc-regular-map-ascent: the existing node ascends regularity of rings for flat maps with regular fibres; it has no SNC-boundary, completion, alteration-category or covering assertion.

I additionally read the specific sources of the new inputs: ILO III 6.2 for complete-local descent, V 2.1.2 and 3.1.1–3.1.4 for marked algebraization, IX 1.3 for proper generic-curve preparation and regular-pair pullback, IX 1.2 and 1.4 for the equivariant nodal model and admissible quotients, IX 1.4 condition (*) for the free torsor and normalized-component refinement, and II 1.2.5–1.2.8 and 2.2.4–2.3.4 for cover calculus. I read the local Stacks statements at tags 030R, 0BXT and 031E. The current blueprint ancestor Step 3 is the Verdier-duality branch; the existing finiteness/duality dependency chain is preserved. The whole-blueprint searches for nodal, algebraization, regular base change and uniformization returned no equivalent blueprint nodes.

Small cases checked: the empty boundary and dimension-zero field; a dimension-one complete normal ring, where the marking is empty or the reduced closed point; the trivial group, where subgroup quotient and normalized refinement give degree one; the full Sylow subgroup in an ell-group and the trivial Sylow subgroup for a group of order prime to ell; and a regular field base extension, where finite-etale base change preserves regularity. In the normalized-refinement assertion the dominating component is essential: a non-dominating special-fibre component cannot be used in the alteration category. All proof steps are shorter than 2000 characters; none hides a long inline sublemma.

## Unfinished work

No part of the stage-1 split remains unfinished. The nine new nodes deliberately carry statements only, for later splitting. The initial resumed dry run found the missing report; the next found shared-tag duplicate checks, repaired by opening all candidates and recording the distinctions above. A subsequent dry run passed; after the final explicit dimension citations, the delivery is checked again.
