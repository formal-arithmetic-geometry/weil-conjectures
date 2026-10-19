# Q138 — prop-a1-curve-boundary-sequence

## Files written

- dag/nodes/sec-deligne-laumon-a1/prop-a1-curve-boundary-sequence.json — item, statement unchanged, split into eight proof steps.
- dag/nodes/sec-deligne-laumon-a1/lem-a1-adic-middle-extension-constructible.json — new statement-only lemma, unsplit; no Mathlib match.
- citations.json — a verbatim statement quotation for every node used by every numbered proof step.

## New nodes

lem-a1-adic-middle-extension-constructible is a statement about the ordinary adic middle extension and its boundary restriction belonging to the constructible hearts, including their induced Weil structures. It asserts no localization triangle, connecting map, cohomology vanishing or exact sequence. The item carries the localization and long-exact-sequence argument itself. The new lemma has no proof, proof dependencies, or proof sketch in its statement.

## Attachments

None. I searched the slopmaster2 WeilConjectures tree by the blueprint id, the recorded declaration name, boundary-sequence terminology, ordinary direct image and constructibility. AlgebraicGeometry.exists_exact_compactlySupportedCohomology_boundary in WeilConjectures/DeligneLaumon/AffineLine/LocalDuality.lean:104-143 has a sorry body. Its statement supplies existential low-degree maps, not the distinguished compact-cohomology triangle of the DAG item, and its docstring explicitly records the missing canonical-map identifications. It also lists separatedness, finite type, quasi-compactness and finite boundary as explicit Lean hypotheses; these belong to or follow from the smooth-curve convention used by this item. It cannot be attached as a complete proof. The master checkout is reference material only.

## WANTED

None. The current main-20261015 blueprint, its separate proof file, the older imported proof, the available coefficient-definition nodes, BBD, and the Stacks sources used below are present. The argument is marked agent-written because it expands an agent-written blueprint.

## Problems found and corrected

The statement is unchanged and I found no statement dispute. I retained the imported metadata, Lean audit and ancestry fields. I read the current blueprint statement and separate proof; they give the same statement and route as the imported version.

The imported single paragraph cited lem-fin-boundary-sheaf for constructibility, although its statement concerns constructible coefficient sheaves on the ordinary small etale site and cites a finite-coefficient inverse-image definition. That statement alone does not establish constructibility of the adic Qlbar sheaf in the constructible coefficient heart. My initial expansion tried to supply this by degree-zero derived direct image and truncation, but that would hide the comparison between ordinary adic sheaf direct image and the heart of the coefficient-passage category. I removed that inline identification and introduced the smaller statement-only lemma expressly at the coefficient stage required here. Thus the ordinary middle extension is not silently replaced by Rj_*F.

The original paragraph also omitted nodes for compact-support composition, exact point fibre, the long exact cohomology sequence, and the finite-boundary hypothesis. These are now explicit uses of existing statements. The final injection needs H_c^{-1}(Z,B)=0, in addition to H_c^1(Z,B)=0 for the degree-one surjection. Both are supplied by the all-integer version of lem-a1-finite-boundary-cohomology. No weight or purity hypothesis is used.

## Searches and reuse

I read searches.jsonl and all returned hits. Every mathlib_searches entry was copied from an actual msearch.py invocation, preserving tool and query. Both semantic phrasings for the item and both phrasings for the new lemma returned general derived-category, Zariski-module, constant-sheaf or unrelated commutative-algebra statements. Loogle's first item query had an unknown identifier; I record it as an invalid query, not absence, and ran a qualified replacement. The other Loogle query gives no hit. LeanSearch was available and returned results, so it is not marked unavailable.

The grep hits for the new lemma were read in Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean:63-76: ellAdicSheaf constructs the continuous-function coefficient sheaf, and EllAdicCohomology defines its cohomology. They assert no middle-extension constructibility. I also read DerivedCategory/ShortExact.lean:30-95 and DerivedCategory/HomologySequence.lean:104-116: these give general distinguished triangles and homological cohomology, not a geometric adic localization theorem. The Loogle ordinary sheaf cohomology results are not compact-support Weil cohomology results.

I searched the entire imported blueprint using blueprint_refs.py for middle extension, ordinary direct image, middle extension constructible, degree-zero, boundary sheaf, boundary localization, zero-dimensional and long exact; I also searched DAG statements and Lean source by those concepts. The new id is unused. The finite-boundary, algebraic dimension-zero finiteness, compact-support functor package, point fibre and t-structure nodes were reused rather than duplicated. Blueprint ancestry reports prop-a1-curve-boundary-sequence itself, with empty via list; the new node records the two precise proof sentences it serves.

## Not duplicates

lem-a1-adic-middle-extension-constructible vs def-wf-middle-extension: the existing node defines ordinary middle extension and distinguishes it from derived direct image; it does not prove that this ordinary sheaf belongs to the adic constructible heart.

lem-a1-adic-middle-extension-constructible vs lem-fin-boundary-sheaf: the existing statement is about constructible sheaves on the ordinary etale site with its discrete-coefficient inverse-image convention; the new statement is about lisse adic Qlbar Weil sheaves and the specified rational/common-stage constructible hearts, including the ordinary extension on C.

lem-a1-adic-middle-extension-constructible vs thm-fin-open-degree-zero: the existing statement assumes a constructible module sheaf over a finite commutative ring on U_et; it has neither the adic coefficient-passage comparison nor the Weil-heart assertion.

lem-a1-adic-middle-extension-constructible vs prop-sf-localization-all-stages: the latter proves bounded constructibility of Rj_*F and preservation by derived pullback; it does not identify ordinary adic j_*F as an object of the heart or its ordinary boundary restriction as a sheaf. Its derived input is not the ordinary sheaf used here.

lem-a1-adic-middle-extension-constructible vs lem-sfb-rational-open-direct-image-constructible: that node concerns derived direct image in the finite-constant-local-model condensed module-object category. It gives neither the ordinary sheaf assertion nor the identification with this coefficient-passage heart.

lem-a1-adic-middle-extension-constructible vs prop-a1-curve-boundary-sequence: constructibility is a prerequisite for applying recollement, not the item's triangle or either of its exactness clauses. The item still carries the complete recollement-to-cohomology argument.

## Review by Q138

I read the chapter sec-deligne-laumon-a1 and unit sk-i-dl-a1-local, the current blueprint item and its proof, and the old imported item. This item provides the localization tool in the unit's local boundary argument; it does not replace the unit's Verdier-duality or Artin-Schreier ramification route. No SGA source is used.

For step 1 I opened def-wf-middle-extension, lem-weil-pbc-finite-type-over-noetherian and lem-pc-zero-dimensional-closed-subscheme-finite. The first fixes separated finite-type, pure-one-dimensional smooth curves over the finite field. The second gives exactly the Noetherianity needed here. The third asserts finiteness for a zero-dimensional closed subscheme of a finite-type scheme over any field. I read Stacks varieties.tex Tag 06LH, label lemma-algebraic-scheme-dim-0, including its algebraic case. The dimension-chain argument in the step establishes its missing hypothesis directly: a boundary chain of length one, preceded by a component generic point outside the boundary, contradicts dimension one. Density excludes every component generic point. The empty case needs no component.

For step 2 I checked the new lemma's statement against the actual input: F is lisse and adic, j is a dense open in a separated finite-type smooth curve, and the usual closed complement is taken with reduced structure, as in the unit. Its first conclusion is precisely that the ordinary A=j_*F is a constructible Weil sheaf. This is why I extracted that prerequisite instead of using a finite discrete coefficient theorem. Its source is the first current blueprint proof sentence and the ordinary-extension convention in def-wf-middle-extension. There is no claim that the blueprint already proves the required adic comparison; that is the new lemma's future work.

Step 3 uses the section formula actually printed in def-wf-middle-extension. For V over U, V times_C U is V; restriction and coefficient maps are the same. This is a short definitional argument, not a lemma moved into a new node. Its naturality also respects the Weil automorphism.

For step 4 I opened both the new statement and prop-sf-open-closed-triangle-all-stages. The new statement explicitly gives B in the boundary constructible heart. The existing theorem accepts K=A in D^b_c at Qlbar, identifies its closed direct image with Ri_*, and supplies the displayed counit/unit triangle and equivariance. The schemes and immersions descend from k0, which is the theorem's Weil hypothesis. It is applied to the ordinary A, not to Rj_*F. This is the correction that avoids the ordinary/derived confusion in the imported prose.

For step 5 I read clause (3) of prop-functor-package, the final equivariance paragraph of prop-weil-operations, the entire statement of lem-weil-point-fibre-equivalence, and def-weil-ordinary-compact-cohomology. Clause (3) explicitly states the localization triangle after Rf_! and its compact-support composition. The point theorem explicitly carries distinguished triangles to distinguished triangles. The cohomology definition identifies each coefficient complex with the required RΓ_c. All schemes and maps are in their separated finite-type domains. Only these generic tool clauses are used; none of the package's smooth base-change, purity or duality assertions enters.

For step 6 I read the current, reviewed statement of lem-a1-finite-boundary-cohomology rather than its obsolete imported proof. It accepts an arbitrary Qlbar Weil sheaf on a scheme finite over k0 and asserts vanishing for every integer except zero. Step 1 and the new boundary-heart clause verify those hypotheses. There is no unproved assertion about cohomology of the full derived boundary complex i^*Rj_*F.

For step 7 I opened clause (5) of lem-weil-heart-short-exact-triangles, def-sbc-standard-tstructure-derived-category and prop-constructible-truncations. I read BBD Example 1.3.2(i) and Theorem 1.3.6 in the available PDF, including the identification of usual derived cohomology with the heart cohomology functor. Clause (5) gives exactly the long exact sequence used, and the standard t-structure gives the correct degree convention. Common-stage cohomology can be computed at a finite field and extended using the scalar-extension compatibility actually stated in prop-constructible-truncations. Naturality and the equivariant triangle make the maps Frobenius-equivariant. Step 8 only computes kernels and images in those two sequences, so is elementary and has no hidden geometric input.

I tested the statements and degree indices on j=id (empty boundary, giving the identity triangle and cohomology isomorphisms), the zero sheaf (all terms zero), a constant sheaf on A1 minus one point, a boundary containing closed points of degree greater than one, and disconnected smooth curves where the dense open meets every component. The new constructibility lemma does not assert that the extension is lisse at the boundary; a nontrivial inertia representation can have a smaller invariant stalk there. It also does not assert the false vanishing of R1j_*F. These tests support the ordinary-versus-derived convention in the split.

I checked delivery-errors B through E against the files: one self-contained statement-only node; definitions of its coefficient category, heart and operations named; actual recorded searches; no new definitions or fabricated Stacks tag; no unquoted dependency, no use of a cited node's internal proof, no clause moved into a child, and no added purity, properness or connectedness hypothesis. Every step is under 2000 characters. Generic off-unit tools are declared in split_report.tool_uses; the maintainer-owned tool_uses field is not edited. Every per-step citation has a verbatim quotation in citations.json. No Lean was written or compiled, and only the sandbox was written.

## Unfinished work

Nothing remains for this one-level stage-1 split except the required server dry run and delivery. The new lemma deliberately remains unsplit for the next DAG level. It requires a proof that the ordinary adic middle extension and its ordinary inverse-image boundary object land in the specified constructible hearts, including the coefficient-passage comparison; it is not being treated as already proved.
