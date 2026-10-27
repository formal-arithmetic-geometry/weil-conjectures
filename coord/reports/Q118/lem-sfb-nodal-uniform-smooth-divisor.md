# Q118: lem-sfb-nodal-uniform-smooth-divisor

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-nodal-uniform-smooth-divisor.json`: statement, split into eight proof steps; no statement change; no Mathlib match.
- `citations.json`: one verbatim statement witness for each of the 27 step/node citations.
- `searches.jsonl`: actual search-command log, supplemented by the item’s preserved earlier search records.
- `report.md`: this report. `write_split.py` is sandbox-only preparation material.

There are **0 new nodes and 0 new Mathlib leaves**. Existing tools suffice; in particular no clause of the item is moved to another node. No Lean was written, no compiler or Lake command was run, and no repository file was edited.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, uniform smooth-support divisor terminology, nodal curves, and globally generated line bundles. The curve divisor/normalization APIs found do not state all clauses for a connected reducible nodal curve with this uniform exponent. They do not justify an attachment.

## WANTED

None. The argument follows the local Stacks source files. No SGA source is used.

## Findings and changes

The inherited item has an accurate statement, but its source note by itself is not a split. Tag 0E3F states a global-generation criterion, not the assertion of this item. Read its statement and proof at `curves.tex`, label `lemma-global-generation`, and the preceding Tag 0E3E, `lemma-vanishing-on-gorenstein`. The latter is already a DAG node, `lem-sfb-curve-ideal-h1-subcurve-obstruction`. Instead of creating a second global-generation node, apply that existing obstruction with the reduced point as cluster and prove the required evaluation surjectivity directly. The proof remains within the numerical-global-generation route given by the item's source.

The subcurve genus estimate is proved in Step 2 by the ideal sequence and vanishing of H²; it does not assume a dual-graph theorem that no cited node states. The normalization-degree comparison, tensor-degree additivity, and degree-length conclusion each have their own existing node citation. Regularity of the section is checked on every affine trivialization using reducedness; a nonzero global section on a reducible curve is not simply assumed regular.

The imported blueprint ancestry has `from.node: null`. The prescribed `tools/blueprint_refs.py ancestor` command itself reports `None`. Preserve this inherited ancestry and its detailed place/via list, rather than inventing a blueprint ancestor. Read the newest source at `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`. Clause (3) is the outer direct-image route; this numerical lemma is an auxiliary created below its inherited relative-Picard/alteration input. Searched the whole imported blueprint with `blueprint_refs.py` for global generation, globally generated, nodal, subcurve, genus, normalization, smooth-support and effective divisor. The existing blueprint has no node stating the whole item. `same_as` remains the searched empty list. The chapter and unit records were read; this is not a key node, so no unit realization is edited.

The item's previous Mathlib searches were retained. Fresh logged searches used LeanFinder twice with distinct numerical/global-generation phrasings, LeanSearch, Loogle and source grep. Read all returned hits: localization of structure-sheaf sections, the smooth locus, Weierstrass division polynomials, analytic divisors and Lagrange interpolation do not state the nodal-curve assertion or a one-line specialization. No search was fabricated and no unavailable service was classified as no match.

## Not duplicates

No new node was created. Before deciding this, searched the whole DAG for Tag 0E3F, subcurve, normalization/genus, degree components, tensor degrees, regular sections, finite linear avoidance and finite singular loci. Reused the existing nodes for those inputs, including the more general reduced-curve H¹ obstruction rather than a new nodal specialization.

## Review by Q118

I read Stacks `curves.tex` Tags 0E3E and 0E3F in full, `varieties.tex` labels `lemma-degree-birational-pullback` (0AYU), `lemma-degree-in-terms-of-components` (0AYW), `lemma-degree-tensor-product` (0AYX), `lemma-degree-effective-Cartier-divisor` (0AYY), and `lemma-chi-tensor-finite` (0AYT), and `divisors.tex` labels `lemma-characterize-OD` (01X0), `definition-zero-scheme-s` (02OQ) and `lemma-regular-section-associated-points` (0AYL). The assembly is marked agent-written because it combines these sources and existing DAG statements rather than reproducing one source theorem. There are no new nodes requiring independent source identification.

For Step 1 I opened the statements of `lem-weil-pbc-invertible-pullback-tensor`, `lem-trf-proper-field-invertible-coherent`, `lem-weil-pbc-closed-immersion-proper`, and `lem-pc-euler-characteristic-well-defined`. They give exactly invertibility, coherence/Noetherianity, properness of arbitrary closed subschemes, and finite-dimensional coherent cohomology. The finiteness statement applies to proper schemes, not just smooth or projective curves. This matters because C may be reducible and a subcurve need not be smooth.

For Step 2 I read `def-sbc-closed-immersion-ideal-sheaf`, `pqf-lem-coherent-ft-locnoeth`, `lem-sc-noetherian-cohomology-above-dimension`, `lem-sfb-closed-immersion-cokernel-cohomology`, and `lem-weil-pbc-proper-reduced-algclosed-global-sections-product`. The definition actually supplies quasi-coherence of the ideal; Noetherian finite generation makes it coherent. The vanishing node covers every Noetherian scheme, unlike `lem-pc-vanishing-above-dim`, whose actual statement requires a smooth projective curve and which I therefore did not use. The closed-immersion cohomology node supplies the precise module cohomology sequence and k-linear identifications. Its H¹ restriction is surjective because the next group H²(C,I_B) vanishes. The global-sections-product node applies to reduced proper B without smoothness. Connectedness and nonemptiness make its product exactly k. I wrote why every reduced connected one-dimensional closed B is a union of components: any additional zero-dimensional component would be isolated and disconnect B. This establishes both g_B ≤ g and χ(O_B)=1−g_B without borrowing an argument from another node's proof.

For Step 3 I opened `lem-sc-normalization-properties`, `lem-per-birational-curve-degree-invariance`, `lem-trf-degree-weighted-irreducible-components`, `lem-weil-pbc-invertible-pullback-tensor`, and `lem-trf-curve-degree-tensor-additive`. The normalization is applied to each integral proper component, not to C as an integral curve. Its source and target are proper of dimension one, and its birationality is exactly the hypothesis of the degree-invariance node. Reducedness forces generic multiplicities equal to one; the weighted-components node gives the finite sum formula on both C and B. The tensor formula works on proper schemes of dimension at most one and iterates for m≥1. Positive integral degrees give at least one on every component; L contributes zero. Thus the same m≥2g+1 bounds every connected subcurve and total degree is mh. No unproved equality between arithmetic degree and component degree is assumed.

For Step 4 I opened `lem-weil-pbc-closed-point-residue-field-base` and `lem-sfb-curve-ideal-h1-subcurve-obstruction`. The residue-field node requires only local finite type over the algebraically closed k. For the obstruction node C is proper, reduced, connected and dimension one; x is a zero-dimensional closed subscheme. The statement actually bounds the degree by −2χ plus the intersection's space of functions, which is the clause quoted in citations.json. The scheme intersection with a reduced point is empty or that point, by the quotient-of-k calculation written in the proof; no Cartier assumption on x is made at a node. The bound is ≤2g_B−1 and contradicts ≥2g_B+1.

For Step 5 I opened `lem-sc-ext-tensor-exact`, `lem-pc-closed-immersion-coherent-cohomology`, and again the module cohomology sequence node. The tensor-exactness node is a theorem, not merely a definition of an invertible or flat sheaf. The closed-immersion theorem includes the projection formula that identifies the quotient with i_*(A|_x). Both schemes are locally Noetherian and the one-dimensional fibre on the reduced k-point is coherent. Vanishing from Step 4 makes the actual evaluation surjective, and hence its kernel proper.

For Step 6 I opened `lem-trf-nodal-marking-special-point-incidence`, `lem-sc-lft-over-field-jacobson-space`, `lem-sfb-separably-closed-field-infinite` and `lem-pc-finite-linear-avoidance`. The first really states finiteness of the singular subscheme for a finite-type nodal curve over algebraically closed fields; specialize the extension to the identity and choose the empty marking, so no projectivity or stable-curve assumption is imported. The Jacobson node gives closed points of the ambient curve dense in every closed component, which is enough to choose q_Z. Algebraic closedness implies the separably closed hypothesis of the infinity node. The avoidance node is a Mathlib leaf for finite-dimensional V and finitely many proper subspaces, precisely the spaces constructed in Step 5. I wrote the integral-domain argument ensuring that nonzero value at q_Z forces a nonzero component-generic restriction.

For Step 7 I read the two definitions cited. I checked the local zero ideal is (a), and proved a is a nonzerodivisor rather than citing a definition for regularity: reduce ab=0 modulo each minimal prime, then use the zero nilradical. This is a few-line elementary ring calculation, so it is a step and not a new node. At a node nonzero fibre value is equivalent to a unit coefficient. Thus all zeros lie in the smooth locus even if the chosen section vanishes with multiplicity elsewhere.

For Step 8 I opened `lem-pc-zero-scheme-divisor-iso` and `lem-pc-degree-base-change`. The former assumes Cartier zero scheme, which Step 7 has established; it is not used to prove Cartier regularity. The latter's effective-divisor clause explicitly states dim Γ(E,O_E)=deg O(E) on any proper scheme of dimension at most one. Its smooth-curve degree comparison would not suffice; I use the general clause. This yields exactly mh, with no reduction of the divisor and no loss of multiplicity.

Small cases checked: C=P¹, g=0, m=1; a tree of rational components (g=0 with arbitrarily many nodes); an irreducible self-nodal curve; a cycle of rational components; and B=C. The genus bound and point-intersection estimate remain valid in each. Rational tails need positive H-degree, which is in the hypothesis. The self-node need only be avoided once as a closed point, and no normalization-branch count enters this proof. Finite fields would invalidate the subspace-avoidance argument, but k here is algebraically closed and infinite. Empty C is excluded as stated. Every proof step is below 2000 characters and hides no separately stated comparison lemma. Off-unit statements are declared in split_report.tool_uses as general tools, not a change of the unit route.

I checked delivery-errors B through E: no new unstated notion or unsearched node, no moved clause, no source-only proof citation, no unsupported non-elementary step, and no application with a missing hypothesis. All 27 uses have exact copied statement witnesses. The statement, original citations, search history, and inherited blueprint fields are retained.

## Unfinished work

None in this one-level split. Server dry run and push are recorded below once they finish.
