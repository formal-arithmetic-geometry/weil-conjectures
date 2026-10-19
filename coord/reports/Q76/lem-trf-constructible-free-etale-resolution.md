# Stage-1 report: lem-trf-constructible-free-etale-resolution

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-constructible-free-etale-resolution.json`: repaired split item; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-constructible-generator-epimorphism.json`: retained statement-only generator input; no Mathlib match.
- `citations.json`: repaired verbatim step-to-node citations.

## Attachments

None.

## WANTED

WANTED: `literature/lu-zheng-duality-nearby-cycles-general-bases.pdf`, Theorem 5.1 proof p. 42, for the finite-etale generator and truncation context. The PDF is unavailable locally; the construction is checked against the available Stacks proof.

## Source error and returned points repaired

The returned Step 3 applied the generator lemma to the identity of a constructible extension sheaf, so its components did not define a differential or a comparison map. I replaced it with the fibre-product induction in Stacks Tag 05T7 (derived.tex line 5302): at degree n the non-constructible cycle pullback `Ker(d_Q^{n+1}) ×_{K^{n+1}} K^n` maps epimorphically to `H^n(Cone(Q_{>n} → K))`, whose target is constructible. The finite-generator lifting lemma is applied to this actual epimorphism, and the two projections define the next differential and chain-map component. The extension direction is therefore the one supplied by the pullback construction, and the cone cohomology is killed in the correct degree.

The item previously repeated both the Noetherian conclusion and the finite-generator lifting lemma as clauses of its own statement. Those clauses have been removed; the generator result remains a separate statement-only input used in the proof. The unused Noetherian node has been removed from this unlanded delivery. Its prior source tags 03RY/03RZ were not retained; the correct Stacks Noetherian statement is Tag 09YV.

## Not duplicates

- `lem-trf-constructible-generator-epimorphism` vs `lem-weil-pbc-free-etale-module-shriek-comparison`: the existing node identifies one free representable with one extension-by-zero generator; this node gives a finite epimorphic family and lifts it through an arbitrary epimorphism onto a constructible target.
- `lem-trf-constructible-generator-epimorphism` vs `lem-weil-pbc-constructible-module-finite-presentation`: finite presentation gives a presentation of one constructible sheaf; this node supplies a family whose composite remains epimorphic for a prescribed epimorphism.
- `lem-trf-constructible-generator-epimorphism` vs `sk-lem-sf-flat-model`: the existing node records finite generators for a flat-model construction; this node asserts the sheaf epimorphism-lifting property used at every degree.

## Review by Q76

I reread the item, its citer `lem-trf-nearby-cycle-verdier-duality`, the chapter and unit context, and the source passages Stacks Tag 05T7 (derived.tex, lemma-subcategory-left-resolution, line 5302), Tag 077J, Tag 095M and Tag 09YV. I also opened the complete statements of `lem-trf-constructible-generator-epimorphism`, `thm-constructible-serre`, `lem-weil-pbc-etale-free-sheaf-constructible`, `def-weil-pbc-derived-categories`, and `def-weil-pbc-constructible-complexes`. The item now states only the bounded-above finite-etale resolution and the brutal-truncation triangle, with the Noetherian scheme, finite coefficient ring, small etale site, constructible cohomology, and positive-cohomology-vanishing hypotheses explicit. It does not assert finite projective resolutions or finite Tor dimension.

Step 1 uses only the derived-category localization statement and checks the subcomplex and quotient degreewise; the two-term identity complex tests the triangle orientation. Step 2 verifies that finite tails have constructible cohomology using the free-sheaf constructibility theorem and weak-Serre closure, and records the exact hypotheses under which the generator lifting statement can be applied. Step 3 follows Tag 05T7's downward fibre-product construction: it names the cycle pullback, the epimorphism onto the cone cohomology, and the two projections that define the differential and comparison map. The cited generator statement supplies exactly the required finite direct sum and epimorphic composite; weak-Serre closure supplies constructibility of the target. Step 4 checks that killing each cone cohomology group makes the comparison a quasi-isomorphism and that kernels and cokernels of the resulting differentials are constructible; it also checks the finite disjoint-union combination in degree zero. Step 5 only undoes the shift and invokes the corrected triangle. I checked the zero complex, the two-term identity complex, and an empty finite generator family as edge cases. No SGA source is used.

## What could not be finished

The Lu--Zheng PDF remains unavailable locally, so its page-42 context is recorded as WANTED; the actual descending construction and cone argument are supplied from Stacks Tag 05T7.
