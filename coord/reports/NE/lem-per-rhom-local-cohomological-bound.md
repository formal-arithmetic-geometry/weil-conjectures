# Worker report

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-rhom-local-cohomological-bound.json`: statement, split; six proof steps; no Mathlib match for the complete item.
- `citations.json`: one verbatim statement quotation for every citation of every step.
- `searches.jsonl`: actual search-command records, retained in the sandbox.

New nodes: 0. New Mathlib leaves: 0. The existing DAG supplies all necessary facts.

## Attachments

None. Searches of the project's `lean/WeilConjectures/` for the exact blueprint tag, RHom, internal Hom and local Hom found no declaration proving all three clauses on arbitrary small ringed sites. The monoidal derived-Hom and etale Hom-triangulated files cover related constructions, not this full local comparison and amplitude statement. A related etale exactness declaration is not an attachment for a theorem on arbitrary ringed sites.

## WANTED

None. The proof uses the local Stacks checkout and existing Mathlib/DAG infrastructure.

## What was wrong or incomplete

The item was an unsplit statement-only extraction from `lem-per-bounded-above-rhom-hyperext`, not a completed proof. Its statement is unchanged, with all three clauses retained. There is no statement dispute. I supplied the local cocycle argument, the module-sheafification passage, the descent to arbitrary derived morphisms, the exact sequence, its naturality and shift signs, and the orthogonality argument. I did not appeal to a spectral sequence above this node, which would make the proof circular.

The source's sheafification passage in Tag 0A95 is expanded using the exactness theorem for modules over a sheaf of rings. The constant-ring sheafification nodes and the ringed-space-only cohomology-sheafification node would not suffice here. I reused `lem-weil-pbc-ringed-site-module-sheafification-exact` instead. Likewise `lem-weil-pbc-finite-type-restriction-exact` has a historical name containing “finite type”, but its actual statement is for an arbitrary small site and arbitrary ring sheaf; no finite-type hypothesis is assumed or introduced.

There is an explicit sign convention: the long exact sequence has local boundary postcomposition with w[n], as in Stacks' discussion following Tag 0147. When a triangle is translated or rotated its displayed arrows carry the usual signs. Step 5 states the translated-boundary sign instead of claiming a sign-free equality of translated triangles.

## Unfinished work

None within the stage-1 split. No Lean was written, compiled, or built. No project, literature, or launcher file was changed.

## Searches and reuse

I searched the DAG by the source tags 0A94, 0A95 and the labels `lemma-RHom-into-K-injective`, `lemma-restrict-K-injective-to-open`, and `lemma-RHom-triangulated`, and searched titles/statements for K-injectives, cohomological Hom, orthogonality, exact restriction and exact sheafification. Whole-blueprint searches used `blueprint_refs.py search` with `derived Hom`, `K-injective`, `cohomological bound`, `local sheafified`, and `sheafification of modules`; `ancestor` gives `lem-per-artin-gabber-affine-curve`. No new node is needed and `same_as` stays empty. In particular I reused the exact local comparison instead of introducing a duplicate of Tag 0A94, and the existing Mathlib orthogonality leaf instead of creating a separate amplitude lemma.

All new item-search entries are the actual queries in `searches.jsonl`. I read the LeanFinder and LeanSearch hits and the relevant Mathlib source: `CategoryTheory/Sites/SheafCohomology/Basic.lean` defines ordinary cohomology presheaves from sheaves and natural-number Ext, while `Algebra/Homology/DerivedCategory/KInjective.lean` proves the external shifted-Hom bijection. Neither is the internal sheaf-Hom theorem here. A second semantic phrasing found the same distinction. The first broad grep also returned incidental occurrences of “rHom”; a second grep using a word boundary and the Sites subdirectory isolates the cohomology-presheaf infrastructure. Loogle explicitly reported overload, so that query is recorded as unavailable, despite the wrapper's OK marker. The inherited searches remain intact.

## Review by NE

I read the item's source, Stacks `sites-cohomology.tex`, Tag 0A94 (`lemma-RHom-into-K-injective`), its proof using localized K-injectivity, and Tag 0A95 (`lemma-RHom-well-defined`) with the sheafification paragraph. I also read the Hom-complex differential and equation 0A8Y, the internal-Hom construction in section 08J7, and the exact-restriction discussion preceding Tag 08FI. For the assembly I read `sites-modules.tex`, Tags 03CY and 03EI, and `derived.tex`, the representable homological lemma 0149, Definition 0147 and its sign discussion, the exact-functor lemmas 014X/015F, and K-injective Definition 070H and Lemma 070I. There are no new-node statements to validate against another source.

I opened every cited node and checked its statement, rather than using an argument hidden in its proof:

1. `prop-pur-kinjective-resolutions-exist` provides an unbounded K-injective representative on precisely a small ringed site; `def-pur-derived-internal-hom` identifies the Hom-complex model. `def-pur-hom-complex` gives its actual differential. `lem-weil-pbc-kinjective-shift` supplies I[n], and `lem-pur-rhom-into-kinjective-local` states the normalized map [f] to Q(f), not just an unspecified group isomorphism. Applying that degree-zero theorem to I[n] is justified by the displayed identity of complexes. `def-pur-localized-ringed-site` gives sectionwise restriction and its composition rule. This checks both module actions and restriction in clause 1 without assuming P is K-flat.
2. `lem-weil-pbc-ringed-site-module-sheafification-exact` explicitly concerns variable ring sheaves, not constant coefficients. `lem-weil-pbc-exact-functor-complex-cohomology` says its cohomology comparison respects cycles and quotient classes. The adjunction in `def-weil-presheaf-modules-sheafification` identifies the sheafification of each sheaf term with itself. The objectwise kernel/quotient description of presheaf cohomology is written out, so no ringed-space sheafification theorem is silently generalized.
3. `lem-weil-pbc-kinjective-hom-derived` explicitly gives the Hom bijection for any complex source and a K-injective target; it applies to I and J representing arbitrary M and N. Thus an arbitrary derived morphism can be represented by the chain map used in the formula. Its homotopy-equivalence consequence handles changes of representatives. Restriction is precisely the one defined in `def-pur-localized-ringed-site`. Naturality and additivity reduce to composition and addition of these represented maps.
4. `lem-weil-pbc-finite-type-restriction-exact` says restriction preserves finite limits and colimits for any small ringed site. `lem-weil-pbc-exact-functor-derived-factorization` includes the induced triangulated functor and its normalized shift comparisons. `lem-weil-pbc-hom-into-triangle-exact` gives representable exactness at the required terms, after rotations/translates. `lem-weil-pbc-ringed-site-module-sheafification-exact` then passes this objectwise exact sequence to module sheaves. The boundary is defined by the actual local arrow w[n]; it is not inferred from a definition node for RHom.
5. The elementary coherence calculation uses the differential in `def-pur-hom-complex` and K-injective shifts from `lem-weil-pbc-kinjective-shift`. `def-weil-triangulated-category` states the last square of a triangle morphism and the rotation signs. The proof explicitly composes that square with h. The identity of component comparisons for successive shifts, and multiplication of the signs, establish the shift compatibility. `def-sp-homological-functor` asks for exactly the middle exactness already proved, together with additivity. This step is elementary relative to the cited facts, not an uncited triangulated-functor theorem.
6. The exact-restriction and exact-functor-cohomology statements used here give preservation of cohomological bounds on every slice. `def-sbc-standard-tstructure-derived-category` describes precisely these bounds, including integer shifts. `lem-pc-derived-tstructure-orthogonality` states vanishing of all morphisms for separated bounds. I verified the inequality r < b-n, not its reverse. Every local Hom group is zero, so the previously established sheafification formula finishes the proof.

The small cases checked were K=0, M=0, a point site with a field, and the cutoff itself: for K=k[-r] and M=k[-b], T^n(M) can be nonzero at n=b-r and vanishes below it. Thus the assertion correctly uses a strict inequality and permits negative bounds. No finite global dimension, finite Tor dimension, bounded resolution of M, points of the topos, or cohomological-dimension estimate is used. No new statement is introduced, so there are no new-node elementary/restatement/duplicate issues under B and D. Each non-elementary step cites actual existing theorems, quotes are verbatim, and every step is below 2000 characters. The cited nodes' dependency closures were checked not to reach this item. Generic off-unit uses are declared in `split_report.tool_uses`; they support the inherited coefficient-duality route and do not replace the perverse unit's argument. I read the current main-20261015 unit and ancestor proof as well as the parent's accepted assembly. There is no SGA citation in the split.
