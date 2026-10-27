# Stage-1 delivery: lem-trf-bounded-injective-rhom-model-support

## Files written

- dag/nodes/sec-trace-formula/lem-trf-bounded-injective-rhom-model-support.json: existing statement, now split into four steps; no exact Mathlib match.
- citations.json: verbatim statement quotations for every step/node citation.
- searches.jsonl: actual searches recorded by msearch.py.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searches under lean/WeilConjectures/ for the blueprint tag and derived-Hom/K-injective notions found no declaration giving all the item's clauses. CategoryTheory.derivedInternalHom_obj_iso and derivedInternalHom_comparison in WeilConjectures/Algebra/Homology/DerivedInternalHom.lean supply related comparisons, but do not include this item's support bound; neither is an attachment for the whole item. Their statements and implementation were read as corroborating source material only.

## WANTED

None. All mathematical sources used are present.

## Corrections and scope

The imported statement is correct and is unchanged, including the lack of finiteness and Noetherian hypotheses. Its proof was empty. The source Tag 0G4H uses the upper-vanishing computation implicitly and does not itself state the full comparison/naturality assertion. The split spells it out using the actual internal-Hom construction in sites-cohomology.tex Tag 08J7, invariance Tag 0A95, the product formula Tag 0A8X, and bounded-below K-injectivity in derived.tex Tag 070J. The original source and blueprint provenance remain intact. No blueprint_update or released repair order was present.

The comparison is constructed with the fixed resolution unit, not inferred from a mere unspecified isomorphism of objects. This makes its first-variable naturality an explicit commuting square and inverse manipulation. No stronger enriched mapping-complex statement is needed, and an external derived Hom in abelian groups is not substituted for internal Hom in D(A).

## Searches and reuse

The current DAG was searched for K-injectivity, the relevant Stacks tags, and derived/module Hom notions. blueprint_refs.py ancestor identified lem-trf-local-term-locality as the ancestor; searches for injective, derived internal Hom, bounded injective and Hom complex found no blueprint node stating this whole item. The existing bounded-below-injectives K-injectivity leaf and Hom-complex invariance statement suffice, so nothing is extracted as a new node.

All four search tools were run through the prescribed msearch.py. A second semantic phrasing and second support-oriented grep were used. Their actual hits are in searches.jsonl and the item's appended mathlib_searches. The original Q160 searches are retained. The hits concern external Ext, injective resolutions of individual objects and K-injectivity; the exact K-injectivity hit was read at Mathlib/Algebra/Homology/HomotopyCategory/KInjective.lean:133 and reused through its existing leaf. None gives every clause of this module-valued internal-Hom statement in one specialization.

## Not duplicates

No new nodes are created. The existing lem-weil-pbc-bounded-below-injectives-kinjective and lem-pur-rhom-well-defined are reused directly.

## Review by Q105

I read dualizing.tex Tag 0G4H (lemma-finite-ext-into-bounded-injective), including its truncation proof and the assertion of upper vanishing; more-algebra.tex Tags 0A5W and 0A8H for derived Hom and the module Hom complex; derived.tex Tags 070H, 070I and 070J for K-injectivity; and sites-cohomology.tex Tags 08J7, 0A95 and 0A8X for the internal-Hom construction and invariance. The main-20261015 ancestor text, chapter and unit were read. This stays on the recorded auxiliary coherent-duality branch rather than changing the trace-formula route. There are no new-node sources to audit.

Step 1 uses def-pc-ring-hom-extension-shared-definitions for the one-object identity category, def-pur-hom-complex for the product, differential and pre/postcomposition maps, and def-sc-module-total-hom-complex for the module-valued formula. I checked each full statement: the single value of a sheaf has no additional descent condition here, and the identity componentwise preserves the scalar action and differential. This is a direct evaluation of those definitions.

Step 2 uses lem-weil-pbc-bounded-below-injectives-kinjective with lower bound a and the given termwise injectivity. Its statement allows any abelian category, so modules are permitted without Noetherian assumptions. def-pur-derived-internal-hom explicitly fixes a functorial K-injective replacement and its quasi-isomorphism unit, and describes descent of the bifunctor through localization. The map eta has source I and target its fixed K-injective replacement; both are K-injective. Consequently lem-pur-rhom-well-defined applies exactly with s=eta and t=identity, yielding a quasi-isomorphism of Hom complexes. def-weil-abstract-derived-category says localization inverts it. The inverse composed with the defining comparison gives theta. These cited nodes say all these facts, rather than merely defining injectivity or external derived morphism groups.

Step 3 uses the precise componentwise pre/postcomposition functoriality in def-pur-hom-complex and the first-variable localization functor in def-pur-derived-internal-hom. I checked arrow directions: v maps Hom(M,I) to Hom(M',I), u_M maps Hom(M,I) to Hom(M,J(I)), and u_M' v = w u_M. Thus v u_M^{-1} = u_M'^{-1} w, giving the displayed target naturality identity after composition with c_M. No quasi-isomorphism condition is imposed on f.

Step 4 uses the exact product formula of def-sc-module-total-hom-complex and the kernel/image and cohomology-functor assertions of def-weil-abstract-derived-category. If p<n the source is zero; otherwise p+r is strictly greater than b. This proves every factor is zero and hence the entire product is zero, even though the index set is infinite. A zero cochain term has zero cohomology, and theta identifies it with the cohomology of derived internal Hom.

For edge cases I checked M=0, I=0, the zero ring, the case a=b, negative a,b,n, and the strict endpoint r=b-n. The assertion makes no claim of vanishing at the endpoint: a source concentrated in degree n and target concentrated in degree b over a field has nonzero Hom there, confirming the strict inequality. No lower bound on M is used before Step 4, and no upper bound on M is introduced. No finite generation, coherence, Noetherianity or bounded-source hypothesis enters the argument. All steps are below 2000 characters; none hides a separate comparison or sublemma. Every node used in every step has a verbatim statement quotation in citations.json. All proof dependencies are exactly the union of the uses lists.

The generic cross-unit tool lem-pur-rhom-well-defined is declared in split_report.tool_uses: its statement is the foundational invariance needed here, and it does not replace the geometric argument of the unit. The K-injectivity node is already a Mathlib leaf. Definitions are used as definitions. No SGA source is used, no Lean is written or compiled, and only the assigned sandbox is written.

## Unfinished work

None in the stage-1 split. Formal Lean statements and proofs are outside this assignment. Delivery validation follows below.
