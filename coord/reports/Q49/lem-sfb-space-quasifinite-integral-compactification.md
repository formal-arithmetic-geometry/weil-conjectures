# Stage-1 report: lem-sfb-space-quasifinite-integral-compactification

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-quasifinite-integral-compactification.json: item, split in three steps; statement and statement dependencies unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-normalization-quasifinite-locus.json: statement-only, unsplit; Mathlib supplies scheme normalization theorems, no algebraic-space match.
- citations.json: ten step/node pairs, quoting the actual cited statements verbatim.

One new node; zero Mathlib leaves.

## Attachments

None. Searches of the live WeilConjectures tree by the item's blueprint tag and by algebraic-space normalization, quasi-finiteness and integral compactification found no declaration proving the whole item. The relevant scheme normalization declarations do not attach to this algebraic-space statement. No Lean was written or compiled.

## Wanted

None. All sources used are available in literature/stacks-project/.

## Corrections and unfinished work

No statement dispute. The item was unsplit with no proof or Lean attachment. Its statement, source, historical searches and blueprint ancestry were retained. The latest blueprint (main-20261023-1620), direct-images proof (3), is the inherited route; this supporting geometric input changes no chapter or unit argument. The ancestry tool returns from.node = None for this existing chain; I retained that result rather than inventing an ancestor.

Two concurrent live deliveries supplied results I had drafted: lem-sfb-space-relative-integral-factorization and lem-sfb-space-qc-cancellation. I opened their statements, removed both uncommitted draft nodes, and cited the existing results instead. The first dry run identified the second duplicate and exited without pushing; it was repaired. The only new delivered node is the finite-type normalization locus theorem. Its proof is intentionally left to a later item under the one-level split rule; nothing required for this item's split is unfinished.

## Searches

Before creating nodes I searched the whole DAG and source statements/places, and used blueprint_refs searches for normalization, normalization of, quasi-finite separated, quasi-finite locus, 0ABR, 0822, 03KS and quasi-compact permanence. Searches were repeated against the changing live DAG before delivery, which found the concurrent nodes. No equivalent imported blueprint statement was found.

Exact msearch queries and actual results remain in searches.jsonl and mathlib_searches. Multiple semantic phrasings, Loogle patterns and source grep were run. All services used here answered. The single-file grep parser placed line numbers in filename fields; I read the source directly instead of treating those malformed fields as declaration locations. Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean:119 is Scheme.Hom.exists_mem_and_isIso_morphismRestrict_toNormalization; Normalization.lean:314 provides scheme quasi-compactness; Morphisms/QuasiSeparated.lean:250 is QuasiCompact.of_comp. They quantify over Scheme, not arbitrary algebraic spaces, so the descent extension is not a one-line specialization. No Mathlib leaf is claimed.

## Not duplicates

lem-sfb-space-normalization-quasifinite-locus vs lem-sfb-space-relative-integral-factorization: the existing node constructs an initial integral factorization; the new node identifies an open inverse image with the quasi-finite locus of a representable finite-type morphism, absent from that existence statement.

lem-sfb-space-normalization-quasifinite-locus vs lem-sfb-space-integral-factorization-etale-base-change: the existing node preserves the universal integral property under etale base change; it asserts neither an open locus nor an isomorphism on that locus.

lem-sfb-space-normalization-quasifinite-locus vs pqf-lem-normalization-open: that existing node is scheme-only and assumes the morphism everywhere quasi-finite; the new node permits algebraic spaces and describes the open portion even when a non-quasi-finite locus exists.

## Review by Q49

I read spaces-morphisms.tex Tag 0ABS (lemma-quasi-finite-separated-quasi-affine) and its proof, Tag 0ABR (lemma-finite-type-separated), Tags 0822/0823 (normalization construction and characterization), Tag 0ABP (normalization base change), and Tag 03KS (quasi-compact cancellation), checking their labels against tags/tags. The new statement is 0ABR expressed through 0823's universal property, which determines the normalization factorization uniquely up to compatible isomorphism. I read 0ABR's reduction to an etale scheme atlas, its isomorphism on the inverse image of an open, and its identification of that inverse image with the quasi-finite locus. This is a genuine supporting theorem: it concerns finite-type maps that need not be quasi-finite and makes no whole-source open-immersion or compactification assertion. Its statement introduces every object and defines representability, finite type, quasi-finiteness, normalization and open subspace. It is unsplit with no proof or proof dependencies, as required.

For step 1 I opened all five cited statements. def-trf-algebraic-space gives the scheme-test interpretation of representable etale maps; def-weil-etale-morphism includes unramifiedness; lem-weil-pbc-unramified-quasi-finite-at-points explicitly gives quasi-finiteness at every point, including finite-type affine neighbourhoods. pqf-def-quasifinite supplies the Stacks pointwise notion, and def-weil-finite-type-morphism supplies finite type as local finite type plus quasi-compactness. Each scheme test U_T to T is etale by hypothesis, hence satisfies the scheme theorem. The given quasi-compactness of a supplies finite type. No atlas surjectivity assumption, global compactness of X or weaker Mathlib-only quasi-finite notion is inserted.

For step 2 I opened lem-sfb-space-relative-integral-factorization: its statement supplies exactly B, j, pi, the equation and universal property, but does NOT supply quasi-compactness of j. I therefore checked that hypothesis separately. On every scheme test, pi is integral and hence affine by def-weil-finite-integral-morphism. Clause (3) of lem-weil-pbc-affine-morphism-permanence explicitly concludes quasi-separatedness of affine scheme morphisms. Their diagonals are precisely base changes of the relative diagonal of pi. To see these tests cover every scheme map H to B times_X B, take its composite H to X: the pair of H-sections gives the map H to B_H times_H B_H, and the pullback of the latter scheme diagonal is the desired test of Delta_pi. Thus the scheme tests verify quasi-compactness of Delta_pi and hence quasi-separatedness of pi. Now the existing lem-sfb-space-qc-cancellation says exactly that a quasi-compact composite with quasi-separated second arrow has quasi-compact first arrow. Its hypotheses are a = pi j quasi-compact and pi quasi-separated, both verified. This closes the potential C4 gap without a duplicate cancellation node or an uncited algebraic-space permanence theorem.

For step 3 I read the new node's statement again: it requires representability, finite type, separatedness and the relative normalization property, all established above. It gives exactly the open inverse-image locus and restricted isomorphism used. Step 1 makes that locus all of U. The inverse image carries the induced open-subspace structure, so the open subspace with full point set is U itself. Therefore j identifies U with the open W in B. Its quasi-compactness, integrality of pi and the factorization equality were already established in step 2. Nothing uses the proof of a cited node or unspecified construction data.

I tested the item and new statement on empty source/target, identity maps, finite etale maps, and non-surjective open charts. For A^1_k to Spec k the quasi-finite locus is empty, and the new node permits W empty; it does not falsely assert the whole first map open. Integral maps need not be finite, and no finite compactification is asserted. The source U can have non-quasi-compact total space over a non-quasi-compact base; the proof only uses quasi-compactness of the morphism. No normality, Noetherian or global separatedness assumption is added.

I checked delivery-errors B--E with the nodes and sources open: the sole new statement is self-contained, has no proof sketch, is neither elementary nor a duplicate nor a restatement of the item's clause, and has actual logged Mathlib searches. All non-elementary facts used in the assembly are cited statements. Every quote in citations.json is verbatim; proof_deps is exactly the union of uses. Final step lengths are 740, 977 and 613 characters, all below 2000. I checked the dependency closures of the reused factorization, cancellation and permanence nodes; none returns to the item. No SGA source, repository write, Lean edit, compiler, Lake or build was used.

The two off-unit scheme facts are declared in split_report.tool_uses: lem-weil-pbc-unramified-quasi-finite-at-points supplies 02V5 on scheme tests, and lem-weil-pbc-affine-morphism-permanence(3) supplies quasi-separatedness on integral scheme tests. Both are generic tools absent from this unit, and neither replaces a unit step.
