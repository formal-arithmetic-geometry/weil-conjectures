# Q59 stage-1 delivery: lem-trf-etale-topos-points-geometric

## Files written

- dag/nodes/sec-trace-formula/lem-trf-etale-topos-points-geometric.json: item, statement unchanged, split into nine steps.
- dag/nodes/sec-trace-formula/lem-trf-site-point-reconstruction-sets.json: statement, unsplit; no exact Mathlib match for reconstruction of an arbitrary geometric-morphism datum on set sheaves.
- dag/nodes/sec-trace-formula/lem-trf-affine-etale-split-neighbourhood.json: statement, unsplit; no exact Mathlib match for an arbitrary affine etale morphism with its possibly nonfinite remainder.
- dag/nodes/sec-trace-formula/lem-trf-cofiltered-finite-sets-section.json: statement, Mathlib leaf, nonempty_sections_of_finite_cofiltered_system, Mathlib/CategoryTheory/CofilteredSystem.lean:79-81.
- citations.json: one verbatim statement quote for every citation in every step. searches.jsonl: actual logged search queries; write_split.py: sandbox-only reproducible writer.

## Attachments

None. Searched WeilConjectures/ in the read-only slopmaster2 source by the exact blueprint tag, the node name, points-small-etale, and geometric/to-pos-point terminology. No project declaration states this item or the proposed children exactly. In particular the Mathlib declaration pointSmallEtale constructs a geometric point and its conservative-family lemmas do not classify arbitrary points. The item has no attached Lean audit record. No upstream sorry declaration is treated as a finished proof.

## WANTED

None. All sources used are present in literature/stacks-project/ or the current blueprint snapshot. No external source was downloaded.

## Corrections and route

The item was unsplit with empty proof and no proof dependencies. Its mathematical statement agrees with Stacks 04HU(2), including the inverse-image functor and the opposite variance of the neighbourhood category. I kept the statement exactly. I added the definition dependencies for pointed neighbourhoods and colimits.

Read the fixed sec-trace-formula chapter, sk-i-curve-zero unit and current main-20261015 lem-trf-local-term-locality.proof.md, especially paragraph (1) and (2), and retained the historical blueprint ancestor and via chain. This item is the generic classification tool used below oriented-product point conservativity, not a change of the contracting-correspondence route. The two unsplit children are general support results, and the finite-set child is an exact Mathlib leaf. No child restates the item or a clause asserting that a topos point is geometric. Off-unit categorical, scheme-topological, field, and geometric-stalk tools are declared in split_report.tool_uses.

Stacks 04HU leaves the affine reduction and functoriality to the reader. I supply those arguments. In particular I first restrict to a fixed affine open A containing the recovered point, so an affine object in the finite-fibre calculation is over an affine base. No quasi-compactness over an arbitrary non-quasi-separated base is tacitly assumed. I use a compatible family on all pointed neighbourhoods, obtained from a small affine subcategory by refinement and equalization. This makes the naturality formula literal. I then give the full affine-cover injectivity argument without claiming an affine overlap is affine. In 04HU's displayed construction the section V to U times V is a section of the projection to V; the source's phrase naming the projection to U is a typographical slip, avoided here.

## Not duplicates

lem-trf-site-point-reconstruction-sets vs lem-trf-site-point-fibre: the existing node reconstructs constant-coefficient module inverse images, including module exactness; it does not state reconstruction on arbitrary sheaves of sets, cover-surjectivity of the site functor, or the required set-valued comparison. Free-module encoding would require another argument, not a one-line specialization.
lem-trf-affine-etale-split-neighbourhood vs lem-trf-etale-topos-points-geometric: the new node splits a given affine etale morphism after a pointed base change; it contains no abstract topos point or representation theorem. The item's support recovery, inverse-limit choice, naturality, global bijection and topos reconstruction remain in its nine proof steps.
lem-trf-affine-etale-split-neighbourhood vs lem-weil-pbc-extension-by-zero-stalks: the existing node computes stalks of extension by zero; it gives no etale-local splitting of a morphism.
lem-trf-affine-etale-split-neighbourhood vs lem-sbc-finite-etale-open-generic-algebra: that statement embeds global sections into a finite generic algebra over an integral base; this statement needs no integrality and constructs a pointed splitting neighbourhood.
lem-trf-affine-etale-split-neighbourhood vs lem-pc-dense-separable-points: density of separable closed points of a smooth scheme does not provide splitting neighbourhoods of an etale morphism.
lem-trf-affine-etale-split-neighbourhood vs lem-weil-pbc-etale-smooth-zero-dimensional-fibres: zero-dimensional smooth fibres do not state the etale neighbourhood decomposition or the remainder's avoidance property.
lem-trf-affine-etale-split-neighbourhood vs lem-weil-pbc-constructible-field-finite-separable-constant: that node trivializes a constructible module sheaf over a field; this node splits a scheme over an arbitrary affine base and has no coefficients.
lem-trf-affine-etale-split-neighbourhood vs lem-weil-pbc-finite-separable-extension-etale: that node only asserts an extension's spectrum map is etale and constructs no neighbourhood decomposition.
lem-trf-affine-etale-split-neighbourhood vs lem-weil-pbc-etale-fibre-discrete-separable-points: that node describes one fibre as spectra of fields, with no etale neighbourhood or sections extending the fibre points.
lem-trf-affine-etale-split-neighbourhood vs lem-weil-pbc-etale-cover-geometric-point-lift: a lift of one geometric point through a cover gives neither simultaneous splitting nor a disjoint decomposition with a fibre-avoiding remainder.
lem-trf-affine-etale-split-neighbourhood vs lem-weil-pbc-etale-algebra-residue-field-separable: a residue-field extension calculation gives no splitting after base change.
lem-trf-affine-etale-split-neighbourhood vs lem-weil-pbc-spec-finite-product-fields: that node describes the spectrum of an already given product of fields; no extension of its components over an etale neighbourhood is asserted.
lem-trf-affine-etale-split-neighbourhood vs lem-exc-etale-field-geometric-points-detect: equality detection for morphisms from an etale field-scheme does not split a scheme over a general base.
lem-trf-affine-etale-split-neighbourhood vs lem-exc-etale-coproduct-etale: that node constructs etale field-schemes from coproducts of separable extensions, not neighbourhoods of affine base points.
lem-trf-affine-etale-split-neighbourhood vs lem-exc-etale-field-point-map-local: that node locally realizes an equivariant map between geometric fibres over a field; the new node constructs a disjoint splitting over a general affine base.
lem-trf-cofiltered-finite-sets-section vs lem-galois-inverse-limit-surjective: the existing node assumes a directed preorder and surjective transitions and concludes surjective projections; this node allows an arbitrary small cofiltered category and arbitrary transitions and concludes only existence of a compatible family.

Additional conceptual comparisons: lem-weil-pbc-directed-limit-compact-hausdorff-nonempty assumes a preordered index, so does not directly apply to the neighbourhood category; its categorical generalization would itself need reindexing. lem-fix-geometric-stalk-topos-point and lem-galois-stalk-representable start with a geometric point and cannot classify an abstract one. The former is reused for the final geometric adjunction. Blueprint searches for points small etale, point site topos, etale local technical, cofiltered finite, finite nonempty, 00YA, 04HM, and nonempty sections found no equivalent imported theorem.

## Review by Q59

I read Stacks etale-cohomology.tex, lemma-points-small-etale-site (04HU), in full, and lemma-stalk-gives-point (04FM). For the reconstruction child I read sites.tex 00YA(2), 00YC and 00YB, checking that the theorem applies to an arbitrary adjunction whose left adjoint preserves finite limits and that the comparison is for sheaves of sets. For the splitting child I read etale.tex 04HM and the third paragraph of 04HU together with the existing 02GL fibre description. Its affine hypotheses imply separatedness and a finite fibre; the ordinary splitting neighbourhood can be given the required geometric lift, refined to an affine, and shrunk to exclude the other finitely many points over s. The remaining W then has no point over s. The n copy sections label all lifts after the chosen geometric base change. For the finite-set child I read categories.tex 086J and Mathlib CofilteredSystem.lean:66-106: the public declaration at line 79 has no surjectivity assumption and permits independent universes. Its section condition is exactly the displayed compatibility formula.

For step 1 I checked the new reconstruction statement gives each of finite-limit preservation, cover-surjectivity, and the set-valued colimit comparison. The etale-site definition really gives finite limits, and the size convention allows the skeleton in the larger universe. Disjoint-union preservation is derived explicitly from covers, empty intersections, and diagonal pullbacks rather than silently cited from a definition. For step 2 I opened the sober-scheme statement: it supplies exactly a unique generic point of a nonempty irreducible closed subset. The irreducibility argument is written in the step. The flat-lfp-open node is applied with flatness and local finite presentation supplied by the etale definition. Cancellation ensures T to its open image is still etale, so the singleton family is an allowed covering.

For step 3 I opened the etale composition/cancellation, algebraic-closure existence, and geometric-point statements. Composition applies to the open A into S, and closure existence is applied to the residue field of the already constructed point s. The geometric-point statement supplies the equivalence with a residue-field homomorphism. This avoids choosing a hollow geometric object. Step 4 uses the new splitting exactly with U and A both affine and etale U to A. The support criterion from step 2 applies to W and V as objects over A. Fibre cardinality is computed over an actual element b of the nonempty u(V), not by cancellation of possibly empty sets.

For step 5 I read the small affine-cover and neighbourhood-cofilteredness statements. The former supplies a set of affine representatives and covers; adding the set of geometric lifts preserves smallness. The latter supplies common sources and equalizers, which are then refined to affine opens around the marked point. The small affine diagram has finite nonempty values by step 4, exactly the hypotheses of the finite-set leaf. For step 6 the same two existing statements provide all refinements and equalizers used in the independence check. I verified parallel composites into T are equalized before comparing images, so compatibility is with all pointed arrows. This gives naturality for every etale S-object.

Step 7 uses the splitting child's explicitly stated bijection between labels and geometric lifts. Coherence on its actual sections identifies their images with the fibre over x_V in the u-product calculation, proving both injectivity and surjectivity. Step 8 uses the affine-cover node for the arbitrary object and for its overlap, while finite-limit preservation from step 1 supplies the element in that overlap. Its injectivity proof needs no separation of T and never replaces a nonaffine overlap by an affine one without a cover. Step 9 uses the reconstruction child's set-sheaf comparison, the existing geometric-stalk point theorem in its etale case only, and the geometric-morphism definition's invertible mate clause. The pointed index categories are isomorphic by c and their opposites have the correct colimit direction.

I checked delivery-errors B through E against the files: the three children contain statements only, all their objects are introduced, all definition dependencies name their actual notions, all recorded searches ran with msearch.py, and candidate Mathlib sources were read. No unattached non-elementary assertion is imported from a cited node's proof. The two genuine geometric/categorical children carry the source lemmas, while support recovery, finite-cardinality cancellation, extension by refinements, naturality and affine-cover descent remain in the item's proof. All citations.json quotations are copied verbatim from statements. No proof step exceeds 2000 characters (maximum 1106).

Small cases checked: an empty base has no topos point since its terminal object is covered by the empty family; the proof derives a nonempty support whenever p is given. An empty geometric fibre gives n=0 and u(U) empty. A field base reduces to the finite separable splitting picture. Infinite disjoint unions and non-quasi-separated bases are handled by the affine-cover step; no finite global cover is assumed. Finite diagrams with nonsurjective transitions are allowed by the Mathlib leaf, and no surjectivity of its limit projections is claimed. All three children are strictly smaller support facts and introduce no route through SGA.

## What remains

No unresolved mathematical issue in this split. The two unsplit support statements remain future stage-1 items by design. This worker wrote no Lean, ran no compiler, started no agents, and made no writes or git calls in the shared repository or source trees.

## Validation

Server-side check_dag and review_split were run with srvcheck.py on the sandbox and passed. Final deliver.py dry-run and push results are recorded after completion below.

Dry run 1 identified a missing numeric mathlib_match.line field on the finite-set leaf. Added line 79, already read and verified in the pinned Mathlib source. No mathematical change.

Final dry run exited successfully: OK (not pushed), preflight passed, receipt commit 3579941e18. The missing line field was the only reported failure and is repaired. The delivery push runs the same preflight on the final report and node set.
