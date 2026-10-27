# Stage-1 delivery: lem-sfb-space-relative-perfect-fibre-criterion

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-relative-perfect-fibre-criterion.json: item, statement unchanged, complete six-step split of Tag 0GFK.
- dag/nodes/sec-six-functors-basics/lem-sfb-ring-relative-perfect-fibre-criterion.json: one new statement-only algebra lemma, Tag 0GHJ; not in Mathlib after two semantic phrasings, Loogle, LeanSearch and logged source grep. No Mathlib leaves.
- citations.json: verbatim statement quotes for every step/node citation.
- searches.jsonl and ring-search-results.json: actual command searches, with their returned hits preserved.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and relative-perfect/fibre terminology. No exact project declaration was found. Existing pseudo-coherent/perfect declarations do not assert the fibre criterion.

## WANTED

None: the Stacks sources required here are in literature/stacks-project.

## Findings and corrections

The item's statement agrees with spaces-more-morphisms.tex Tag 0GFK, lemma-bounded-on-fibres; no statement dispute or correction. The source reduces to affine charts using Tag 0DKQ, then perfect.tex Tag 0GEH, whose proof uses more-algebra.tex Tag 0GHJ. Only the last algebra input is missing in the DAG. Existing nodes supply the non-elementary etale/Zariski comparisons, pseudo-coherence descent, affine pseudo-coherence, affine Tor-amplitude test, K-flat facts, and etale locality/base change of relative perfection. No new node is a definition, an elementary calculation, or a clause of the item itself: the sole new lemma is about ordinary ring complexes with global bounds, strictly below the sheaf/chart descent argument of this item.

The inherited blueprint.from.node is null and ancestor prints None; the long existing via lineage and place are retained. The child has the same null ancestor and the item prepended to via. Searches of the entire imported blueprint by relative perfect, relatively perfect, relative perfection, bounded on fibres, bounded-on-fibres, relative Tor, Tor dimension, bounded below and flat finitely presented found no blueprint statement of the new algebra criterion. Searched the whole DAG for 0GHJ, 0GEH, 0GFK, bounded-on-fibres, and their terminology; 0GHJ has no existing node. I read the current blueprint unit and direct-images proof in literature/blueprint/latest: this is the inherited supporting relative-duality branch of direct-images proof (3); no unit or chapter route is changed. The recorded unit JSON still has the older sec-six-functors route text; its fields were not edited.

## Not duplicates

No existing node has source Tag 0GHJ. lem-sfb-ring-relative-perfect-fibre-criterion vs lem-sfb-space-relative-perfect-fibre-criterion: the former is the ordinary algebra theorem for a flat finitely presented ring map and global boundedness of complexes of modules; the latter requires algebraic spaces, local bounds, site comparison, relative Tor tests for arbitrary sheaves and etale descent. lem-sfb-ring-relative-perfect-fibre-criterion vs lem-sfb-space-perfect-test-relative-perfection: the latter starts from perfect derived global sections against every perfect test, not bounded derived residue fibres of a pseudo-coherent ring complex. lem-sfb-ring-relative-perfect-fibre-criterion vs lem-trf-affine-relative-tor-amplitude-criterion: the existing node compares two Tor tests already assuming an interval; it does not derive such an interval from bounded residue fibres.

## Review by Q131

I read the complete statement and proof of spaces-more-morphisms.tex Tag 0GFK, the comparison lemma 0DKQ, perfect.tex Tag 0GEH, and more-algebra.tex Tag 0GHJ. For the only new node I copied the exact flatness, finite-presentation, pseudo-coherence and boundedness hypotheses of 0GHJ, with R-perfect expanded into finite relative Tor amplitude. The bound for each prime is allowed to depend on that prime. I read every cited node's statement, not merely its title or proof, and put its actual statement into citations.json so that the exact clause can be audited.

Step 1 uses the existing relative-perfect base-change statement with arbitrary base change, which explicitly gives relative perfection on the residue-field fibre. Taking the inverse-image structure sheaf as the test module gives the two required lower bounds directly. Neither a perfect-fibre claim nor a Noetherian hypothesis is used.

Step 2 uses the presentation criterion and scheme source-and-target locality for both flatness and local finite presentation. The finite-presentation definition permits refining to affine charts with a finitely presented ring map, and the affine flatness equivalence proves the remaining ring hypothesis. The existing space base-change node's statement explicitly includes etale locality of relative perfection, which is exactly what is needed to pass between this covering and X.

Step 3 uses the exact faithful affine etale realization to reflect cohomological vanishing. The etale/Zariski equivalence identifies the Zariski object; the pseudo-coherence-descent node explicitly gives pseudo-coherence in both sites, and the affine pseudo-coherence criterion supplies a bounded-above finite-free A-model. There is no unjustified global finite-free model on X.

Step 4 uses the chart-calculus node's pullback restriction and composition comparisons on the fibre square. The scheme flat-complex pullback node applies because the chosen model is bounded above and free over A. Its etale realization is identified by the explicit derived pullback comparison of the etale/Zariski-equivalence node. Flatness transitivity and the bounded-above flat-module K-flat lemma apply over R because A is R-flat. Thus P tensor_A (A tensor_R k) and P tensor_R k are the same termwise complex, with the same tensor differential. This is why the ordinary derived residue fibre, rather than an underived or incorrectly based fibre, appears.

Step 5 uses the etale open-map theorem and affine quasi-compactness to select finitely many open images. Taking the minimum of the corresponding finitely many lower bounds kills every lower cohomology sheaf, as detected by the jointly conservative exact geometric stalks explicitly included in the stalk-test statement. The affine realization's exact faithfulness then reflects that vanishing to the ring complex. I added an explicit citation for affine quasi-compactness during self-review, rather than leaving that non-elementary fact implicit. The finite-cover argument is elementary from these cited statements; it introduces no extra node. For an empty fibre the complex is zero, so the empty-cover case is handled separately. This is repeated for each prime and requires no uniform bound over Spec R.

Step 6 applies the new algebra theorem only after checking all its hypotheses in steps 2--5. The existing affine relative Tor criterion explicitly tests arbitrary inverse-image-ring modules, without a Noetherian or flat-base-change restriction. The etale relative Tor comparison has the required local finite-Tor clause; the space node gives etale descent. All off-unit citations are generic tools recorded in split_report.tool_uses; no alternate six-functor or SGA route is used.

I checked zero complexes, zero/empty source or fibre rings, a base field (where a bounded coherent complex on a singular fibre need not be perfect on the fibre), arbitrary non-Noetherian bases, and complexes with different lower bounds at different base primes. The conclusion is relative finite Tor dimension, not absolute perfection on fibres. Flatness is used precisely in the K-flat fibre comparison; finite presentation is retained precisely where 0GHJ requires it. Every proof step is below 2000 characters. The sole child is statement-only with no hidden proof sketch. No compiler, Lake, Lean writing, repository git mutation, external messages, or agent delegation was used.

## Unfinished

Nothing in this one-level split. The new statement-only algebra theorem remains for a later stage-1 worker by design. Required dry run and direct delivery results follow below.

## Validation

Server review_split passed. The first complete dry run passed and wrote the durable ready receipt at c0f8bdeffed. A final dry run rechecks the delivered wording before the direct push.
