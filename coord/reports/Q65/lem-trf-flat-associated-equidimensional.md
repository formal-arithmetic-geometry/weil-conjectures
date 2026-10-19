# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-flat-associated-equidimensional.json`: item, split into three proof steps; mathematical statement is byte-identical to the shared repository. Added the existing module-pullback definition to statement dependencies.
- `dag/nodes/sec-trace-formula/lem-trf-flat-relative-associated-specialization.json`: one new statement-only lemma, unsplit; no Mathlib match. It states the pointwise specialization theorem, Stacks 0GSI, including the component-dimension equality explicitly established in its proof.
- `citations.json`: verbatim statement quotations for every step/node pair.
- `searches.jsonl`: actual searches recorded by msearch.py; `write_split.py` is sandbox-only preparation code.

## Attachments

None. Searches of the entire read-only slopmaster2 `WeilConjectures/` tree for the item tag, equidimensionality, relative associated points and specialization found no exact project declaration. The master's reference declarations are not treated as finished proofs. No Lean was written or compiled.

## WANTED

None: all mathematical sources used are present in the repository.

## Corrections and scope

The item's source really is More on Morphisms Tag 0GSJ, `lemma-flat-associated-equidimensional`, with the hypotheses printed in the item: arbitrary schemes, locally finite type morphism, finite type quasi-coherent module, relative associated point, and flatness only at generic points of the fibres of the reduced point closure. I did not impose a Noetherian base, global flatness, flatness of the closure, finite presentation, or quasi-compactness. There is no statement dispute.

The original item was statement-only. Its complete proof is the pointwise-to-uniform argument of 0GSJ. I made its finite integer explicit: the nonempty irreducible fibre at t=f(y) has the same dimension as a nonempty finite type affine open. The two dimension conventions must not be confused: this item uses the equidimensional-fibre convention of Morphisms 02NJ, not merely constant total fibre dimension as in `def-pc-dimension`. The existing latter definition is deliberately not cited.

The new pointwise node is not a renamed clause of the item. It assumes flatness at one selected point x, imposes no flatness elsewhere, and computes the precise dimension from the initial fibre Y_t. The item must still establish that this dimension is a finite nonnegative integer and apply that computation uniformly to all components. This is exactly the named non-elementary input which the source's proof uses.

Searches of the whole DAG by 0GSI, 0GSJ, associated-point-specializes, relative assassin and equidimensionality, and whole-blueprint searches by `associated`, `specializes`, `equidimensional`, `0GSI` and `flat associated equidimensional`, found no existing pointwise node. The blueprint ancestor is `lem-trf-local-term-locality`; both ancestry chains and the exact component-closure/flat-family place are recorded. The unit and chapter records were read and not changed: this is a lower-level dimension tool in the existing semistable-alteration branch, not a replacement of the unit's route.

Mathlib was searched through msearch.py with two pointwise phrasings and an additional uniform formulation, Loogle, LeanSearch and two source grep patterns. Returned types were read. Flat.generalizingMap and HasGoingDown only lift specializations; rankAtStalk results concern module rank rather than fibre-component dimension; generic-point results say nothing about the relative assassin. The AlgebraicCycle/Basic.lean hit at line 65 is a comment about pushforward weights, not a theorem; other grep hits concern elliptic-curve formulae. No returned theorem is an exact match or a one-line specialization. The new node records the six pointwise searches actually logged; the item retains its older searches and adds this run's actual logged queries. Every service used responded successfully.

## Not duplicates

lem-trf-flat-relative-associated-specialization vs lem-trf-flat-fibre-component-closure-dimension: the existing node assumes a globally flat scheme morphism and a fibre-component generic point for the structure sheaf, and compares all component closures; the new node allows an arbitrary morphism and finite type quasi-coherent module with flatness only at one selected point, assumes a relative associated point, and proves relative association and a pointwise dimension comparison. The existing source mentions 0GSI but does not state it, and the existing node depends on the item, so using it here would also be circular.

lem-trf-flat-relative-associated-specialization vs lem-trf-flat-associated-equidimensional: the item has simultaneous flatness at all fibre-component generic points and a global fixed-dimension conclusion; the new node has only pointwise flatness and a specified numerical comparison with Y_t. It is the source's independently stated pointwise input, not a clause copied with the same hypotheses.

lem-trf-flat-relative-associated-specialization vs lem-trf-flat-dense-generic-fibre-pure-dimension: the latter assumes a flat morphism with dense pure-dimensional generic fibre over an integral base and concludes geometric-fibre purity; it neither allows an arbitrary module nor states relative association or flatness at only a single point.

## Review by Q65

I read `more-morphisms.tex`, 0GSJ (`lemma-flat-associated-equidimensional`) and its whole pointwise input 0GSI (`lemma-associated-point-specializes`). The latter's statement gives relative association and local fibre dimension; its second proof paragraph explicitly gives dim(C)=dim(C')=dim(Y_t), which justifies the component-dimension clause of the new node without appealing to an uncited conversion. I also read Varieties 0A21(3), including its affine-open proof, and Morphisms 02NJ. The new node retains exactly the pointwise source assumptions: f is locally finite type, F is quasi-coherent of finite type, y is fibrewise associated, x is generic in the specified closure fibre, and F is S-flat at x. Its definitions of stalk, associated prime, pullback and flatness were checked against their dependency statements. It has no proof or proof dependencies; its real proof remains a future item.

Step 1 uses `lem-weil-pbc-immersion-base-change-lft` only for part (2), `lem-weil-pbc-proper-fp-permanence` only for locally finite type composition in (e), and `lem-weil-pbc-lft-base-change` exactly for arbitrary base change to the residue field. None requires finite presentation, Noetherianity, or flatness of Y. The fibre and generic-point definition statements give the topological identification and the definition of closure. The residue fields of a closed subscheme and ambient scheme coincide at the same point, directly by the quotient-local-ring calculation; the fibre-product identification is its universal property. The assertion that y remains generic in Y_t is written out using intersections with opens, not an assumed dominance of every fibre.

Step 2 uses `def-weil-finite-type-morphism` to choose a finite type affine open in a locally finite type field scheme. `lem-kun-dimension-finite-type` actually says that a finite type scheme over a field has finite dimension, so it applies to this affine U; I do not apply it directly to the possibly non-quasi-compact Y_t. `lem-sc-dimension-locally-algebraic` actually says that every nonempty open in an irreducible locally finite type field scheme has its dimension; its hypotheses were proved in step 1. `def-kun-topological-krull-dimension` excludes negative infinity because Y_t contains y, so its finite dimension is a nonnegative integer. The cited generic dimension theorem is reused as a tool, not reproduced or silently strengthened.

Step 3 uses `lem-sc-scheme-sober`, whose statement explicitly gives a generic point of every component of a scheme. The new node says exactly the two conclusions taken from it, including dim(C)=dim(Y_t); I checked them against 0GSI rather than using its internal proof objects. Its pointwise flatness is precisely an instance of the item's assumption, with flatness over S throughout (not a change to flatness over T). The common integer d was selected before s and C, which proves the uniform assertion. Fibres over S and T have already been identified in step 1. Each citation appears in citations.json as a literal substring (the full statement), and proof_deps is the union of the step uses.

For B1-B9 and C1-C8 I checked self-contained hypotheses, definitions for every mathematical notion, the source tag/label correspondence, single TeX escapes, all-node and blueprint duplicate searches, actual recorded search results, ancestry and off-unit tool declarations. No new Mathlib leaf is claimed. No unsplit proof sketch was hidden in the new statement. D1-D5: the steps establish finite dimension and uniformization; only the genuinely pointwise theorem is deferred. There is no call to the parent dimension node and hence no circular shortcut. E1-E7: all hypotheses above were checked where used; no source error or coefficient identification is involved. No step exceeds 2000 characters (lengths 866, 643, 913), and no hidden comparison lemma is being suppressed inside a long step.

Small cases checked: over a field, the closure of an associated point is irreducible and the comparison reduces to its own dimension. For A^1 over Spec k[t] with F=O, the generic closure gives d=1 and all components satisfy the pointwise statement. In xy=t over k[t], the special fibre has two components and the same dimension 1. A module supported on the closed fibre, such as O/(t), is not flat at its support, so it cannot incorrectly force association to persist from a different generic fibre. A generic-point open immersion into a DVR gives d=0 with an empty closed fibre, which remains allowed. F=0 has no relative associated y and never enters the hypotheses. No scheme is assumed quasi-compact and no reduced closure is assumed flat.

No work remains unfinished beyond the deliberately unsplit new node. All writes were confined to this sandbox; no git command was run in the shared repository, and no Lean/compiler/Lake/build command was run.
