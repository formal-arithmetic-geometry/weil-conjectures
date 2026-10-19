# Q102: lem-sfb-kflat-derivability

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-sfb-kflat-derivability.json`: split into eight steps; unchanged mathematical statement.
- `dag/nodes/sec-proetale-coefficients/lem-sfb-functorial-bounded-above-class-resolution.json`: statement, unsplit; no Mathlib match. This resolves the entire category of bounded-above complexes, without putting a bound into each object's data.
- `dag/nodes/sec-proetale-coefficients/lem-sfb-kflat-homotopy-triangulated.json`: statement, with existing project declarations recorded; no Mathlib match.
- `dag/nodes/sec-proetale-coefficients/lem-sfb-homotopy-resolution-derivability-criterion.json`: statement, with existing project declaration recorded; no Mathlib match.
- `citations.json`: a verbatim statement quotation for every step/node citation.
- `searches.jsonl`: actual search-command results; retained without rewriting.

## Attachments and existing interfaces

The earlier attachment of the whole item was refused. This delivery does not repeat it. Instead its proof cites DAG nodes for the smaller project interfaces and explicitly constructs the unbounded replacement.

`HomotopyCategory.isLeftDerivabilityStructure_quasiIsoLocalizerMorphism` belongs to `lem-sfb-homotopy-resolution-derivability-criterion`, in `WeilConjectures/Algebra/Homology/HomotopyCategory/DerivabilityStructure.lean:211` (docstring begins at 201).

`HomotopyCategory.kFlat_quotient_obj_iff`, `HomotopyCategory.instContainsZeroIntUpKFlatQuasiIso`, `HomotopyCategory.instIsStableUnderShiftIntUpKFlatQuasiIso`, `HomotopyCategory.instIsTriangulatedIntUpKFlatQuasiIso`, together with `CategoryTheory.MorphismProperty.instIsClosedUnderIsomorphismsKFlatOfRespectsIso`, belong to `lem-sfb-kflat-homotopy-triangulated`. Their modules and lines are recorded in the node. The first four are in `WeilConjectures/FromJoel/CategoryTheory/Abelian/Flat/KFlat.lean:155-197`; the last is in `WeilConjectures/FromJoel/CategoryTheory/Monoidal/KFlat.lean:38-42`.

These names occur as project declarations (not Mathlib declarations) in `local/sorry_map_slopmaster2_full.jsonl.gz`, with both direct and transitive sorry flags false. I read their actual source statements and section hypotheses. No theorem of upstream master has been treated as evidence of a finished proof. The independent server audit remains authoritative.

## WANTED

None. The blueprint, Stacks sources and the supporting project source are locally available. The proof origin is nevertheless `agent`: the functorial strengthening and the general two-sided categorical colimit calculation are spelled out here rather than attributed verbatim to Stacks' module case.

## Findings and changes

There was no existing item file or report in this sandbox, only dispatcher marker files. I copied the current unsplit item and retained all its prior search records and blueprint ancestry. The rejected attachment names do not on their own justify bypassing the work required by this brief.

The important gap in the previously seeded route is functoriality. Stacks Tag 06XX (`derived-lemma-special-direct-system`) and `lem-sfb-subcategory-truncation-resolution-system` provide a strictly commuting system for one complex, but their statements do not provide a functor in the input complex. Likewise `lem-sfb-unbounded-kflat-resolution-existence` and `lem-sfb-abstract-kflat-resolution` assert existence only. They are not cited for the stronger functorial assertion. The added bounded-above lemma is about a single functor on all bounded-above complexes; its finite-total construction supplies compatibility across changing bounds.

The original cover functor need not be additive or preserve zero morphisms. This is accounted for in the new lemma's direct-summand hypothesis: reduce the cover via the split idempotent `1-P(0)` before forming functorial object resolutions. Its image is a direct summand of a class object. Naturality of the cover kills `P(0)`, so the restricted augmentation is still epic. This reduction is exactly the purpose of Mathlib's `LeftResolution.reduced`, read at `Mathlib/Algebra/Homology/LeftResolution/Reduced.lean:53-154`. One must not silently apply a zero-preserving resolution construction to an arbitrary cover functor.

No chapter or unit route is changed: these are the first three sentences of the current `lem-sfb-derived-monoidal.proof.md`, the K-flat input to step 1 of unit `sk-def-sfb-derived-tensor-hom`. The item's statement, all hypotheses and its explicit refusal to assert a homotopy-level functorial replacement are retained. The added statement dependency records the meaning of colimit. There are no SGA citations.

## Not duplicates

Before writing the new nodes I searched the entire DAG by statements, names, the Stacks tag, and the relevant project declaration names, and ran `blueprint_refs.py search` for K-flat, functorial, bounded-above, bounded above resolution, homotopy, triangulated, derivability, and 05T7. None gives the new generic interfaces. The following are every existing same-tag (05T7) pair; some mention the tag only in their proofs or search logs.

lem-sfb-functorial-bounded-above-class-resolution vs lem-sfb-subcategory-left-resolution: the old statement gives objectwise existence at a fixed bound, without functorial covers or one functor across varying bounds.
lem-sfb-functorial-bounded-above-class-resolution vs lem-sfb-subcategory-truncation-resolution-system: the old statement gives a compatible sequence for one input complex, not a functor in all bounded-above complexes.
lem-sfb-functorial-bounded-above-class-resolution vs lem-pc-kflat-bounded-flat-replacement: the old statement concerns sheaves of modules on a ringed site; the new statement concerns an arbitrary abelian category and an arbitrary class with the specified closure properties.
lem-sfb-functorial-bounded-above-class-resolution vs lem-kun-bounded-flat-replacement: the old statement is for constant-coefficient etale module sheaves with a supplied fixed bound; the new statement is generic and supplies one functor for varying bounds.
lem-sfb-functorial-bounded-above-class-resolution vs lem-pc-functorial-cycle-pullback-construction: the old construction works on complexes vanishing above one fixed N and gives a local lifting property; the new lemma works on the entire bounded-above category with no bound as input and gives a natural quasi-isomorphism.
lem-sfb-functorial-bounded-above-class-resolution vs lem-pc-functorial-cycle-pullback-core-stage3: the old fixed-bound recurrence has no epic-cover hypothesis or quasi-isomorphism conclusion; it does not supply the entire varying-bound functor.
lem-sfb-functorial-bounded-above-class-resolution vs lem-pc-functorial-cycle-pullback-lifting-stage3: the old lemma is a single-degree lifting assertion assuming a given epic pullback map.
lem-sfb-functorial-bounded-above-class-resolution vs def-pc-cycle-pullback-tower-data-stage3: the old node defines a fixed-bound recursive tower, not the functor with its quasi-isomorphism property.
lem-sfb-functorial-bounded-above-class-resolution vs lem-pc-cycle-pullback-tower-laws-stage3: the old lemma verifies differential/augmentation identities in that specific fixed-bound tower, without quasi-isomorphism or a bound-independent resolution functor.
lem-sfb-functorial-bounded-above-class-resolution vs lem-pc-cycle-pullback-tower-comparison-stage3: the old lemma identifies a term of the fixed-bound tower with a pullback-cover object.
lem-sfb-functorial-bounded-above-class-resolution vs def-tower-canonical-comparison-g3: the old node defines the canonical comparison of a recursive stage, not a resolution theorem.
lem-sfb-functorial-bounded-above-class-resolution vs new-tower-comparison-first: the old lemma is one projection identity for that comparison.
lem-sfb-functorial-bounded-above-class-resolution vs new-tower-comparison-second: the old lemma is the other projection identity for that comparison.
lem-sfb-functorial-bounded-above-class-resolution vs lem-weil-pbc-subcategory-right-resolution-05T6: the old lemma concerns bounded-below right resolutions by monomorphisms, not the functorial bounded-above left-resolution interface.
lem-sfb-functorial-bounded-above-class-resolution vs lem-weil-pbc-subcategory-right-resolution-system: the old lemma constructs a bounded-below right-resolution system with cokernel embeddings, not the new functor.
lem-sfb-functorial-bounded-above-class-resolution vs lem-weil-pbc-subcategory-right-resolution-assembly: the old lemma assembles a specified right-resolution system, not the new functor.
lem-sfb-functorial-bounded-above-class-resolution vs lem-weil-pbc-cokernel-map-mono-of-mono: the old lemma is about the induced monomorphism of two cokernels.
lem-sfb-functorial-bounded-above-class-resolution vs lem-weil-pbc-bounded-above-projective-model: the old lemma gives an objectwise projective representative for ordinary modules, not a generic varying-bound functor.
lem-sfb-functorial-bounded-above-class-resolution vs lem-sf-projection-finite-constant: the old lemma is a projection-formula isomorphism for a scheme morphism.

lem-sfb-kflat-homotopy-triangulated vs lem-pc-kflat-closure: the old closure statement is restricted to sheaves of commutative-ring modules; the new one applies in arbitrary nonsymmetric monoidal abelian categories, uses two-sided K-flatness and states the homotopy-quotient identification.
lem-sfb-kflat-homotopy-triangulated vs lem-sfb-total-tensor-homotopy: the existing node provides the monoidal structure on the homotopy category, not the K-flat property's cone/shift closure.
lem-sfb-homotopy-resolution-derivability-criterion vs lem-sfb-kflat-derivability: the new generic lemma assumes a functorial quasi-isomorphism into an already triangulated property. It neither constructs a resolution nor proves any K-flatness. The item's steps must supply both.

## Review by Q102

I read the current blueprint proof and its unit and chapter records. For the colimit argument I read Stacks Tags 06Y3 and 06Y4, `more-algebra-lemma-colimit-K-flat` and `more-algebra-lemma-K-flat-resolution`, in `literature/stacks-project/more-algebra.tex:14314-14410`, as well as Tag 06XX (`derived-lemma-special-direct-system`) at `derived.tex:9215` and the statement of the existing Tag 05T7 node. These Stacks results establish the intended truncation/colimit route; their ring-module setting alone is not cited as a theorem about the arbitrary monoidal category.

For the new bounded-above lemma I read `CochainComplexMinus.lean:32-273`, including zero-preservation, the finite diagonals of the bicomplex total, its upper-bound instances, `totalπ`, `minusResolutionFunctor`, naturality and the quasi-isomorphism instance. I also read Mathlib `LeftResolution/Basic.lean:35-135` and `LeftResolution/Reduced.lean:53-154`. The reduction uses exactly direct-summand stability; finite totals use exactly finite-biproduct stability. Resolving each term and totalizing is possible without choosing a bound as object data, because every diagonal has finite nonzero support whenever any upper bound exists. This explains why the lemma is not an objectwise existence lemma or a fixed-N recurrence. Its proof is not put into the new statement node.

For the new K-flat closure node I read `Flat/KFlat.lean:81-218` and the generic isomorphism-closure declaration in `Monoidal/KFlat.lean:38-42`. Tensor descends to homotopy, and K-flatness in complexes agrees with the homotopy formulation (`kFlat_quotient_obj_iff`). The zero, shift and triangulated instances supply precisely the listed closure conditions. The source's graded tensor assumptions are available here because all small coproducts exist and tensor preserves them; no braiding, symmetry or closed structure is needed. I recorded project declarations, with false transitive-sorry flags, rather than calling them Mathlib leaves.

For the new criterion I read all of `HomotopyCategory/DerivabilityStructure.lean:47-221`. Its property is closed under isomorphisms and triangulated, exactly as the new statement specifies. The auxiliary square goes from the preimage property on complexes to the property on the homotopy category. Its restricted quotient is a localized equivalence and the inverse square is Guitart exact, proved using cylinders. The generic transfer theorem itself is in Mathlib `OfLocalizedEquivalences.lean:60-64`, which I read, but that theorem alone does not supply this restricted quotient square. The functorial resolution is used upstairs on complexes. There is no unproved assertion that it preserves homotopies. This is why the complete criterion is a project interface and not a Mathlib leaf.

Step 1 uses the statement of `def-sp-grothendieck-abelian`, which explicitly gives small colimits and exact filtered colimits. The integer diagram is small and filtered. Flat objects' finite sum and summand closure is a blockwise kernel/image/cokernel calculation using the assumed additivity; no extra exactness of tensor is presumed for nonflat objects. Step 2 cites the new bounded-above lemma, whose statement explicitly quantifies over maps with different bounds and supplies the natural quasi-isomorphism and flat terms.

Step 3 uses only complexes and colimit universal properties, as stated by its two cited definitions. I checked the transition in degree n is a kernel inclusion, not an identity; each fixed degree becomes constant only after n exceeds that degree. Applying the *single* functor S produces strict compatibility, including for maps of input complexes. Step 4 proves the cohomology/colimit identification from the exactness in the cited Grothendieck definition, via the three displayed short exact sequences; it does not import an unlisted lemma on exact functors or assume injective transition maps.

Step 5 opens and applies `lem-sfb-bounded-above-flat-kflat`: its statement really gives the two-sided total-tensor conclusion for arbitrary abelian monoidal categories with the required exact integer colimits. The flat terms and upper bound come from step 2; all colimit and preservation hypotheses come from the item. Step 6 uses the actual tensor formula and definition of K-flatness in `def-sfb-preserves-kflat-quasi-iso`, plus the colimit definition. Both tensor directions, their signs and their morphisms are checked on the direct-sum summands, so the cited facts suffice. Exactness of colimits is supplied by step 4's explicit calculation.

Step 7 takes only the homotopy invariance and triangulated closure stated by the new K-flat node. Step 8 takes only the generic criterion's stated conclusion after checking each of its hypotheses against steps 3, 4, 6 and 7. It does not use a result from another unit as a substitute for the chosen route, nor the proof of an objectwise existence node as though that proof were its statement. All step citations have their exact quotation in `citations.json`.

For small cases I checked the zero complex (a quasi-isomorphism to zero is acyclic; no assumption that the original P sends zero to zero is made), complexes concentrated in one degree and their shifts (the bound may be negative), and an unbounded complex (only each truncation, never the original complex, is assumed bounded above). Finite sums/summands of flat objects pass the same blockwise exactness check in both tensor variables. For the criterion, the full homotopy category with the identity resolution and the zero property in the zero abelian category give the expected inclusions. The K-flat statement asserts stability under homotopy equivalence, not under arbitrary quasi-isomorphism to a K-flat complex. No statement dispute was found.

Against delivery-errors B-E: all new nodes are self-contained statements with no proof or proof dependencies; notation is TeX and definitions are cited or given inline. The searches in each record were actually run, their hits read, and second phrasings checked; no service outage has been treated as a negative search. Existing Stacks-tag neighbours are distinguished above. The split constructs R, its natural augmentation, its quasi-isomorphism and its two-sided K-flatness, instead of relocating either clause of the item into a new node. The only substantial construction delegated below it is the bounded-above functor, strictly smaller and without the unbounded, tensor or derivability conclusions. Every proof step is below 2000 characters; no long step hides a comparison lemma. The original statement and imported metadata are preserved.

## Unfinished work

The new bounded-above statement remains a stage-1 queue item; this is the authorized one-level split. The other two new interfaces are supported by the recorded existing project proofs. No Lean file was written and no compiler, Lake or local DAG/preflight checker was run. Delivery validation is performed by the required server tools.
