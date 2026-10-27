## Worker report

Files written:

- `dag/nodes/sec-six-functors/lem-sf-created-grothendieck-exact-integer-sum.json`: item, now split into nine steps; its statement is unchanged.
- `citations.json`: one entry per step/node citation, quoting the actual cited statement verbatim.
- `searches.jsonl`: actual Q74 searches logged by msearch.py.
- `report.md`: this report.

## New nodes

None. The split uses two existing Mathlib leaves, `lem-sfb-grothendieck-filtered-finite-limits` and `lem-weil-pbc-jointly-reflect-short-exact`, with existing definitions. The finite-subsum presentation is proved by its universal property, and exactness of finite biproducts is proved by componentwise kernel and cokernel factorizations; neither deserves a new node.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and for the relevant notions. `CategoryTheory.Endofunctor.IsoAlgebra.isGrothendieckAbelian` (Endofunctor/IsoAlgebra.lean:374) covers the special fixed-pair category, and `CategoryTheory.Endofunctor.IsoAlgebra.Free.preservesHomology_functor` (DerivedCategory/RightDerivedFunctor/IsoAlgebra.lean:57) covers its particular free functor. Neither states the present theorem for arbitrary abelian B, functors U and A, and a given pointwise orbit-sum isomorphism, or all the finite-subsum comparisons. Thus neither is an attachment for this item. No compiler or build was run.

## WANTED

None. The sources needed here are available locally.

## Issues and changes

The item was statement-only in the live repository and had no earlier sandbox split. I preserved the statement and all provenance and historical searches. Its source describes the generic argument extracted from the parent item's returned steps 5-6, rather than a separately numbered Stacks theorem: the proof therefore has `proof_origin.by = agent`. The definition and AB5 property are Stacks Tag 079B, `definition-grothendieck-conditions`, together with the following discussion. The finite-subsum argument is also used explicitly in `injectives.tex`, `lemma-F-G-monos`, whose proof I read. I expanded the universal properties instead of treating that use as a theorem statement.

I added the existing exact-functor, colimit and exact-sequence definitions to statement dependencies. In particular “exact” has its finite-limit and finite-colimit meaning from `def-galois-exact-functor`; the final step proves this formulation as well as preservation of short exact sequences. There is no statement correction or disputed clause.

`blueprint_refs.py ancestor` returns None. I retained this inherited provenance and its via list; no fabricated blueprint ancestor was inserted. The parent `lem-sf-fixed-pair-derived-forget-comparison` uses this item precisely to establish Grothendieckness and exact free induction. I read `dag/chapters/sec-six-functors.json`, `dag/units/sk-thm-sf-package.json`, and the package text in main-20261015: this is a categorical tool below clause (2), not a change to any chapter or unit route. No SGA source is used.

## Searches and reuse

I searched the whole DAG by titles and statements for AB5, exact filtered colimits, finite subsums, generators and reflection of exactness, and searched all imported blueprint nodes using `blueprint_refs.py search` for “Grothendieck”, “faithful generator”, “finite subsum”, “finite subsums”, “exact filtered colimits”, and “conservative exact”. The Grothendieck definition and the two generic tools already exist. `lem-weil-pbc-module-coproduct-small-subsum-diagram` is specifically about module sheaves with a particular small-universe presentation and is neither necessary nor a general statement for this item; I do not cite it.

The fresh Q74 msearch calls used two distinct natural-language phrasings in LeanFinder, a natural-language LeanSearch, the focused Loogle pattern `CategoryTheory.HasExactColimitsOfShape.domain_of_functor`, and a grep for transfer, separator and finite-subset coproduct results. All services answered. Search queries are recorded exactly as executed; historical Q125 queries remain untouched. I read the hits: Mathlib's `HasExactColimitsOfShape.domain_of_functor` (GrothendieckAxioms/Basic.lean:90) supplies a transfer ingredient; `AB4.of_AB5` supplies exact sums, and `CoproductsFromFiniteFiltered.liftToFinsetColimIso` (Limits/Constructions/Filtered.lean:165) supplies the natural presentation. None alone states the complete item, with its generator and the canonical kernel/cokernel comparisons. The existing finite-limit and detection leaves suffice for a proof without creating any new leaf. I read the detection theorem and all its hypotheses in Functor/ReflectsIso/Exact.lean:37-87 and the filtered-limit leaf's full statement.

## Not duplicates

No new nodes were created, so there are no new/existing pairs with a common tag to distinguish.

## Review by Q74

I checked the statement against Tag 079B in `injectives.tex`, including the precise “misses a proper subobject” convention for a generator, and against the actual implementation at IsoAlgebra.lean:228-233 and :366-383 and RightDerivedFunctor/IsoAlgebra.lean:54-58. This generic theorem needs abelian B, local smallness, a conservative exact U creating small colimits, and the stated adjunction. Those are all hypotheses, rather than facts inferred from the fixed-pair special case. Faithfulness is harmless but stronger than needed in the direct argument. No additional fullness of U is used: the adjunction-transfer search hits with a Full hypothesis are not applied.

For step 1 I opened `def-galois-exact-functor`, `def-sp-grothendieck-abelian`, and `def-weil-pbc-category-colimit`. Their statements supply precisely finite-limit/colimit preservation, existence of the image colimit, and its universal property. Creation and conservativity are the given assumptions, not claims drawn from a definition node. The proof explains how existence and preservation follow from creation.

For step 2 the exact-functor definition supplies preservation of kernels and therefore of monomorphisms. The definition of a proper subobject says that its monic representative is not an isomorphism; conservativity implies the same for its image. The chosen map from G then exists by the generator hypothesis, with the convention copied from Tag 079B. The displayed adjunction-naturality formula proves the required nonfactorization. This is an elementary use of the given hom bijection, and does not cite the special fixed-pair theorem as if it asserted the generic one.

For step 3 I opened `lem-weil-pbc-jointly-reflect-short-exact` and checked every hypothesis: both categories are abelian, U preserves finite limits and colimits and zero morphisms, and the singleton family is jointly conservative. Its statement really gives both directions of short exactness detection. The Grothendieck definition really supplies exact filtered colimits for A. Step 1 supplies the three colimit identifications and their arrows, so there is no missing comparison. Smallness is V-small throughout. B already has V-small Hom sets by hypothesis. The generator, all small colimits, and AB5 therefore give precisely Grothendieck B.

For steps 4-5 the cited abelian definition supplies finite biproducts, the Grothendieck definition supplies the full coproduct, and the colimit definition supplies the universal-property test. I explicitly checked that finite subsets form a small nonempty directed poset, including the empty subset, and that the transition maps compose on summands. Restriction to singleton legs and reconstruction of each finite leg are inverse operations. The formula on injections proves naturality, rather than merely asserting that the identifications transport the sequence.

For step 6 I read `def-sp-abelian` and `def-weil-pbc-exact-sequence`. I checked the finite kernel lift with the biproduct projections and its finite-sum reconstruction, and the dual cokernel descent with the coproduct injections. Both give uniqueness. For a short exact sequence the first arrow is its kernel and the second its cokernel in the abelian category, so the displayed component argument gives exactness of each finite subsum. This is the elementary finite-biproduct calculation, not an unproved infinite-sum exactness claim.

For step 7 I opened the full statement of `lem-sfb-grothendieck-filtered-finite-limits`. It explicitly says that for any V-small filtered I, colim preserves finite limits; this is stronger than only existence of filtered colimits, and it is exactly what the kernel comparison needs. The kernel shape is finite and Fin(I) has the right size. The Grothendieck definition also explicitly supplies preservation of short exact sequences under these filtered colimits. Steps 4-5 identify the canonical maps as well as the objects, establishing the full direct-sum exactness clause.

For step 8 the argument for cokernels is the written universal-property bijection, so it does not pretend that the finite-limit leaf states a cokernel theorem. Compatibility of the finite kernel/cokernel transition maps follows by uniqueness of their lifts and descents; naturality follows by cancellation of a kernel monomorphism or a cokernel epimorphism. This covers arbitrary maps of families, not just the original short exact families. In particular the comparison statements have not been weakened to abstract object isomorphisms.

For step 9 each P_n satisfies the finite-exactness hypotheses of the singleton detection leaf and is conservative because it is an autoequivalence. Z is a small set; no large colimit is taken. The assumed isomorphism UA with the sum is natural, which identifies both sequence arrows. The earlier singleton-U check then applies without a new hypothesis. I also checked the final kernel/cokernel comparison for A: applying U identifies it with the corresponding invertible comparison for UA because U itself preserves kernels/cokernels, and conservativity reflects its invertibility. Additivity and the kernel-of-difference descriptions give finite limits and, dually, finite colimits. This checks “A is exact” in the exact-functor definition, beyond merely quoting the conclusion about short sequences.

Small cases checked: zero category (G=0 is allowed), the empty family (its finite-subset poset has the empty object and all sums are zero), singleton and finite families (the full finite subset is terminal), zero maps (the kernel and cokernel comparisons reduce to the identity comparisons for X and Y), identity maps (zero kernel and cokernel), and the example A=B=Ab, U=id, A=id when no additional orbit-sum datum is imposed. With U=id and the orbit-sum datum imposed, the proof uses that datum only in step 9 and makes no claim that id is naturally a countable direct sum of identities.

I checked delivery-errors B-E against the actual files: no new node, no duplicate, no statement change, no unsupported source theorem, no cycle through the parent, no non-elementary claim cited from another node's proof, and no SGA route. Each non-elementary step names its exact existing inputs. Every elementary step writes the universal-property or coordinate argument. No step exceeds 2000 characters (the longest has 1138). The citation file quotes the actual statements verbatim for every listed use. Nothing remains mathematically unfinished in this one-level split; the remote dry run and push are the remaining delivery checks.
