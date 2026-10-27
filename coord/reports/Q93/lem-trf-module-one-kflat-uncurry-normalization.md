## Files written

- dag/nodes/sec-trace-formula/lem-trf-module-one-kflat-uncurry-normalization.json — statement, now split in five steps; no Mathlib match.
- citations.json — fourteen verbatim statement excerpts, one for every step/node citation.
- New nodes: none. New Mathlib leaves: none.

## Attachments

None. I searched the live WeilConjectures source for the exact blueprint tag and for one-K-flat and uncurrying terminology. The nearby TensorCounitOneKFlatCoordinates theorem concerns pullback counits, not this product-Hom transpose. The existing Sheaf oneKFlatChainTranspose theorem has a sorry and assumes the flat-term second-factor model; it is a DAG input, not an attachment for the item.

## WANTED

None. The Stacks sources needed for this argument are present.

## Problems found and corrections

The live item was unsplit, without a proof or Lean audit declaration. Its statement is well typed and true: no statement correction or additional hypothesis is needed. The only subtlety is that the existing one-sided transpose lemma assumes flat terms for its second factor. Applying it directly to V would be invalid. Instead I resolve V by P with flat terms, apply it to (U,P), and descend the equality by an explicitly written tensor naturality square and Hom naturality square. A resolution F of U also checks that the one-sided comparison in that input is exactly the inverse native tensorator required by this item.

I retained the item's original statement, source, parent route, inherited searches and maintainer-owned fields. New searches appended to mathlib_searches exactly match searches.jsonl, whose answers I read. LeanFinder returned Tor infrastructure and generic localization comparisons; LeanSearch returned abstract MonoidalClosed.uncurry and tensorBifunctorIso. I read their source, and also Adjunction.derived and derivedε_fac_app. None proves the normalized module-complex equation by a one-line specialization: they need the representative and derived-functor compatibilities this argument establishes using existing DAG nodes. The grep hits in Homology/Monoidal and Double concern total tensor construction and unrelated adjunctions. The second LeanFinder phrasing likewise gave no exact match. The inherited earlier searches are retained as historical records, not newly claimed searches.

## Unfinished work

None in this one-level split. Existing cited nodes remain their own items; no new unsplit obligation is introduced. Independent maintainer review remains part of the delivery protocol.

## Not duplicates

No new nodes. Whole-DAG and whole-blueprint searches for 0A65, uncurry, internal hom, one-K-flat and tensorator located the existing one-sided transpose and native tensor results, which are reused. The existing lem-sfb-hom-kflat-chain-transpose assumes a flat-term second factor and does not cover the original item when only U is K-flat; the resolution and cancellation steps supply the missing extension. No blueprint node found states this precise equation under the original either-factor hypothesis.

## Review by Q93

I read the chapter and unit records, the current blueprint ancestor lem-trf-local-term-locality, and the inherited path through the double-evaluation normalization. This item is a generic algebra input to that established route, not a new proof of the local-term unit. I read more-algebra.tex Tag 0A65 (lemma-internal-hom) and its preceding equation-internal-hom construction, and Tag 0A5Y (lemma-compose), including the product and direct-sum indexing and the differential signs. I also read sites-cohomology.tex Tag 08J9 (lemma-internal-hom), Tag 06YS (lemma-K-flat-resolution), and Tag 0A95 (lemma-RHom-well-defined). There are no new-node sources to check. I checked delivery-errors B–E against the actual statements and these source passages, as follows.

Step 1 uses the statement of lem-pc-kflat-resolution, which really gives a quasi-isomorphism onto every unbounded complex with a K-flat source and flat terms. On the terminal one-object site all module-sheaf constructions reduce to ordinary modules, so it applies to both V and U. The definition of localization in def-weil-abstract-derived-category makes their images invertible. Neither boundedness nor any flatness of U or V is introduced. The auxiliary F is used only to pin the comparison in step 3.

Step 2 uses the exact product Hom differential and functorial total tensor in the cited definitions. Precomposition q sends each actual Hom component to evaluation at qz, so the displayed equation uses the hypothesis on phi and psi literally, without an interchange sign. I read lem-weil-pbc-module-tensor-hom-currying and its Mathlib source TensorProduct.ext' and lift.equiv in LinearAlgebra/TensorProduct/Basic.lean (lines 134, 188–199). It supplies equality on each module tensor summand; the direct-sum universal property gives equality of the total maps. This is an elementary step with the needed generic uniqueness result cited, not an unproved claim that a chain map exists: both maps already exist by composition.

Step 3 uses the statement, not the proof, of lem-sfb-hom-kflat-chain-transpose. Its first complex is unrestricted; its second has flat terms and is K-flat; its target is K-injective. P and I meet exactly those hypotheses. Its statement includes the pure-tensor normalization, naturality, and compatibility with representative quasi-isomorphisms. The native-tensor statement gives a natural comparison agreeing with simultaneous K-flat comparison, so testing both comparisons on F,P gives the same right side. The cited module K-flat definition explicitly includes preservation of quasi-isomorphisms on either side, making Q(T(a,1)) cancellable. The derived-Hom definition identifies the canonical representative comparison with j, including an arbitrary K-injective target rather than only a chosen replacement. This is where I avoided the invalid shortcut of silently assuming the two tensor comparisons are identical.

Step 4 uses precisely the invertibility and naturality clauses of lem-sf-ringed-derived-native-tensor. The pair (U,P) has its second factor K-flat, and the pair (U,V) has one K-flat factor by the original disjunction. Thus both inverse comparisons used in the formula exist. I wrote the naturality equation before rearranging its inverses and composing with Qpsi; no claim that arbitrary tensor preserves q is needed. For the Hom square, def-pur-derived-internal-hom explicitly defines the bifunctor by localization. I checked lem-pur-rhom-well-defined: q is a quasi-isomorphism and the target map is 1_I between K-injectives, satisfying all its hypotheses. It states exactly the induced precomposition quasi-isomorphism, not merely the definition of K-injectivity.

Step 5 uses the three-variable naturality actually stated in lem-sf-ringed-derived-closed-symmetric-monoidal. The variance is contravariant in the second tensor argument: precomposing A with 1 tensor h matches postcomposing its transpose with RHom(h,1). I checked both sides' sources and targets. Since h is invertible, the functorial derived-Hom definition gives inverse RHom(h inverse,1); cancelling it is elementary. The proof never swaps U and V, so it never introduces a Koszul symmetry sign or assumes the other factor is flat.

For small cases I tested V=0, U=0 and the zero ring: the same argument and identities give zero maps and no nonzero-unit assumption. For complexes concentrated in degrees p,q with zero differential, the formula is ordinary evaluation into degree p+q without a sign. The odd/odd case still has no sign because no swap occurs. A nonflat module in one slot with R in degree zero in the other is covered, including when only U is K-flat; the resolution P, rather than V, is the flat-term second factor. Infinite unbounded complexes cause no finite-support assumption on Hom: all components are evaluated through the product projections, while maps from the direct-sum tensor are determined summandwise. All five steps are below 2000 characters and contain no hidden standalone comparison lemma: the comparison equality is the single naturality square followed by cancellation, written in full.

I checked that every proof dependency is exactly the union of the step uses, every quoted excerpt is a literal substring of its cited statement, and none of the cited nodes depends on the item (also checked transitively for the main inputs). I declared the off-unit homological algebra tools in split_report.tool_uses, with reasons, rather than setting the maintainer's tool_uses field. There are no statement-only nodes carrying proof text, no duplicate or restated clause nodes, no unsupported Stacks references used as facts, and no Lean writing, compilation, repository edits or direct git commands.
