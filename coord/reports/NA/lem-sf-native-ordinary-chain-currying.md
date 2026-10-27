# Worker report: lem-sf-native-ordinary-chain-currying

## Files written

- `dag/nodes/sec-six-functors/lem-sf-native-ordinary-chain-currying.json`: statement, split; no exact Mathlib match. Its five steps construct the product lift and check its chain-map equation explicitly.
- `citations.json`: verbatim statement quotations for every cited node at every step.
- `searches.jsonl`: actual searches made with the prescribed msearch command; the live item's earlier search records remain in the item and are inherited evidence, not searches claimed as run here.

New nodes: 0. New Mathlib leaves: 0. The small universal-property arguments and sign calculation belong in the proof, rather than being made nodes.

## Attachments

None. Searches for the exact blueprint tag and for ordinary/native currying under `lean/WeilConjectures/` found no declaration giving this assertion. The relevant `NativeCurrying.internalHomEquiv` and `internalHomEquiv_f_π` are private constructions in `lean/Sheaf/Paper/NativeOrdinaryRepresentativeCurrying.lean`, not declarations of the required project root `WeilConjectures/`. They are source material for the convention check, not an ATTACH claim.

## WANTED

None.

## What needed repair

The live item was statement-only. Its statement, its statement dependencies and the exact native models are preserved. Stacks Tag 0A90, `sites-cohomology.tex`, label `lemma-compose`, gives the related Hom-complex isomorphism but omits its proof and uses the usual Hom convention. It is not quoted as a ready-made theorem about the native row differential. I supplied the degree-zero calculation and marked its proof origin as agent-written. The nearby Hom-complex section spells out the conventional differential, making the convention distinction explicit.

There is no statement dispute: unsigned degree-zero currying is correct precisely because of the factor (-1)^p in the native row differential. It would be wrong to silently substitute the usual Hom differential. No K-flat replacement, K-injective resolution, derived equivalence, signed flip or derived representative normalization is used.

The archive-list command returned no matching abandoned directories across all groups. The active sandbox contained only dispatcher brief markers, so I copied the live item without replacing earlier work. No repair note exists for the item. `blueprint_refs.py ancestor` returns None, agreeing with the live null ancestor. I retained that ancestry and its via list and supplied the exact current blueprint paragraph in the split report. The chapter and unit were read; this is a chain-level tool below the native comparison route, not a change to their statements or proofs.

## Search evidence and reuse

Whole-DAG searches by `ordinaryTensorTotal`, `bifunctorHom`, row differential, currying, additive adjunctions and the relevant declaration names were followed by reading the statements of `lem-sf-site-tensor-hom-equiv`, `lem-sf-kflat-bifunctor-tensor-hom`, `lem-sfb-ringed-site-dg-tensor-hom`, `lem-sf-native-weil-chain-uncurry-forget`, `lem-sf-adic-module-tensor-hom-comparison` and `lem-sf-native-ordinary-representative-currying`. The first is a sectionwise ringed-site result; the others require derived data, K-flatness or a prescribed uncurrying map, or concern a different differential. None is used to justify the strict arbitrary-complex assertion.

Whole imported-blueprint searches for `currying`, `row-sign`, `additive adjunction` and `strict currying` found no statement equal to this one (the currying search returned three broader blueprint nodes). The current blueprint source read was `literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/cor-coef-verdier-weil-equivariance.proof.md`, specifically its internal-Hom comparison/evaluation/transposition paragraph.

The new logged semantic searches used two phrasings for strict currying, plus a search for its additive adjunction support. LeanSearch returned ordinary closed-category curry and module curry, not a chain-complex adjunction. LeanFinder returned tensorHom, tensorObj, total inclusions and totalDesc. Their reported signatures describe tensor morphisms and universal maps, not currying into the row-sign Hom. The support query returned `CategoryTheory.Adjunction.homAddEquiv`; I read `Mathlib/CategoryTheory/Adjunction/Additive.lean:32-100`, including the definition at line 53, and `Parametrized.lean:44-113`, including the three naturality identities at lines 98, 107 and 112. Those facts are available in Mathlib but the few-line specialization is written directly from the assumed adjunction in step 1. It is not made into an unnecessary new node. Logged greps of `Algebra/Homology` and `Algebra/Homology/Monoidal.lean` found no native Hom/currying comparison. Loogle confirmed the ordinary naturality lemmas, not the desired chain-map theorem. Every new search recorded in the item is copied from the command's actual log, with its precise query text; none of these services was unavailable.

## Not duplicates

No new nodes are created, so there are no new/existing-node pairs to distinguish.

## Review by NA

I read Tag 0A90 (`lemma-compose`) and the preceding sheaf Hom-complex construction in `sites-cohomology.tex`; I also read the live ordinary bifunctor definitions in `NativeWeilClosedModels.lean:42-105`, the explicit native currying definitions/projection equation in `NativeOrdinaryRepresentativeCurrying.lean:240-267`, and the actual row differential in `BifunctorHomComplex.lean:146-151`. The prime and scheme are arbitrary throughout the ordinary part: the finite-field and Frobenius data of the larger closed-model interface are not used to add hypotheses to the item. No new node or external source requires review, and no forbidden source is used.

Step 1 uses exactly the sentence of `def-sf-native-weil-closed-models` defining ordinary Hom by precomposition/postcomposition, and the full statement of `def-weil-preadditive-category` for bilinearity of composition. The chosen currying equivalence is the ordinary adjunction expressly assumed by the item. Its unit formula proves additivity in two lines; all three naturalities are part of that adjunction with its ordinary Hom bifunctor. This does not take additivity of a derived functor from a definition. I read both cited statements and quoted their actual relevant wording.

Step 2 uses the defining existence/uniqueness property of the products already specified in the item, once for each q; it does not need exactness of products, interchange of limits, a finite direct sum, or an existence theorem about a new category. The inverse identity is the ordinary adjunction's inverse identity. Those one-line uses of definitions are elementary, and no theorem is cited covertly.

Step 3 cites `def-weil-abstract-derived-category` only for its explicit definition of a morphism of complexes. Its statement says precisely that the component maps commute with differentials; it is not being used for a derived adjunction. Restriction to a tensor summand and bilinear distribution give the displayed equality, with the p sign of the first curried variable. The tensor order stays Q^q tensor P^p in every map. Degrees of both terms on the right are p+q+1, matching the output differential.

Step 4 applies the three ordinary naturality identities separately, recording which variable each one concerns. After additivity, subtracting the P term and multiplying by (-1)^p is the whole argument. In particular the P term uses b_(p+1,q), not b_(p,q+1). This explicit rearrangement is a few-line elementary calculation, not a hidden comparison lemma. Step 5 uses the given row-differential formula and the defining uniqueness property of the product. The quoted definition of a complex morphism is exactly what turns the resulting equality into a chain map. Its unsigned normalization is the inverse identity already proved in step 2.

I checked the small cases: zero complexes give the zero lift; complexes concentrated in degree zero recover ordinary currying; an odd row p=1 or p=-1 reverses both signs as required; an even row p=0 gives the usual subtraction; in characteristic two both minus signs become plus and the same identity holds. All indices range over the integers and the argument neither sums an infinite family nor restricts to finitely many nonzero terms. Thus arbitrary unbounded complexes are included, with no boundedness, flatness, injectivity or exact-product hypothesis introduced. No coefficient category is transported to another one. These checks also show why dropping the row sign would break step 4.

Against delivery-errors B--E: all objects of the item remain introduced in its statement; there are no new statements or data definitions, and all TeX is encoded with single logical backslashes. Every citation was checked against the cited node's statement and recorded verbatim in citations.json. All five steps are elementary instances of stated definitions, naturality of the assumed adjunction or the displayed algebraic identity, with lengths below 1000 characters each. No content is moved into a new node, no derived theorem is invoked on unsuitable representatives, and no cycle or off-unit theorem edge is introduced. I corrected the initially tempting use of the broader K-flat derived adjunction by not using it: the proof instead checks the strict component equation directly.

## Unfinished work

None in this stage-1 split. No Lean file was written, no compiler or Lake command was run, and the shared repository and launcher were not modified. Required server dry-run and delivery results are recorded below once they complete.
