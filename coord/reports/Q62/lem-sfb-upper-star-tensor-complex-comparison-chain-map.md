# Stage-1 report: lem-sfb-upper-star-tensor-complex-comparison-chain-map

## Files written

- `dag/nodes/sec-six-functors/lem-sfb-upper-star-tensor-complex-comparison-chain-map.json`: split into four elementary component calculations; statement preserved verbatim, monoidal-functor definition added to statement dependencies. No new nodes or Mathlib leaves.
- `citations.json`: seven verbatim statement quotations, covering every use in all four steps.

## Attachments

None. I searched the live `lean/WeilConjectures/` by the exact blueprint tag, `upperStarTensorComplexHom_comm`, and pullback/tensor-comparison notions. `AlgebraicGeometry.ProEtale.CondensedRing.upperStarTensorComplexHom_comm` in `SixFunctors/ProEtale/ModuleObject/Derived/Monoidal.lean:148-157` still has proof `sorry`. Its declaration is exactly the adjacent-degree equation in the item (Lean's relation says that the second degree is the first plus one). The arbitrary-integer differential relation poses no additional case.

The generic `CategoryTheory.Functor.mapCochainComplexμIso` and `ιTensorObj_mapCochainComplexμIso_hom_f` in `WeilConjectures/Algebra/Homology/Monoidal/MapHomologicalComplex.lean:48-86` construct a different named complex comparison and describe its components, under coproduct-preservation instances. Neither declaration directly states this item's equation for `upperStarTensorComplexHomX`; an identification by coproduct uniqueness is still required. They are not claimed as an exact attachment.

## WANTED

None. All definitions needed for this elementary proof are available locally.

## Findings and changes

The imported proof was empty. Its statement agrees with the upstream concrete component construction, so there is no statement dispute. The latest blueprint ancestor is `literature/blueprint/latest/blueprint/sec-six-functors/sk-lem-sf-open-ctf/sk-prop-proper-image-localizing-open.md`, id `det-proper-image-localizing-open`; its current text has the extension-by-zero statement and no component-level proof. This obligation originates in the upstream module's Complexes construction (docstring step 1, lines 30-36; sorried-input explanation at lines 60-62). The proof is therefore correctly marked as written by an agent, using the signed total and naturality definitions from Stacks. The inherited source and all upstream audit fields are retained.

The unit and chapter records were read, and the latest unit text was checked. This auxiliary item is not the unit key statement, so no unit realization fields are changed. The inherited blueprint `from` and `same_as: []` are retained; whole-blueprint searches for `tensor differential`, `upperStarTensor`, `tensorator`, `complexes tensor`, and `comparison differential` found no equivalent blueprint node. The ancestor utility currently follows the audited item's creation links to None rather than the stored blueprint ancestor; since no new node is created, this causes no fabricated ancestry record.

The important distinction is that this direction of comparison is constructed out of the source coproduct. Its chain equation needs only the given natural monoidal comparison and additivity. It does not require preservation of coproducts, a chosen inverse, an exactness theorem, flat complexes, boundedness, or a derived-category identification. No underived-versus-derived isomorphism is asserted here.

## Searches and existing related material

All fresh Mathlib searches were run through the required msearch command and are retained exactly in `searches.jsonl` and appended to the item's prior search records. Both natural-language phrasings were read. The hits `HomologicalComplex.tensorHom`, `ιTensorObj`, `mapBifunctorDesc`, `ι_mapBifunctorDesc`, `map₂CochainComplex`, and shift/flip comparison lemmas do not assert the tensor comparison for an arbitrary additive lax monoidal functor. In particular `tensorHom` tensors two existing maps inside one category. The two greps of `Algebra/Homology` and the Loogle query are recorded with their actual results. No failed service was represented as an empty search. Relevant source read: Mathlib `Algebra/Homology/Bifunctor.lean:150-173`, `Algebra/Homology/Monoidal.lean:45-65`, and `CategoryTheory/Monoidal/Functor.lean:620-640`.

The existing DAG node `lem-sfb-termwise-strong-monoidal` is substantially more general: it gives an isomorphism, naturality and monoidal coherence, with extra colimit assumptions. It was opened and read; its statement is not used without verifying those assumptions. Rather than introduce any version of its elementary signed calculation as another node, this item's proof writes that calculation directly. The existing definitions `def-sfb-module-upper-star`, `def-sfb-preserves-kflat-quasi-iso`, `def-sfb-strong-monoidal-functor`, and `def-weil-pbc-category-colimit` suffice. No new lemma merely restates a clause of the item.

## Unfinished work

None within stage 1. The upstream Lean proof remains `sorry`; no Lean file was written and no compiler, Lake, or build was run.

## Not duplicates

No new nodes. The related stronger termwise-monoidal node is discussed above; all needed primitive definitions are reused.

## Review by Q62

I read the upstream `Monoidal.lean` docstring and exact definitions at lines 132-168, and the strong-monoidal module pullback construction in `UpperLowerStar/MonoidalModule.lean`. I checked the mathematical convention against Stacks `homology.tex`, Tag 0A5J (`example-double-complex-as-tensor-product-of`), and Tag 012Z (`definition-associated-simple-complex`): the first differential is unsigned and the second is multiplied by (-1)^p. I also read `categories.tex`, Tag 0FFL (`definition-functor-monoidal-categories`) for functoriality of the tensorator, and Tag 002F (`definition-colimit`) for uniqueness. These are the only categorical facts used, beyond the item's given data.

For step 1 I opened `def-sfb-module-upper-star` and verified its statement explicitly says that f* is additive. I opened `def-weil-pbc-category-colimit` and verified its unique factorization statement applies to the countable discrete family indexed by p+q=n. The map c on each inclusion is the equation given in the item, not a theorem inferred from a sorried construction. The target differential is just termwise application of F.

For step 2 I opened `def-sfb-preserves-kflat-quasi-iso` and checked that its statement explicitly gives both summands of the signed total differential. Additivity is again quoted from `def-sfb-module-upper-star`. Thus F of the two-term sum and its sign can be expanded without claiming it preserves any infinite coproduct. This is a finite additive calculation.

For step 3 I opened `def-sfb-strong-monoidal-functor` and copied its actual tensorator-naturality equation. The supplied comparison in the item is the monoidal comparison, so its naturality is part of that data; this step does not use a definition node as a theorem establishing monoidality of f*. Applying that equation with (d_A,1) and (1,d_B) gives precisely the displayed identities. The next substitutions use only the defining components of c in degree n+1. Every source and target matches: the first term lands through (p+1,q), the second through (p,q+1).

For step 4 the same tensor definition applies to FA and FB, whose differentials are F(d_A) and F(d_B). Comparing the expanded expressions gives equality on each summand; the colimit definition's uniqueness then proves equality of the maps. Composition distributes over the two-term sums in these additive module categories. All four steps are elementary because they expand definitions or substitute the stated naturality equation, with no hidden comparison lemma; each is under 700 characters and none approaches the long-step threshold.

I checked zero complexes and zero differentials, complexes concentrated in a single degree, and a nonzero second differential with p odd (including p=-1): both expressions acquire the same negative sign. Even p gives the unsigned second term. The argument applies equally to unbounded complexes since it never sums morphisms over infinitely many bidegrees: it checks each inclusion separately. The identity pullback is the identity calculation. No hypothesis on f beyond a scheme morphism was used, and no finite-coefficient or smoothness assumption entered. No new statement needs a separate small-case test. There were no returned points to repair. I corrected the initially missing monoidal-definition dependency and gave each use a verbatim quotation. Server `review_split` already returned PASS before this report was written; the mandatory full dry run and delivery follow.

The first full dry run rejected the 35-character additivity sentence under its minimum quotation-length rule. I expanded those two citations to the contiguous closing sentences of the same statement, retaining the exact additivity assertion; the mathematical split did not change.
