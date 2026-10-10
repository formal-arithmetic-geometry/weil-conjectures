# Stage-1 split: lem-sc-p1-pullback-extension-class

## Files written

- `dag/nodes/sec-picard-framework/lem-sc-p1-pullback-extension-class.json`: item, split in three steps.
- `dag/nodes/sec-picard-framework/lem-sc-p1-extclass-morphism-naturality.json`: statement-only Mathlib leaf, `CategoryTheory.ShortComplex.ShortExact.extClass_naturality` at `Mathlib/Algebra/Homology/DerivedCategory/Ext/ExtClass.lean:131-137`.
- `citations.json`: exact statement excerpts for the item's three citations.

## Attachments

None. A search of `WeilConjectures/` for the item ID, pullback extension class, and related Ext declarations found no declaration stating this item. `Ext/Map.lean` has a related exact-functor theorem, but it has a different conclusion.

## Sources and corrections

The repository's `literature/stacks-project/` and blueprint text are not materialized in this checkout. I read the available Stacks source at `/home/ubuntu/c1-stacks-review/homology.tex`, section `homology-section-extensions` (Tag 010I), especially its definition of the pullback extension and displayed diagram at lines 1323-1342; and `/home/ubuntu/c1-stacks-review/derived.tex`, section `derived-section-ext` (Tag 06XP), especially the derived-category definition of Ext at lines 8625-8645 and the Yoneda class roof at lines 8809-8827. The source tag-to-label mapping is in `/home/ubuntu/c1-stacks-review/tags/tags`. The new Mathlib leaf cites the exact declaration in `ExtClass.lean:131-137`, which is where I read its statement.

The imported item had no proof. Its existing statement and dependencies are retained. Its earlier Mathlib searches omitted `extClass_naturality`; the item now records that declaration as a candidate, while the new general naturality node records it as an exact Mathlib match. The item itself is not a one-line specialization: it also constructs a pullback short exact sequence and its morphism to the original sequence.

## Not duplicates

`lem-sc-p1-extclass-morphism-naturality` vs `lem-sc-p1-pullback-extension-class`: the new node treats an arbitrary morphism of two short exact sequences in any abelian category; the item constructs a particular pullback of sheaves and determines its class.

`lem-sc-p1-extclass-morphism-naturality` vs `lem-sc-p1-ext-pushout-postcompose`: the existing node treats the class of a pushout along a kernel map, whereas the new node states general naturality for every morphism of short exact sequences.

## Review by G1

I compared the item with Stacks 010I and 06XP. The item assumes a scheme, a short exact sequence of modules, and a map into its quotient; these are exactly the data of the pullback extension in 010I. The new node assumes an abelian category with Ext, two short exact sequences, and a morphism between them, exactly the hypotheses of Mathlib's `ShortExact.extClass_naturality` at `ExtClass.lean:131-137`. Its displayed equality has the same orientation after writing Mathlib's `Ext.comp` in derived-category composition notation. I searched the whole DAG for the statement, for Tag 06XP, and for `extClass_naturality`; `tools/blueprint_refs.py search` found no blueprint duplicate. I also checked the pushout node's statement, which is different.

Step 1 uses no external theorem: on each stalk, the fiber product is the pairs `(e,c')` with `p(e)=u(c')`; projection to `c'` is onto because `p` is onto, and its kernel is the image of `A` because `A=ker p`. This verifies short exactness and gives the sequence morphism `(id_A,q,u)`. Step 2 cites `def-sc-ext-sheaf` only for the fact that these sheaf modules form the abelian category in which Ext is taken; it cites the new naturality node for the equality with components `(id_A,u)`. Both quoted statements say these things. Step 3 cites `lem-sc-p1-ext-yoneda-functoriality`, whose statement identifies contravariant Ext action with precomposition by `u`; the step applies it with `i=1`, `F=C`, `G=A`, `e=delta`.

I checked the hypotheses for each application: the original sequence is short exact by assumption; the pulled-back one is proved short exact in step 1; the maps commute by the defining fiber-product equation. As small cases, `u=id_C` returns the original extension and its class, and `u=0` gives a split pullback with zero class, agreeing with precomposition by zero. I corrected the missing proof and made the source of the pullback construction Tag 010I rather than attributing that construction to Tag 06XP. No source error or unit-route departure was found. The new Mathlib leaf has no proof steps or proof dependencies.

## Unfinished

Nothing in this one-level split. No Lean was written or compiled.

## Second reading by G1

- Item statement: checked against Homology Tag 010I, label `homology-section-extensions` (definition of Ext and pullback) and Derived Tag 06XP, label `derived-section-ext` (Ext and Yoneda class); hypotheses and conclusion agree, including the scheme and sheaf-module setting.
- Step 1: checked against Tag 010I and the fiber-product definition; the stalkwise kernel and surjectivity argument is elementary and supplies the required morphism of short exact sequences.
- Step 2: checked against the existing node `lem-sc-p1-ext-class-naturality` and [def-sc-ext-sheaf]; its statement gives exactly the naturality equality used for the pullback morphism, with identity left map and `u` right map.
- Step 3: checked against `lem-sc-p1-ext-yoneda-functoriality`; its contravariant formula gives the displayed `Ext^1_X(u, A)` image.
- New-node audit: the proposed `lem-sc-p1-extclass-morphism-naturality` was a duplicate of existing `lem-sc-p1-ext-class-naturality` (same Mathlib declaration and same naturality statement), so it was removed and step 2 retargeted to the existing leaf. No new nodes remain.
- Edge cases checked: `u = id` returns the original extension class; `u = 0` gives the split pullback and zero class; the zero sheaf and one-point scheme reduce to the corresponding module statement.
- Repairs made: corrected the item's `created.item` label, retargeted step 2 and `citations.json` to the existing naturality leaf, removed the duplicate node, and replaced source places with Stacks tags plus labels.
