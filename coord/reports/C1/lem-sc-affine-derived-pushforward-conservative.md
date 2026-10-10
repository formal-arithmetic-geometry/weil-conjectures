1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-affine-derived-pushforward-conservative.json`: item, split proof, no Mathlib match.
- `citations.json`: verbatim statement quotes for both proof steps.

2. Attachments: none. I searched the slopmaster2 source for the item id, blueprint tag, affine derived-pushforward terms, and likely theorem names; no sorry-free exact declaration exists.

3. WANTED: `literature/stacks-project/perfect.tex`, Tags 0AVW and 08I8, for the affine derived equivalence and conservativity inputs.

4. The imported item had no proof. I found the existing DAG node `lem-sc-finite-affine-derived-equivalence`, which is strictly more general than the needed conservativity statement and is not a restatement of the item. The proof first uses its explicit composite description of `Rf_*` and the elementary fact that restriction of scalars reflects isomorphisms, then uses that an equivalence reflects isomorphisms. The item remains unchanged and no new node was created. Mathlib searches were run for the item with LeanFinder, Loogle, grep, and LeanSearch; LeanFinder and grep found only ordinary sheaf declarations, Loogle found no match, and LeanSearch was unavailable.

## Review by C1

I read the item source as Stacks Project `perfect.tex`, Tag 08I8 (label `lemma-affine-morphism`), and the supporting affine-equivalence source at Tag 0AVW. The hypotheses are unchanged: `f` is affine, `E` and `F` are objects of the quasi-coherent derived category, and the conclusion is reflection of isomorphisms by `Rf_*`. I also opened the cited node `lem-sc-finite-affine-derived-equivalence`; its statement explicitly supplies an equivalence `Phi` and says that composing it with restriction of scalars is `Rf_*`.

Step 1 uses exactly that equivalence/composite statement. The only additional argument is elementary module theory: an inverse to an isomorphism after forgetting the `f_* O_X`-action is automatically linear. Step 2 uses the same cited statement for the equivalence and the standard fact that an equivalence reflects isomorphisms. The two steps together give the item's exact morphism-level conclusion, with no circular citation to the t-exactness node. I checked the identity affine morphism and an affine scheme map `Spec A -> Spec B` as small cases; both reduce to restriction of scalars along `B -> A`, which reflects isomorphisms. The split passed JSON validation before the dry run.
## Second reading by C1

- Item statement: checked against Stacks `perfect.tex`, Tag 08I8 (`lemma-affine-morphism`); hypotheses and conclusion agree exactly.
- Step 1: checked against Tag 0AVW and `lem-sc-finite-affine-derived-equivalence`; the composite description supplies `Rf_*`, and the cone argument is elementary.
- Step 2: checked against Tag 08I8 and the same equivalence node; a quasi-inverse reflects isomorphisms elementarily.
- New nodes: none; the existing cited node was read in full and supplies both facts used.
- Edge cases: identity and affine `Spec A -> Spec B` maps, zero morphisms, and empty schemes behave as stated.
- Searches: all recorded searches were checked; no matching Mathlib or slopmaster2 declaration exists.

Changes made: made both categorical reflection arguments explicit and marked both steps elementary. No statement, source, dependency, or citation quote changed.
