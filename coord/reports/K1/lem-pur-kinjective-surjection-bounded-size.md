1. Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-kinjective-surjection-bounded-size.json`: statement node, split; Mathlib searches found no match.
- `citations.json`: verbatim citations for every proof-step dependency.

2. Attachments: none.

3. WANTED: none; the Stacks source is available at `/home/ubuntu/c1-stacks-review/injectives.tex`.

4. What was wrong or incomplete: the imported proof had two false inferences. It tried to lift a map through the epimorphism `pi`, although `U` is only a generator, and it treated the image `M'` as a subobject of the coproduct. I repaired both points while retaining the three-step source argument. No duplicate DAG or blueprint statement was found, and no exact Lean declaration exists in the checked source.

5. What I could not finish: no child node was required; the auxiliary result is complete at this stage.

## Review by K1

I read Stacks `injectives.tex`, Lemma `lemma-surjection-bounded-size`, including its displayed coproduct construction. Step 1 uses the generator statement from `def-sp-grothendieck-abelian` on the proper inverse image `pi^{-1}(N')`; this inverse image is proper because `pi` is epi, so no lifting property is assumed. Step 2 uses the definition in `lem-pur-kinjective-set-iso-classes-bounded-size`: `M'` is a quotient of the coproduct `P`, hence subobjects of `M'` inject by inverse image into subobjects of `P`; the index coproduct embeds as a direct summand in the `|N|`-indexed coproduct. Step 3 uses the selected summand indexed by a proper subobject to contradict containment and proves surjectivity. I checked zero and one-subobject edge cases. I also reran the required LeanFinder, Loogle, grep, and LeanSearch queries; the first three found no matching Mathlib theorem and LeanSearch was unavailable. The return's two faults are explicitly corrected in Steps 1 and 2.

## Not duplicates

`lem-pur-kinjective-surjection-bounded-size` vs `lem-pur-kinjective-set-iso-classes-bounded-size`: the existing node concerns a set of isomorphism classes of bounded-size objects and quotient presentations; this item constructs a bounded-size subobject surjecting onto a specified quotient.

## Second reading by K1

- Item statement: checked against Stacks `injectives.tex`, Lemma `lemma-surjection-bounded-size`, hypothesis by hypothesis; verdict agrees.
- Step 1: checked the generator argument against the first sentence of the Stacks proof and `def-sp-grothendieck-abelian`; the repaired step takes the proper inverse image and chooses `phi_{N'}` directly, so it makes no invalid lift claim.
- Step 2: checked the coproduct image and cardinal estimate against the displayed construction and the size definition; the repaired step treats `M'` as a quotient of `P`, uses inverse images of subobjects, and uses the direct-summand inclusion into the larger coproduct.
- Step 3: checked the contradiction proving surjectivity against the final sentence of the Stacks proof; it uses the selected summand indexed by the alleged proper containing subobject.
- New node `lem-pur-kinjective-surjection-bounded-size`: statement-only form, self-contained hypotheses, TeX notation, source label, definition dependencies, blueprint fields, and recorded Mathlib searches all satisfy B1-B7; no child node exists.
- Repaired Step 1 to avoid lifting through `pi` and instead apply the generator to `pi^{-1}(N')`.
- Repaired Step 2 to avoid a nonexistent monomorphism `M'\\hookrightarrow\\bigoplus U` and use the quotient preimage injection plus the direct-summand bound.
