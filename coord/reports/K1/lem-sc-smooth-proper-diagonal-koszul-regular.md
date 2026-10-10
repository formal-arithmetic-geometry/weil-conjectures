1. Files written

- `dag/nodes/sec-picard-framework/lem-sc-smooth-proper-diagonal-koszul-regular.json`: repaired split into four proof steps.
- `dag/nodes/sec-picard-framework/lem-sc-koszul-regular-closed-immersion-perfect.json`: statement-only general perfectness consequence; Mathlib searches found no match.
- `citations.json`: verbatim quotes for every cited step.

2. Attachments

None. No exact sorry-free declaration for the item or the new child was found in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` or `Comparator`.

3. WANTED

WANTED: `literature/stacks-project/more-on-morphisms.tex`, Tags 067U and 068C, because that source file is absent from this checkout.

4. What was wrong or incomplete

The previous attempt marked all substantive steps elementary and left `proof_deps` empty. It also introduced a cyclic downstream dependency in the attempted helper. I removed that route. The repaired proof cites the existing regular diagonal theorem and regular-sequence-to-Koszul theorem, and adds only the strictly more general statement that a Koszul-regular closed immersion has perfect pushforward. Properness is elementary from the definition of proper morphism. The new child differs from the item because it applies to every Noetherian Koszul-regular closed immersion, not specifically to a smooth diagonal or its codimension.

## Not duplicates

`lem-sc-koszul-regular-closed-immersion-perfect` vs `lem-sc-smooth-proper-diagonal-koszul-regular`: the child is the general implication from Koszul-regular closed immersion to perfectness, while the item additionally proves smooth diagonal regularity, codimension, and properness.

5. What I could not finish, and why

The Stacks TeX source is unavailable locally, so the cited tags could not be read directly. Mathlib has no corresponding Koszul-regular/perfect-immersion declaration; LeanSearch was unavailable and recorded as such.

## Review by K1

I read the imported item, its unit and chapter records, the blueprint ancestor `lem-sc-finite-duality`, and the full statements of `lem-pur-diagonal-regular-immersion` and `lem-weil-pbc-regular-sequence-koszul-regular`. Step 1 uses only the former, which explicitly supplies a regular closed diagonal of pure codimension d. Step 2 uses that same statement for the local regular-sequence description and the latter node's explicit conclusion that every regular sequence in a ring is Koszul-regular. Step 3 uses the new child's verbatim statement, which gives the bounded finite-free Koszul resolution and the locally perfect pushforward. Step 4 is the direct definition-level argument that a closed immersion is separated, finite type, and universally closed, hence proper.

I verified the hypotheses against each cited statement: smoothness, separatedness, pure relative dimension, and the Noetherian base are present in the item; the diagonal target is the fibre product; and the new child assumes a Noetherian target. I tested the edge cases d=0 (finite etale diagonal) and a smooth projective line over a field (codimension one diagonal with a two-term Koszul resolution). I also checked the dependency graph: the item does not cite the downstream relative-duality node, so the prior cycle is removed.

## Second reading by K1

- Source check: Stacks Tag 067U, Lemma 31.23.11, states that an immersion between smooth schemes over the same base is regular; Tag 068C, Lemma 37.61.7, states that a Koszul-regular immersion is perfect. The local TeX checkout lacks `more-on-morphisms.tex`, so these tag pages were checked online and the missing local source is recorded above.
- Step 1: checked against `lem-pur-diagonal-regular-immersion`; its regular closed immersion and pure codimension conclusion is exactly what the short application uses, and the node is declared as the unit tool in the split report.
- Step 2: checked against `lem-weil-pbc-regular-sequence-koszul-regular`; the cited statement supplies regular-sequence implies Koszul-regular, preserving codimension from Step 1.
- Step 3: checked against the new child statement; it supplies the finite-free Koszul resolution and local perfectness used for the diagonal.
- Step 4: checked from the closed-immersion definitions; separated, finite type, and universally closed imply proper, and no extra hypothesis is used.
- New node `lem-sc-koszul-regular-closed-immersion-perfect`: statement-only, self-contained, all notions cite definitions, and its source is Tag 068C, Lemma 37.61.7. Removed the unsupported “regular sequence, equivalently Koszul-regular” wording and state the Koszul-regular hypothesis directly. Mathlib searches are recorded and found no declaration.
- Item statement: checked the diagonal target, smoothness, separatedness, pure relative dimension, perfectness, and properness on the edge cases d=0 and X=P^1 over a field; source labels were made exact.

Changes made: corrected the child to the precise Tag 068C hypothesis, retained the acyclic elementary application of the imported diagonal tool, and recorded the online source and all step verdicts.
