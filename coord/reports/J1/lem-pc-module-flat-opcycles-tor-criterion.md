1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-module-flat-opcycles-tor-criterion.json`: statement split, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-module-opcycles-tor-surjection.json`: statement-only child, no Mathlib match.
- `citations.json`: verbatim citations for the item proof.

2. Attachments: none.

3. WANTED: `literature/stacks-project/more-algebra.tex`, More on Algebra Lemma 15.59.2 (Tag 0653), for the Tor_1 quotient argument and flatness conclusion.

4. The imported item had no proof. I checked the exact statement against the Tag 0653/0654 wording recorded in the node and retained its hypotheses and conclusion. The non-elementary homological input is isolated as `lem-pc-module-opcycles-tor-surjection`; it says precisely that the preceding tensor homology surjects onto Tor_1 of the degree-a cokernel. Step 1 uses that statement. Step 2 uses only the item's exactness hypothesis and the meaning of zero, so it is elementary. Step 3 uses the existing `lem-weil-pbc-flat-tor-ideal-criterion`, whose statement explicitly gives flatness iff Tor_1 against every ideal quotient vanishes. I read that node and verified that its conclusion applies to the same cokernel Q. Mathlib searches for both nodes found only generic flatness/opcycle declarations, with no matching Tor statement. The source TeX is not present in this checkout, so the proof origin is marked agent-written and the source is listed as WANTED.

## Review by J1

I read the item, its ancestor `lem-sc-finite-duality`, the dependent flat-model node, and the cited ideal-Tor criterion. I checked that every proof step names the statement it consumes, that the ideal criterion supplies exactly the final flatness implication, and that the hypothesis quantifies over all modules before specializing to `A/I`. I also checked edge cases such as `a` at either end of a bounded complex and `I=0` or `I=A`; these impose no extra condition. The only missing material is the unavailable Stacks source text, recorded above rather than silently claimed as read.

## Not duplicates

lem-pc-module-opcycles-tor-surjection vs lem-pc-module-flat-opcycles-tor-criterion: the new node gives a natural surjection from preceding tensor-complex homology to Tor_1 of the opcycle cokernel; the item concludes flatness from vanishing of that Tor group for all modules, so the new node is a homological input rather than a restatement of the conclusion.

## Second reading by J1

- Item statement: checked against the recorded Tag 0653/0654 truncation argument and the existing ideal-Tor criterion; repaired the module/sheaf mismatch by making the one-point-site specialization and ordinary module flatness explicit.
- Step 1: checked that the cited surjection node states the required map for every A-module N; verdict sound after the statement repair.
- Step 2: checked exactness in degree a-1 gives zero cohomology, and a surjection from zero forces Tor_1 to vanish; verdict elementary and sound.
- Step 3: checked the cited ideal-quotient Tor criterion has exactly the required converse; verdict sound.
- New node lem-pc-module-opcycles-tor-surjection: checked the Tor quotient argument, edge cases a=0, zero complex, field, and I=0 or A; verdict mathematically sound after adding the one-point-site, flatness, cohomology, and Tor definition dependencies.
- Existing node lem-weil-pbc-flat-tor-ideal-criterion: checked its statement and citation quote verbatim; no change.

Changes made: repaired both new statements and the two affected citation quotes to be self-contained and dimensionally consistent; added the missing definition dependencies. The source TeX remains unavailable in this checkout and is retained as WANTED.
