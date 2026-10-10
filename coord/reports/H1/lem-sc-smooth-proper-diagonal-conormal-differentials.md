Files written:

- `dag/nodes/sec-picard-framework/lem-sc-smooth-proper-diagonal-conormal-differentials.json` (statement, split)
- `citations.json`

Attachments: none.

WANTED: none.

The item had no Lean declaration in `weil-src-slopmaster2`. I checked the imported statement against Stacks Tag 08S2 and retained its generality: no smoothness or properness hypothesis is needed for this identity. Step 1 writes the affine ring calculation directly from the Kähler differential quotient and the diagonal multiplication map, then uses the two existing Kähler-differential definition nodes. Step 2 is the elementary sheaf gluing/isomorphism-on-an-affine-basis argument; its functoriality follows from the canonical quotient and universal derivation, so it cites no hidden theorem. I checked the zero-ring and polynomial-ring cases: the kernel quotient and differentials both vanish for the zero algebra, while for R[x] the generator 1⊗x-x⊗1 maps to dx.

## Review by H1

I read `literature/stacks-project/morphisms.tex`, Tag 08S2, and the source statements of every cited node. The affine step's hypotheses are exactly a commutative base ring, an R-algebra, and the multiplication kernel; the cited affine node states the quotient and the generator-to-differential map verbatim. The existing Kähler nodes supply the universal derivation and affine sheaf description, exactly what the step takes from them. The second step only uses restriction compatibility and the sheaf criterion that an affine-local isomorphism glues, so it is marked elementary. I verified that the new node is not a duplicate by searching its kernel/I² and 08S2 keywords across `dag/nodes` and the blueprint. No statement or source error was found.

What could not be finished: no Lean compilation is permitted at stage 1; the required delivery dry run is the remaining verification.

## Second reading by H1

- Item statement: checked against Stacks `morphisms.tex`, Lemma `lemma-differentials-diagonal`, Tag 08S2; the theorem is for every morphism, and the repaired statement now handles the diagonal as an immersion and defines relative differentials on affine opens.
- Step 1: checked against the affine portion of Tag 08S2 and the statement of `lem-weil-pbc-affine-conormal-sections`; the `I/I^2` identification is cited, the Kähler universal derivation is cited, and the remaining generator calculation is written explicitly and marked non-elementary.
- Step 2: checked against the sheaf-gluing portion of Tag 08S2; restriction functoriality and the affine-basis isomorphism criterion are the only elementary ingredients, so no uncited substantive theorem is used.
- New nodes: no new node is created; the edited item is the existing unsplit item. Its statement, definitions, source tag, and affine hypotheses were checked against 08S2. The Mathlib searches were rerun and recorded; the scheme-level theorem has no Mathlib leaf.
- Small cases: for the zero ring both conormal and differential modules vanish; for a field over itself both vanish; for `R[x]` over `R`, the class of `1\\otimes x-x\\otimes1` maps to `dx`; the empty scheme is vacuous.

Changes made:

- Repaired the statement's false global closed-immersion assumption by defining the conormal sheaf locally for the diagonal immersion, as in Tag 08S2.
- Replaced the curve-only `def-sc-kahler-differentials` reference with the affine relative Kähler differential definition.
- Added the existing affine-conormal node and the Kähler definition to step 1 and `proof_deps`; updated `citations.json` with verbatim statement quotes.
- Corrected the split summary to remove the incorrect Mathlib-leaf claim and recorded the affine-conormal node as a tool use.
