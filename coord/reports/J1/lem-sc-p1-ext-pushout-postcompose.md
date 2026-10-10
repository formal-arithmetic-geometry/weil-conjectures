Files written:

- `dag/nodes/sec-picard-framework/lem-sc-p1-ext-pushout-postcompose.json` — statement, two proof steps, and split metadata.
- `dag/nodes/sec-picard-framework/lem-sc-p1-ext-class-naturality.json` — statement-only Mathlib leaf for Ext-class naturality.
- `citations.json` — verbatim support for every proof-step citation.

Attachments: none.

WANTED: none.

The item statement was retained. I searched the whole DAG and blueprint for an existing pushout/Ext-class naturality statement; the existing `lem-weil-pbc-pushout-short-exact-sequence` supplies pushout exactness and the morphism of short exact sequences, while no existing node states the Ext-class naturality equation. The new node records the exact Mathlib declaration `CategoryTheory.ShortComplex.ShortExact.extClass_naturality`.

## Review by J1

I read the item source at Homology Tag 010I and its Derived Tag 06XP reference, and read the complete statement of `lem-weil-pbc-pushout-short-exact-sequence`. Step 1 uses exactly that node's assertion that the pushout produces a short exact sequence and that the canonical maps form a morphism with third component `id_C`; the hypotheses match because sheaves of modules on a ringed space form the abelian category used for Ext. Step 2 uses exactly the new Mathlib leaf statement: a morphism of short exact sequences transports the extension class by the end maps. Substituting first map `phi` and third map `id_C` gives the claimed postcomposition formula, and the final rearrangement is elementary. The off-unit pushout node is declared as a generic tool use because this unit has no separate pushout-exactness route.

I checked the edge cases `phi = id` (the pushout sequence is the original sequence and the class is `delta`), `phi = 0` (the pushout is split and its class is zero), and a split original sequence (both sides are zero). I also inspected Mathlib source line 131 directly and ran LeanFinder, Loogle, and Mathlib grep searches for the new leaf; the exact-name Loogle search found the declaration, and the source line agrees with the node statement.

What I could not finish: no Lean proof was written, as required for stage 1.
