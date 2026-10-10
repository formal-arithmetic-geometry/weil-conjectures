Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-boundary-cech-compatibility.json`: repaired statement node and proof.
- `dag/nodes/sec-curve-estimates/lem-sc-boundary-cech-injective-middle.json`: statement-only injective-middle comparison node; Mathlib searches found no match.
- `citations.json`: verbatim citations for every step.

Attachments: none.

WANTED: none. The Stacks source was read at the passages for 01EQ, 01EP, and 0B8S.

The returned proof incorrectly treated the Cech complex as a resolution and used naturality of c_H as if it were naturality of connecting maps. I replaced it with the injective reduction requested by the return. The new node isolates the strictly smaller case with injective middle term, based on the double-complex comparison of 01EQ and the injective Cech acyclicity of 01EP. The source tags now distinguish 0B8S (boundary derivation/local lifts), 01EQ (Cech-to-derived comparison), and 01EP (injective Cech acyclicity); no citation to `lem-sc-boundary-cech-local-lifts` remains, avoiding a cycle.

## Review by H1

I read the actual Stacks passages for 01EQ and 01EP and the local-lift paragraph of 0B8S. Step 1 uses the exact statement of `lem-weil-pbc-scheme-modules-enough-injectives` for the monomorphism into an injective and the exact naturality clause in `lem-weil-pbc-right-derived-universal-delta-functor` for the morphism of short exact sequences; the induced quotient map and diagram are the standard abelian-category construction. Step 2 checks directly that applying the extension map to each local lift preserves the same difference cocycle, with the restriction maps from `def-weil-pbc-site-cech-complex`; it does not claim that the Cech complex resolves B. Step 3 uses the new injective-middle statement, whose statement is exactly the injective case of 01EQ/01EP, and then reuses derived-boundary naturality from Step 1. The Cech differential quote fixes the sign: the differential is `d^0(t)_{i_0 i_1}=t_{i_1}-t_{i_0}`, while 0B8S names the boundary cocycle `f_{i_0}-f_{i_1}`; the 01EQ comparison conventions give the positive connecting class as stated. I checked the one-open-cover and zero-kernel cases, and verified every `citations.json` quote is a verbatim substring of its cited node statement. The two off-unit theorem citations are declared in `tool_uses` because they are generic categorical tools not supplied by this unit's route.
