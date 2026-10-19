# Worker report: lem-per-regular-strict-local-model

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-regular-strict-local-model.json`: item split into ten proof steps.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-smooth-colimit-regular.json`: statement-only Stacks Tag 07EP node; Mathlib searches found no exact declaration.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-flat-tensor-scalar-comparison.json`: Mathlib leaf `RingHom.Flat.mapOfCompatibleSMul`, `Mathlib/RingTheory/RingHom/Flat.lean:250–256`.
- `citations.json`: verbatim statement quotes for every node used by every item step.

## Attachments

No Lean declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` has the item tag or states this item exactly. No attachment was made.

## WANTED:

None. The ILO XVII PDF, Stacks sources, and the Greco excellence result used here were read from the available literature or existing DAG nodes. The Greco paper is already recorded in the cited existing node; no new source file is needed.

## Not duplicates

- `lem-per-smooth-colimit-regular` vs `lem-weil-pbc-popescu-smoothing`: the new node proves regularity of a filtered colimit of smooth algebras from Noetherian fibres; the existing node constructs a smooth filtered presentation of a given regular map and does not state the converse regularity criterion.
- `lem-per-smooth-colimit-regular` vs `lem-weil-pbc-regular-composition`: the new node is the smooth-colimit criterion; the existing node is composition of two regular maps under a Noetherian composite-fibre condition.
- `lem-per-flat-tensor-scalar-comparison` vs `lem-weil-pbc-flat-module-base-change`: the new node is flatness of `T ⊗_R U → T ⊗_S U` from flat multiplication; the existing node only says tensoring a flat module along a base change remains flat.
- `lem-per-flat-tensor-scalar-comparison` vs `lem-exc-weakly-etale-ring-base-change-composition`: the new node is the specific tensor comparison map and its flatness; the existing node gives weak-etale stability under arbitrary base change and composition, including a stronger property with different hypotheses and conclusion.

## What was wrong or corrected

The retained item had no proof and its blueprint `from.place` was already populated but did not identify the algebraic local-model argument. I preserved the statement and all original statement dependencies, added the definitions used explicitly by the closed-fibre clause, filled the blueprint place and `same_as`, and recorded the exact source route. The saved previous worker searches were reused; only the changed search questions for the new two nodes and the item’s strict-local theorem question were rerun. No source statement was weakened.

The item is stronger than the two local lemmas printed in ILO XVII 4.3.2.3–4: I therefore wrote the regularity, excellence, fibre-dimension and closed-base-change arguments explicitly, rather than treating the ILO reduction sentence as a complete proof. The strict-local fibre decomposition uses the existing 0AH1 node, and the regularity of the ind-etale strict-local extension uses the existing Greco excellence node. The flatness comparison in Step 4 is exactly the Mathlib declaration recorded for the new leaf. The finite-product argument in Step 6 is elementary from the displayed idempotents and the definition of regularity; no hidden node is used.

## Review by Q43

I read the item source in Illusie–Laszlo–Orgogozo, Exposé XVII, the opening reduction of Lemma 4.3.2.1 and Lemmas 4.3.2.3–4.3.2.4, then checked the algebraic ingredients against Stacks Tags 06LJ, 07C0, 07C1, 07EP, 0AH1, 07QH, 00ON and 0HA1. Step 1 cites strict-henselization triples and functoriality for the actual local rings and map, finite-type localization for excellence, and strict-henselization Noetherianity; I checked that no finite-type hypothesis on `h` was silently introduced. Step 2 cites the filtered-etale presentation, weak-etale stability, and the existing Greco excellence-ascent theorem; its target-Noetherian hypotheses are supplied by Step 1. Step 3 uses the local criterion for regular maps, etale implies smooth, Noetherian fibre rings, the new 07EP statement, and regular composition; each cited statement supplies exactly the property used. Step 4 checks flat base change, the new Mathlib `mapOfCompatibleSMul` statement, and flat composition, with the tensor comparison map and its inverse written explicitly. Steps 5–6 read the finite separable fibre decomposition from 0AH1, check the tensor cancellation isomorphism, and prove the finite-product/idempotent decomposition and geometric-regularity transfer; the separable-algebraic field extension hypothesis is exactly the one required by 07QH. Steps 7–8 apply the existing flat height formula to both local maps, verify the fibre local rings are fields, and use the scheme-fibre stalk quotient node; the base dimensions are finite by the Noetherian parameter node. Step 9 replaces strict localizations by ordinary localizations and checks localization transitivity. Step 10 identifies a closed subscheme with `Spec(A/I)`, computes the fibre as `Spec(B/IB)`, applies finite-type regular base change, and checks excellence of both quotient rings.

I tested the new statements on the identity map, a smooth polynomial algebra, a finite separable field extension, an empty closed subscheme (`I=A`), and zero-dimensional strict-local fibres. These cases expose no missing nonemptiness or finiteness hypothesis. I searched the whole DAG and blueprint for 07EP, tensor-comparison, strict-henselization regularity, and the cited tags; the “Not duplicates” section records the only nearby statements and why they differ. Every proof step has a source, every non-elementary assertion has a cited node, and `citations.json` quotes the exact statement text used. No Lean source was written or compiled, and no SGA source was cited.
