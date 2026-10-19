# lem-trf-faithfully-flat-universal-injective-reflection — Q79

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-faithfully-flat-universal-injective-reflection.json`: item retained with its statement and hypotheses, now split into three proof steps; no direct Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-scalar-tensor-cancel-base-change.json`: new Mathlib leaf, exact `TensorProduct.AlgebraTensorModule.cancelBaseChange` (Tower.lean:436; pure-tensor formula at :448).
- `dag/nodes/sec-trace-formula/lem-trf-scalar-tensor-distrib-base-change.json`: new Mathlib leaf, exact `TensorProduct.AlgebraTensorModule.distribBaseChange` (Tower.lean:441; pure-tensor formula at :463).
- `dag/nodes/sec-trace-formula/lem-trf-faithfully-flat-ltensor-injective-reflection.json`: new Mathlib leaf, exact `Module.FaithfullyFlat.lTensor_injective_iff_injective` (Basic.lean:385).
- `citations.json`: verbatim quotations for every node cited by every item step.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` for the item id, its blueprint tag, and faithful-flat/universal-injectivity terminology; no sorry-free project declaration states this item.

## WANTED

None. The cited Stacks source and Mathlib files are present locally.

## What was wrong and what was repaired

The imported item was unsplit and had no proof. I retained its exact statement and dependencies. The proof now makes both directions explicit: forward cancellation identifies `T tensor_S (S tensor_R u)` with `T tensor_R u`; reverse scalar extension to `S tensor_R L`, distributivity identifies the resulting map with `S tensor_R (L tensor_R u)`, and faithful flatness reflects injectivity. No finiteness, flatness of `P` or `Q`, or extra hypothesis is introduced. The item is not a restatement of any new leaf.

## Not duplicates

- `lem-trf-faithfully-flat-ltensor-injective-reflection` vs `lem-weil-pbc-faithfully-flat-universally-injective`: the existing node only states injectivity of the canonical map `N → N tensor_R S`; the new leaf reflects injectivity of an arbitrary linear map after left tensoring.
- `lem-trf-faithfully-flat-ltensor-injective-reflection` vs `lem-trf-flatness-faithfully-flat-extension`: the existing node concerns detection of flatness over an intermediate ring; the new leaf concerns injectivity of one arbitrary linear map.
- `lem-trf-scalar-tensor-cancel-base-change` vs `lem-weil-pbc-module-tensor-comm`: the existing node swaps two tensor factors over one ring; the new leaf cancels scalar extension across an algebra map and changes the base ring of the inner tensor.
- `lem-trf-scalar-tensor-distrib-base-change` vs `lem-weil-pbc-module-base-change-across-pushout`: the existing node is a pushout-specific module isomorphism with extra ring and map data; the new leaf is the general scalar-extension distributivity equivalence for two modules.

## Review by Q79

I read the item, chapter `sec-trace-formula`, unit `sk-i-curve-zero`, and the inherited blueprint ancestry. I also read Stacks `algebra.tex`, Tag 05A5 (the final faithfully-flat reflection sentence) and Tag 05CK, and inspected the Mathlib declarations and source lines recorded in all three leaves. The item statement uses the faithful-flat ring-map and module-tensor definitions exactly as their nodes state them.

Step 1 assumes universal injectivity over `R`, fixes an arbitrary `S`-module `T`, and restricts scalars along `R → S`. The cancellation leaf supplies exactly the `S`-linear isomorphism `T tensor_S (S tensor_R N) ≃ T tensor_R N` and its pure-tensor formula. Checking the induced map on pure tensors gives the required conjugacy, so injectivity transfers for every `T`.

Step 2 fixes an arbitrary `R`-module `L` under the converse hypothesis. Universal injectivity over `S` applies to the `S`-module `S tensor_R L`. The distributivity leaf supplies exactly the isomorphism between `S tensor_R (L tensor_R P)` and `(S tensor_R L) tensor_S (S tensor_R P)`; the formula shows it intertwines the map induced by `u`. The faithful-flat `lTensor` leaf states the precise iff reflecting injectivity of `L tensor_R u`, and the faithful-flat ring-map definition supplies the required faithfully flat `R`-module `S`. Step 3 is just the conjunction of the two implications and checks the tensor convention.

I checked edge cases such as `u = 0`, identity maps, zero modules, and `R = S` with the identity algebra: both sides reduce to the ordinary universal-injectivity condition, and the cancellation/distributivity maps reduce to the usual tensor unit identifications. All three new leaves were searched with LeanSearch, LeanFinder, Loogle, and Mathlib grep; every recorded query is present in the actual Q79 search log. No SGA source is used, no definition is hollow, proof dependencies equal the union of step uses, and all citation quotes are literal substrings of the cited statements.

## What could not be finished

Nothing. The split, citations, report, and self-review are complete; the server dry run and delivery remain.
- `lem-trf-faithfully-flat-ltensor-injective-reflection` vs `lem-trf-faithfully-flat-universal-injective-reflection`: the new Mathlib leaf is the ordinary injectivity reflection theorem for one fixed map after left tensoring; the item quantifies over all further module tensorings and compares universal injectivity over two rings.
- `lem-trf-faithfully-flat-ltensor-injective-reflection` vs `lem-trf-mittag-leffler-faithfully-flat-descent`: the new leaf is an exact Mathlib theorem about injectivity of one linear map; the existing item is the larger Mittag–Leffler descent statement whose proof uses faithful-flat universal-injectivity reflection.
- `lem-trf-scalar-tensor-cancel-base-change` vs `lem-trf-faithfully-flat-universal-injective-reflection`: the new leaf is a tensor-associativity/cancellation isomorphism for arbitrary modules; the item is an iff about universal injectivity and contains no standalone tensor isomorphism conclusion.
- `lem-trf-scalar-tensor-cancel-base-change` vs `lem-trf-mittag-leffler-faithfully-flat-descent`: the new leaf is the general scalar-cancellation equivalence; the existing statement is descent of the Mittag–Leffler property and does not assert this equivalence.
- `lem-trf-scalar-tensor-distrib-base-change` vs `lem-trf-faithfully-flat-universal-injective-reflection`: the new leaf is scalar-extension distributivity over a tensor product; the item concludes equivalence of universal injectivity and does not state distributivity as its result.
- `lem-trf-scalar-tensor-distrib-base-change` vs `lem-trf-mittag-leffler-faithfully-flat-descent`: the new leaf is a general Mathlib tensor equivalence; the existing statement is a faithful-flat descent theorem for Mittag–Leffler modules and has different objects and conclusion.
