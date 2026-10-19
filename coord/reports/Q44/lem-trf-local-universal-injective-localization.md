# Worker report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-local-universal-injective-localization.json`: item split into three proof steps; no new nodes; existing Mathlib leaf `lem-weil-pbc-localization-tensor-over-base` is cited.
- `citations.json`: verbatim statement excerpts for every cited node in Steps 2 and 3.

Attachments: none. No sorry-free project declaration states this item exactly in the searched Lean source.

WANTED: none.

The imported statement agrees with Stacks Algebra Tag 05CM(1), after taking the base-ring multiplicative subset to be `{1}` and the target-ring subset to be the given `T`. I found no statement error, missing hypothesis, or route departure. No new node was necessary: localization preserving injectivity is the two-line fraction-kernel argument from the localization definition, while tensor-localization compatibility is already the Mathlib leaf `lem-weil-pbc-localization-tensor-over-base`.

Nothing remains unfinished.

## Review by Q44

I read the item, its chapter `sec-trace-formula`, its unit `sk-i-curve-zero`, and the parent node `lem-trf-local-generic-basis-universal-injective` that uses this item. I searched both read-only Lean source trees for the blueprint tag and the localization/universal-injectivity names; no finished declaration covers the item. I read the full statement and direct proof of Stacks Tag 05CM, including the displayed argument that localization is exact and that localization commutes with tensoring. I also read the Tag 00DK tensor-localization statement and Tag 00D2 tensor-with-bimodule statement, and the complete statement of the existing node `lem-weil-pbc-localization-tensor-over-base`.

Step 1 fixes an arbitrary `R`-module `L`, obtains injectivity of `v = 1_L ⊗ u` directly from the hypothesis, and checks the induced `S`-module structures and `S`-linearity. Step 2 applies the existing tensor-localization statement with `A = S`, `M` equal to each of `M` and `M'`, and `N = L`; its fraction formula, followed by tensor symmetry, gives the two comparison isomorphisms. I checked the displayed pure-fraction calculation, which proves the square commutes and uses exactly the cited statement. Step 3 checks injectivity by the localization equality criterion: `v(x)/t = 0` gives an `s ∈ T` with `s v(x)=0`, hence `s x=0` and `x/t=0`; the comparison isomorphisms then transfer injectivity to `L ⊗_R T^{-1}u`, and arbitrariness of `L` gives universal injectivity.

I tested the edge cases `T = {1}`, `0 ∈ T` (both localizations are zero), zero modules, and `u = id`; each behaves as the statement predicts. The statement and dependencies needed no correction, and no new node or duplicate was introduced.
