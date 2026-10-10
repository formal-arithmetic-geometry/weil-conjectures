# Stage 1 report

1. **Files written.** Repaired item `dag/nodes/sec-abelian-varieties/lem-sc-intersection-effective-cartier.json`, added statement-only node `lem-sc-effective-cartier-dimension-drop` (unsplit, no Mathlib match), and retained `citations.json`.

2. **Attachments.** None. No sorry-free declaration in `WeilConjectures/` states Tag 0BEU exactly.

3. **WANTED:** None.

4. **Not duplicates.** `lem-sc-effective-cartier-dimension-drop` vs existing dimension nodes: the search `rg -n 'integral.*Cartier|Cartier.*integral|dimension.*d-1|dimension.*one less' dag/nodes` found no node stating the global dimension-drop conclusion; the existing local-ring quotient nodes concern Cohen--Macaulay local algebra and do not state an effective Cartier divisor on an integral finite-type scheme has dimension `d-1`. Existing `lem-sc-snapper-numerical-polynomial` is cited for the polynomial degree bound, and `lem-weil-pbc-closed-immersion-proper` is cited for properness; neither restates the item.

5. **Repair.** The returned statement omitted conditions needed by `def-sc-intersection-number`: the repair now assumes `d >= 1`, that `D` is nonempty, and that `dim D = d - 1`. Step 1 cites `lem-weil-pbc-closed-immersion-proper` for the conclusion that the closed subscheme `D` is proper. Step 2 explicitly uses the supplied dimension equality to bound the quotient polynomial by degree `d - 1`. The new node `lem-sc-effective-cartier-dimension-drop` records the dimension theorem invoked in the Tag 0BEV proof as a standalone statement for the consumer to cite. The consumer `lem-sc-positive-ample-hilbert-degree` must cite that node for `dim D=g-1`; it must cite `lem-pc-very-ample-ample` and `def-sc-ample` (as already used in its step 2) for ampleness of the restricted module. Its intersection step can then cite this item for the equality after discharging these hypotheses.

## Review by G1

For the new node I read the dimension assertion in the Tag 0BEV proof (which invokes Divisors and dimension theory after constructing the zero scheme), rather than attributing it to Tag 0BEU. Integrality and finite type over a field, nonempty effective Cartier divisor, and positive dimension give dimension one less. I searched the whole DAG and blueprint before creating it; no existing node states this global conclusion. The required LeanFinder, Loogle, grep, and LeanSearch queries were run and recorded in the node; only local Krull-dimension quotient lemmas appeared, so this remains an unsplit statement-only Stacks node. I tested the edge cases conceptually: a principal divisor on an integral curve is zero-dimensional, while the empty divisor is excluded because its dimension is not `d-1`.

I reread Stacks Project `varieties.tex`, Tag 0BEU (`lemma-numerical-intersection-effective-Cartier-divisor`) and its exact sequence and Euler-characteristic difference proof. I checked the repaired hypotheses against `def-sc-intersection-number`: `d >= 1` ensures the list of modules is meaningful, while nonempty `D` and `dim D=d-1` make the right-hand intersection number defined. I checked the statement of `lem-weil-pbc-closed-immersion-proper`; it explicitly says that a closed subscheme of a proper scheme is proper, which is exactly the fact used in step 1. I reread `lemma-nagata-effective-cartier-is-invertible`, `def-weil-closed-immersion`, `def-sbc-closed-immersion-ideal-sheaf`, and `lem-pc-divisor-line-bundle-invertible`; their statements provide the invertible ideal, closed-subscheme ideal, and dual identification used in the exact sequence argument. For step 2 I reread `lem-pc-euler-additive`, `lem-sc-snapper-numerical-polynomial`, and `def-sc-intersection-number`; the quoted Snapper statement gives total degree at most `dim Supp(F)`, and the repaired hypothesis `dim D=d-1` supplies the required bound. `citations.json` now contains verbatim quotes for every cited node in both steps. I tested the edge cases that motivated the return: `D` empty is excluded, `d=0` is excluded, and a disconnected proper scheme with a divisor on a lower-dimensional component is excluded by the explicit equality `dim D=d-1`. I also recorded the consumer handoff: properness/dimension and ampleness of the specific divisor remain obligations of the consumer's preceding steps.

## Not duplicates

- `lem-sc-effective-cartier-dimension-drop` vs `lem-sc-top-dimensional-reduction-intersection`: the new node proves the dimension of one nonempty effective Cartier divisor on an integral finite-type scheme; the existing node gives a weighted intersection-number decomposition over all top-dimensional irreducible components and does not state a divisor dimension result.
- `lem-sc-effective-cartier-dimension-drop` vs `lem-sc-proper-affine-finite-general`: the new node is a codimension-one dimension theorem; the existing Mathlib leaf states that a proper affine morphism to a field is finite.
- `lem-sc-effective-cartier-dimension-drop` vs `lem-sc-isogeny-facts`: the new node concerns effective Cartier divisors and scheme dimension; the existing node concerns multiplication isogenies of abelian varieties and only cites Tag 0BEV for a separate positivity fact.

## Second reading by G1

- Item statement: checked against Stacks `varieties.tex`, Tag 0BEU, hypothesis by hypothesis; the added assumptions `d >= 1`, nonempty `D`, and `dim D = d-1` make both intersection numbers defined.
- Step 1: checked the exact sequence and ideal/dual identifications against Tags 0BEU and the cited node statements; properness follows from the cited closed-immersion properness node.
- Step 2: checked Euler-characteristic additivity and the Snapper degree bound; explicitly verified `Supp(O_D)=D` and `dim D=d-1`, so the quotient polynomial has degree at most `d-1`.
- New node `lem-sc-effective-cartier-dimension-drop`: checked against the Tag 0BEV dimension argument and its hypotheses; retained as a standalone statement-only node because no existing DAG or Mathlib declaration supplies the scheme-level result.
- Edge cases checked: `d=0`, empty `D`, and `dim D != d-1` are excluded; the field and properness hypotheses agree with Tag 0BEU's setting.
- Changed the second proof step to state the support-dimension argument explicitly, repairing C1/E; documented that the consumer must separately establish divisor dimension and restricted ampleness, since Tag 0BEU supplies neither conclusion.
