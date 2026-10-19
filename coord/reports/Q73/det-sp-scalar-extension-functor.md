# Stage-1 worker report: det-sp-scalar-extension-functor

## Files written

- `det-sp-scalar-extension-functor.json`: retained the imported statement and route, marked split, and replaced the two returned long steps with short cited steps.
- `lem-sp-stratum-scalar-extension.json`: new statement-only child; no Mathlib match.
- `lem-sp-invertible-tensor-scalar-extension.json`: new statement-only child; no Mathlib match.
- `citations.json`: 31 step/node pairs with verbatim statements.

## Attachments

None. The permitted `WeilConjectures/` source search found no declaration tagged `(blueprint: det-sp-scalar-extension-functor)` and no declaration stating the cross-ring derived functor with its constructibility, Tor interval, Tate-line and coherence clauses. The fixed-coefficient tensor code and the Adic documentation do not construct this ordinary constant-ring scalar extension.

## WANTED

None. Both new child statements use the existing blueprint proof and existing DAG interfaces; no external source is needed for the stage-1 split.

## Faults found and corrected

The returned-delivery instruction identified that the old step 4 (3180 characters) and step 7 (2061 characters) hid non-elementary lemmas. I added `lem-sp-stratum-scalar-extension` for the constant-module inverse-image comparison, exact restricted cohomology, K-flat pullback and termwise tensor comparison used on each refined stratum. I added `lem-sp-invertible-tensor-scalar-extension` for the generic tensor-power and dual comparisons for a locally free rank-one module. The item now cites these children and both steps are under 2000 characters. The item statement and all other steps remain unchanged.

The earlier imported statement corrections remain recorded in the item: the Tate example requires `ell` invertible on `T` (otherwise on `Spec(F_ell)` the root sheaf is zero), and the unit comparison requires the identity map `g=id_B`, rather than merely equal endpoint rings (the Frobenius endomorphism of `F_4` is a counterexample). No hypothesis was added to the general functor, constructibility, line or associativity clauses.

## Not duplicates

- `lem-sp-stratum-scalar-extension` vs `lem-kun-inverse-image-monoidal`: the existing node is an étale derived-tensor comparison; the new node states the finite constant-module comparison on small pro-etale strata together with exact cohomology and K-flat scalar-extension pullback.
- `lem-sp-stratum-scalar-extension` vs `lem-weil-pbc-left-exact-site-inverse-image-tensor`: the existing node gives abstract finite-limit/colimit preservation for a site functor; the new node packages its application to constant module sheaves, coefficient-ring identification, and the ringed tensor comparison needed here.
- `lem-sp-invertible-tensor-scalar-extension` vs `det-def-sp-tate-twist-locally-free`: the existing node constructs and proves invertibility of Tate lines; the new node is the generic sheaf-level scalar-extension comparison for powers and duals of any rank-one module.
- `lem-sp-invertible-tensor-scalar-extension` vs `lem-pur-sheaf-tensor-product`: the existing node defines sheaf tensor products and powers; the new node states their canonical change-of-rings isomorphisms and coherence, including sheaf Hom duals.

## Review by Q73

I read `coord/brief-stage1.md`, stages/1-dag.md, the current item, its chapter and unit records, the main-20261015 blueprint statement and proof, the Q73 return entry, and delivery-errors sections B--E. The current shared item has no finished declaration in either permitted source checkout; its `lean_audit` is `none`.

For the new stratum child I checked the statements of `def-weil-proetale-inverse-image`, `def-weil-pbc-constant-sheaf`, `def-weil-pbc-sheafification`, `lem-weil-pbc-left-exact-site-inverse-image-tensor`, `prop-weil-pbc-proetale-constant-ring-map`, `prop-weil-pbc-proetale-constant-exact`, `lem-weil-pbc-ringed-topos-kflat-pullback`, and `lem-weil-pbc-ringed-topoi-module-pullback-tensor`. They provide exactly the constant-set coproduct argument, preservation of module operations, coefficient identification, exact cohomology pullback, K-flat pullback, and tensor comparison used in the child statement. Its `blueprint.from` points to paragraph (2) of the item proof.

For the invertible-module child I read `def-pur-sheaf-tensor-product`, `def-pur-sheaf-hom`, and the finite-coefficient clauses of `det-def-sp-tate-twist-locally-free`. The child abstracts only the ordinary tensor-power and evaluation-map argument; the Tate root comparison and exponent independence remain in item step 7. Its `blueprint.from` points to paragraph (3) of the item proof.

Step 4 now uses the existing stratification-intersection node, the new stratum child, and `lem-weil-pbc-locally-constant-tensor`. I checked the hypotheses: the finite ring `A` is Noetherian, `B` is finite as an `A`-module, both tensor factors are bounded above, and the refined stratum restrictions have finite locally constant cohomology. Step 5 still supplies the finite `B`-action table and local equality argument, so the new child does not silently claim `B`-constructibility. Step 7 uses the explicit root map at a common exponent and then the new generic tensor/dual child for positive, zero, and negative twists; invertibility from the Tate node makes ordinary and derived tensor agree.

I tested the repaired statements on the zero complex, empty scheme, zero coefficient ring, a rank-one line in degree zero, interval `[a,a]`, nonflat `Z/ell^2 -> F_ell`, twists `0,1,-1`, and identity versus Frobenius maps on `F_4`. I searched for duplicate DAG and blueprint statements by the new node names and concepts. For each new node I ran and read LeanFinder, Loogle, grep, and LeanSearch through `msearch.py`; the logs are in `searches.jsonl`. The hits are generic module or sheaf APIs and do not state either new sheaf-level result. `citations.json` quotes the current cited statements verbatim, and `proof_deps` is the union of all step uses. No SGA source, Lean edit, compiler, Lake, or global build was used.

The resumed dry run rejected both child statements for missing inline node citations. I repaired their statements by citing the actual definitions of module sheaves, inverse image, constant sheaves, local constancy, K-flatness, flatness, tensor products and cohomology. I removed from the stratum child's statement dependencies the theorem nodes that are material for its eventual proof rather than notions used to state it. Its mathematical assertions are unchanged. I also replaced approximate Mathlib hit summaries with the exact top-hit lists retained in searches.jsonl; the queries and no-match verdicts are unchanged. I refreshed the two child quotes in citations.json.

I compared the sandbox item with the current shared item: only proof, proof_deps, split_report and status differ. The item statement, the accepted statement corrections, blueprint metadata, unit binding, tool_uses and maintainer review are retained. I read the dedicated Q73 return: its two numbered long arguments are precisely the arguments now isolated, and every current proof step is below 2000 characters.

For completeness, my step-by-step citation check is as follows. Step 1 takes the exact target-ring-valued exact functor and quasi-isomorphism invariance from lem-pur-derived-change-of-rings, and a flat-term K-flat representative from lem-pc-kflat-resolution (Stacks 06YY and 06YS). Step 2 takes K-flatness after change of rings from lem-pur-kflat-change-of-rings (0G7E); its balanced formulas, inverse and differential compatibility follow directly from the cited tensor and restriction definitions. Step 3 applies the definition of Tor amplitude to the underlying restricted B-module, and uses the tensor unitor; it needs no flatness of B over A. Step 4 takes the common refinement from the intersection statement, the exact stratum comparisons from the new child, and finite locally constant tensor cohomology from lem-weil-pbc-locally-constant-tensor (094H). Its small-site and bounded-above hypotheses hold on each stratum, with A finite hence Noetherian. Step 5 uses precisely the local representation and local equality clauses of lem-weil-pbc-site-sheafification-sections-local (00WK), rather than deriving them from the definition of sheafification; the finite coefficient action table supplies B-linearity. Step 6 takes bounded-flat K-flatness from lem-weil-pbc-independent-bounded-flat-kflat (06YQ); flatness of the line is checked on its trivializing cover. Step 7 uses the finite-ring clauses of the Tate-line node, its exponent transition maps and the new generic tensor/dual comparison; it assumes ell invertible exactly here. Step 8 uses K-flat change of rings, computation of the exact derived functor and the localization equivalence explicitly stated by lem-weil-pbc-site-derived-tensor-descent; the displayed chain comparison is compatible with both arrows of a roof. Step 9 checks unit and pentagon on pure tensors and uses that equivalence to descend equality. All these cited statements were opened and read, and every step/node quote is an actual substring of its current statement.

## Statement disputes retained from the accepted item

STATEMENT-DISPUTED: The blueprint's unrestricted Tate example fails in characteristic ell, and its identity assertion for equal endpoint rings fails for a nonidentity ring endomorphism. The current shared item already repairs them by requiring ell invertible for the Tate example and g=id_B for the unitor assertion. This repair delivery keeps those statements unchanged. The explicit counterexamples are T=Spec(F_ell), where the pro-etale ell-th roots-of-unity sheaf is zero, and the nonidentity Frobenius on F_4. The accepted unit-route issue and arbitrary non-Noetherian scheme counterexample remain fully recorded in split_report.unit_route_error; no unit file is delivered.

## Resumed review and validation

The first resumed dry run passed server preflight at 7ac9f4cff5 (not pushed). I then found three literal tab characters where the shortened steps intended TeX `\to`, and corrected them in steps 4 and 7. I restored the original step-4 finite-model justification and its citation to `lem-weil-proetale-constant-sheaf-stalk`: a local constant module value on a nonempty member equals its geometric stalk and is finite by input constructibility; pullback of its trivializing cover retains the finite model on the refined stratum. The new stratum lemma supplies the constant-module comparison. This avoids treating finite stalks as a definition of finite-type local presentations without justification. I added the corresponding verbatim citation. All changes remain confined to the sandbox.
