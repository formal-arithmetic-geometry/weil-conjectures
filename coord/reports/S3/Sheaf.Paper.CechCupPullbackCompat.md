## What changed

Completed the two remaining proofs in `lean/Sheaf/Paper/CechCupPullbackCompat.lean`:
`moduleCup_coefficient_naturality` and `moduleCup_pullback_naturality`.
Added the proof-only imports `Sheaf.Paper.ModuleCupCoefficientResolutionMaps` and
`Sheaf.Paper.ModuleCupPullbackResolutionMaps`. Both imports pass `import_direction.py may`.
The existing theorem statements, universes, definitions, visibility, and public imports
are preserved; no other module is adapted.

Both arguments use the existing simultaneous computing-resolution maps. Surjectivity
of the resolution class map lifts the two input classes to global kernel cocycles.
Leibniz constructs their product cocycle. For coefficient maps, the existing local
`map_cycle` transports all three cycles. For pullback, the new private
`map_additive_cycle` constructs their images across scalar rings directly from the
cochain commutation equation. The three class equations identify their cohomology
images; the pairing equation identifies the mapped product section. Applying the
source and target `IsModuleCupProduct` characterizations proves each naturality.

The private surjectivity and product-cocycle arguments use the same Mathlib APIs as
`ModuleCohomologyCupProduct`. Scoped heartbeat settings cover the resolution class
identifications and the three class transports; the single-file time limit is unchanged.
Updated Step 4, `proof_deps`, and `proof_origin` of
`dag/nodes/sec-abelian-varieties/lem-sc-picard-cech-cup-pullback-compat.json` to record
these actual dependencies and remove the stale assertion that sheaf naturality is
unproved. The unit `sk-prop-av-cube` and its route are preserved.

## Proved and sorry left

Closed both original holes, belonging to node
`lem-sc-picard-cech-cup-pullback-compat`:

- `AlgebraicGeometry.Scheme.Modules.moduleCup_coefficient_naturality`.
- `AlgebraicGeometry.Scheme.Modules.moduleCup_pullback_naturality`.

No `sorry` remains in the delivered module. No new hole, public declaration, module,
or DAG node is added. All new private helpers are complete. The five previously
proved public theorems remain proved. This is two holes closed and zero holes added,
using existing library dependencies; it is not a decomposition into new holes.
Existing dependencies may still rely on unfinished lower proofs, as intended by stage 3.

## No longer needed

None. Every original import is still used by the previously completed comparison,
coefficient, or refinement-composition arguments or by the module's signatures.
The two added proof imports are used respectively by the two new naturality proofs.
No dependency node or module from the existing route is pruned, and no global
import-closure pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The DAG's Step 4 still said the sheaf-cup naturalities were unproved, but the current
library already contains the two resolution-map statements needed to complete them.
The argument needs those resolution maps explicitly; cochains alone on an arbitrary
open cover cannot lift arbitrary sheaf cohomology classes. No affine-cover assumption,
comparison-isomorphism hypothesis, flatness assumption, or altered cup definition is
introduced. Empty schemes, zero coefficient maps or sheaves, and degrees zero use
the same kernel, additive-map, and Leibniz arguments.

The remote checkout does not contain the untracked Stacks TeX sources. The official
Stacks pages for Tags 01FD, 0FKU, and 0FKV were read online; the delivery follows the
already stated resolution-map lemmas and their documented Godement argument.

## Second reading by S3

1. Interface preservation: PASS. Read the whole delivered module and compared its
   diff with the repository version. Every existing declaration's statement and
   visibility is unchanged; all existing definition bodies and public imports are
   unchanged. The only Lean additions are two plain proof imports, three private
   helpers, scoped heartbeat settings, and proofs of the two original holes.
   There is no interface change or forced adaptation needing a change record.
2. Proof and axioms: PASS. Local compilation through `lcompile.py` completed
   without errors or warnings in 43.0 seconds. A scratch copy containing
   `#print axioms` for all seven public theorems and all three new private helpers
   compiled cleanly in 42.0 seconds. Coefficient naturality, all three helpers,
   and the three previously proved coefficient/refinement naturalities use only
   `propext`, `Classical.choice`, and `Quot.sound`. Pullback naturality, the main
   comparison theorem, and refinement composition additionally use `sorryAx`
   from existing lower dependencies. No other axiom occurs. No `sorry` or forbidden
   declaration occurs in the delivered file. `map_additive_cycle` constructs its
   underlying value as the degree component of the supplied cochain map, and its
   kernel proof follows from commutation and the input's kernel equation.
   The resolution existence statements are eliminated inside theorem proofs;
   no definition chooses arbitrary data from an unproved existence statement.
3. Split statements and edge cases: PASS; none are added. Read the existing
   simultaneous coefficient and pullback resolution-map statements and the
   resolution-data and cup-characterization definitions. The three helpers prove
   class surjectivity, a cocycle for the actual bilinear product, and transport of
   an actual cocycle. Their arguments remain valid in degree zero, for zero
   coefficients or coefficient maps, and on the empty scheme. Leibniz kills both
   differential terms, including degree zero; the cross-ring helper uses only
   additivity, with no scalar-linearity or flatness assumption. The public proofs
   combine these distinct steps rather than applying a renamed target statement.
4. Shortest route and pruning: PASS. Repeated the Mathlib search with
   `Alexander.?Whitney|CupResolutionPairing|CupAcyclicResolution`, a LeanFinder
   query about bilinear chain pairings inducing natural cohomology products, and
   Loogle `Function.Surjective, "homology"`; no applicable shorter theorem was
   found. Searched both library roots for resolution-class surjectivity, product
   cycles, and coefficient/pullback cup naturality. The matching surjectivity and
   product-cycle helpers in `ModuleCohomologyCupProduct` and
   `ModuleCupRealizationEvaluation` are private; their underlying Mathlib APIs
   are already used here. Scalar-cup results have different coefficient and cup
   definitions. Every direct import supplies a public-signature notion or an
   explicitly used proof declaration. The two new proof imports are plain imports.
   Every old `proof_deps` node is still used, so `No longer needed: None` is complete.
   The unit `sk-prop-av-cube`, including its empty `realized` lists, is unchanged.
5. DAG agreement: PASS. The only changed node fields are `proof`, `proof_deps`,
   and `proof_origin`. The dependency list equals the union of all proof-step
   `uses`; each dependency's recorded Lean module and declaration was checked.
   Step 4 describes the actual lifts, Leibniz cocycle construction, coefficient
   and additive pullback transports, class equations, and pairing equations.
   The source and unit route are preserved, and there are no new nodes to audit.

Second-reading changes: added this review and the explicit axiom findings to the
report. No Lean or node repair was needed. The delivery closes the two original
local holes and adds zero holes; full axiom closure of pullback still depends on
the existing lower work. No global ledger net or module pruning is claimed.
