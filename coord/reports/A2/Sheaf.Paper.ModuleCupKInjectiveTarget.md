## What changed

Repaired return H10 (reviewer X-1e2b5): the delivered target had twice exceeded
60 seconds. Both delivered modules now locally activate the existing
`globalPullbackCommRing`, `globalPullbackMonoidal`, `globalPullbackSymmetric`,
`globalPullbackColimits`, `globalPullbackPreadditive`, `globalPullbackClosed`
and `globalPullbackFlatResolution` instances with priority 2000. This lets the
pullback theorem, polygon and target proof share their instance expressions,
so conversion does not repeatedly unfold duplicate tensor constructions.
The original local instance declarations are retained. In the target the shared
instances are activated after the existing definitions, preserving their bodies.

The target declaration and its proof respect the local irreducibility attributes
by enabling `backward.isDefEq.respectTransparency` and its `.types` option.
Propositional local instances in the proof use `have`; the monoidal data still
use `let`. The global tensor pullback import is public because the theorem's
elaborated statement uses its shared instance constants. The other newly added
proof imports remain private imports. No theorem was split to meet the limit,
no limit or checking setting was relaxed, and the mathematical route is unchanged.

The existing decomposition is retained: construct the induced derived
adjunction, define the cup as the transpose of the tensor of the counits after
the tensor comparison, prove naturality, and apply the specified-transpose
polygon using the existing counit and tensor comparison theorems.
The earlier `moduleCup_sourceLax` def-to-abbrev change remains, with identical
data; it is recorded in `coord/changes/module-cup-source-lax.md`.

Validation: `lcompile.py --all` compiled both delivered modules cleanly
(polygon 52.1 seconds; target 42.9 seconds, including slot waiting). The required
direct importer `Sheaf.Paper.ModuleCupNaiveDerivedCompatibility` compiled
cleanly against this sandbox's compiled overlay in 55.4 seconds (exit code 0).
Its source was checked byte-for-byte against the repository copy; it is not
part of the delivery. No forced adaptations are made. The final delivery dry
run printed `OK (dry run)` at commit `ce037041ee`, after compilation and
axiom probes of the delivered files. Preflight passes except for the second
reading, which the designated second reader supplies. Nothing was pushed.

## Proved and sorry left

Closed upper hole:
`AlgebraicGeometry.Scheme.Modules.moduleCup_exists_kinjective_target_pairing`
(node `lem-sc-module-cup-kinjective-target`). Its construction and naturality
are proved, and its compatibility follows from the named polygon theorem.

Added lower hole:
`AlgebraicGeometry.Scheme.Modules.moduleCup_adjunction_polygon`
(node `lem-sc-module-cup-adjunction-polygon`). Its proof is exactly `by sorry`
in its own module, with a source and complete proof in words. It assumes a
specified adjunction transpose and the actual tensor and counit normalization
equations; it does not construct a pairing or prove its naturality.

Thus one original hole is closed and one strictly smaller hole split off:
a decomposition with net zero holes eliminated. H10 adds no holes. No sorry
remains in the target module; the polygon is the only sorry in delivered files.
Existing open dependencies remain open. No data are chosen from an unproved
existence theorem in a definition: the existential pullback data are used only
inside the proof of the existential target theorem.

## No longer needed

Removed direct imports relative to the repository baseline:

- `Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`.

The induced adjunction is constructed directly using `Adjunction.derived` and
K-injective absoluteness. Nodes `lem-pc-ringed-spaces-derived-adjoint-general`
and `def-pc-global-derived-rhom` are no longer immediate proof dependencies.
The latter's module remains transitively imported by the existing global
pullback module, so no global reachability pruning is claimed.

Other former immediate target proof dependencies removed from this route:
`lem-sc-module-cup-naive-map-chain`, `def-pc-tensor-complex-sheaves`,
`def-pur-sheaf-tensor-product`, `def-sc-ringed-space-module-cohomology`.
Their definitions remain in the signatures; the naive-map calculation belongs
to the polygon node. The three global pullback/tensor/counit comparison nodes
remain used. The polygon assumes the comparison equations, so it does not
itself import their proving theorems. H10 changes no mathematical dependencies
and adds no pruning. No unit-level route is bypassed.

## Where the brief, the DAG or earlier work was wrong

H10 is confirmed: the returned version times out despite earlier successful
runs near the limit. Changing only tactic shape and folding the adjunction was
insufficient. Sharing the already defined pullback instances removes the costly
conversions between separately named but definitionally identical tensor data.
The final source retains the original definitions and their local instance
names; only theorem elaboration activates the common instances.

The earlier rejected arbitrary-natural-pairing argument is not restored:
naturality alone cannot identify the cup (the zero pairing is natural).
The retained polygon instead requires the actual transpose, the canonical
localization comparison, the canonical transported derived unit, naturality of
the tensor comparison and the tensor/counit normalization equations.
The target statements and their meanings are preserved.

## New nodes

`lem-sc-module-cup-adjunction-polygon` in
`dag/nodes/sec-abelian-varieties/lem-sc-module-cup-adjunction-polygon.json`
is the existing new node of this delivery: the K-injective compatibility
calculation for the specified transpose. Its Lean statement and proof-dependency
records agree with the module. The target node records the explicit transpose,
proved naturality and this remaining polygon. No node is added by H10.

Change record: `coord/changes/module-cup-source-lax.md`.

## Second reading by A2

1. Compared the target module against the read-only repository using diff.
   Every existing declaration signature is byte-for-byte unchanged. The sole
   definition transparency change (`moduleCup_sourceLax` from an
   instance-reducible def to an abbrev) and public pullback import are declared
   in the change record. The shared instances have the same bodies as the
   original local instances. A scratch example with the repository's original
   local instances and verbatim original theorem type accepts the delivered
   theorem by `exact`, confirming definitional equality of the elaborated types.
   Verdict: statements and mathematical data preserved.
2. Recompiled the two delivered modules with lcompile.py --all: polygon 22.7 s,
   target 40.3 s, both clean. The scratch original-type check compiled in 51.8 s;
   its #print axioms for both the target and polygon lists only propext,
   Classical.choice, Quot.sound and sorryAx. Text inspection found no forbidden
   declaration or holed definition; the sole delivered sorry is the polygon's
   complete public named theorem proof. The unchanged direct importer
   ModuleCupNaiveDerivedCompatibility compiled against the overlay in 55.8 s.
   Its source is a byte-for-byte copy of the repository file and is retained
   only in scratchpad, outside the delivery. Verdict: passes the unchanged limit
   and trust-basis checks, conditional on the named open dependencies.
3. Read the entire polygon, its node, and the actual tensor-diagram, naive-map,
   pullback and counit declarations. Compared the mathematical calculation with
   Stacks Tags 0FP3, 0FP0 and 0FP1. The canonical qLax and beta equalities, specified
   transpose, full tensor diagram, derived counit square and ordinary evaluation
   equation fix the maps needed in the calculation. Zero maps/complexes, shifted
   complexes, and arbitrary unbounded totals introduce no additional hypothesis;
   naturality alone is not being used to identify a pairing. The polygon leaves
   only compatibility for already supplied data; construction of the pairing
   and its naturality have genuinely been proved in the upper theorem. This is
   a strictly smaller sourced decomposition, not a renamed existence theorem.
   Independent leanfinder, loogle and grep searches for monoidal-adjunction
   tensor/counit compatibility found map_μ_comp_counit_app_tensor and related
   monoidal adjunction lemmas, but no existing theorem identifying the concrete
   totalized naive section map with this derived transpose. No few-minute proof
   of the remaining totalization calculation was found. Verdict: valid split,
   one upper hole closed and one lower hole added, net zero.
4. Checked the actual proof from its construction downward: Adjunction.derived
   and K-injective absoluteness replace the general ringed-space adjunction;
   counit and tensor comparison theorems supply the polygon's hypotheses.
   Imports added only for proofs are private. The public pullback import is
   needed for shared instance constants in the elaborated statement. Compared
   old and new proof_deps: all six removed immediate dependencies are listed
   under No longer needed; no transitive reachability pruning is overstated.
   Read dag/units/sk-prop-av-cube.json: its realized fields are unchanged and no
   statement or step in the unit's route is bypassed. Verdict: route and pruning
   report agree.
5. Compared both node records with the Lean declarations, hypotheses and proof
   applications. The new polygon has its complete verbatim Lean statement,
   sourced proof steps, searches, creation/blueprint fields and split status.
   The existing target node changes only proof, proof_deps and proof_origin;
   their uses match the construction, naturality and final polygon application.
   Verdict: nodes agree with Lean.

Second reading changed no Lean proof, statement, definition or node. Added this
review section and independent search/validation evidence; the H10 instance
sharing repair is accepted. Scratch validation modules are not delivered.
