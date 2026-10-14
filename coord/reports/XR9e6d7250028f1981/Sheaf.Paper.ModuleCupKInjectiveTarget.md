## What changed

Repaired the red-build return recorded in `request.json`: a non-module
`BatchProbe.lean` could not import `Sheaf.Paper.ModuleCupKInjectiveTarget`
because its generated anonymous local symmetric instance had the same name as
one in `GlobalTensorPullbackMonoidalNormalization`. The independent second
reader reproduced this exact error with the supplied repaired files, even though
both module-mode source compilations passed. All seven anonymous local instances
in the target now have explicit `moduleCupTarget...` names. Their types and
bodies are unchanged. The pullback and polygon imports remain proof-only imports.
The polygon keeps only its two necessary public imports; seven redundant direct
imports already provided publicly by the pullback module were removed.

The earlier H10 performance repair is retained: both delivered modules activate
the existing named global pullback instances at priority 2000, sharing tensor
instance expressions at the theorem boundary without changing the original
definition data. No theorem was split to meet a compile limit.

The target declaration and its proof respect the local irreducibility attributes
by enabling `backward.isDefEq.respectTransparency` and its `.types` option.
Propositional local instances in the proof use `have`; the monoidal data still
use `let`. The target's global tensor pullback and polygon imports are private: they are
used to elaborate the proof. The polygon publicly imports the pullback because
its statement names `moduleCup_globalTensorDiagram`. No theorem was split to meet the limit,
no limit or checking setting was relaxed, and the mathematical route is unchanged.

The existing decomposition is retained: construct the induced derived
adjunction, define the cup as the transpose of the tensor of the counits after
the tensor comparison, prove naturality, and apply the specified-transpose
polygon using the existing counit and tensor comparison theorems.
The earlier `moduleCup_sourceLax` def-to-abbrev change remains, with identical
data; it is recorded in `coord/changes/module-cup-source-lax.md`.

Validation of the final repair is recorded in the independent second reading
below. Earlier timing and dry-run claims described the H10 attempt, which did
not exercise the failing non-module import context, and are superseded.

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

The second reader also removed redundant direct imports from the polygon:
`Sheaf.Paper.ModuleCupNaiveMap`, `Sheaf.AlgebraicGeometry.GlobalDerivedHom`,
`Sheaf.AlgebraicGeometry.DerivedTensorStructure`,
`WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal`,
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution`,
`Mathlib.CategoryTheory.Functor.Derived.Adjunction`, and
`Sheaf.Algebra.Homology.KFlatPullback`. All remain available through the
polygon's public pullback import; no additional global pruning is claimed.

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

The earlier worker reported H10: its returned version timed out despite
earlier successful runs near the limit. Changing only tactic shape and folding the adjunction was
insufficient. Sharing the already defined pullback instances removes the costly
conversions between separately named but definitionally identical tensor data.
The final source retains the original definition bodies. The red-build repair
renames local instance declarations to prevent duplicate exported names; theorem
elaboration still activates the common instances.

The earlier rejected arbitrary-natural-pairing argument is not restored:
naturality alone cannot identify the cup (the zero pairing is natural).
The retained polygon instead requires the actual transpose, the canonical
localization comparison, the canonical transported derived unit, naturality of
the tensor comparison and the tensor/counit normalization equations.
The target statements and their meanings are preserved. The current return was
an import-environment collision, rather than a timeout; private imports alone
did not resolve it, and the uniquely named local instances address that failure.

## New nodes

`lem-sc-module-cup-adjunction-polygon` in
`dag/nodes/sec-abelian-varieties/lem-sc-module-cup-adjunction-polygon.json`
is the existing new node of this delivery: the K-injective compatibility
calculation for the specified transpose. Its Lean statement and proof-dependency
records agree with the module. The target node records the explicit transpose,
proved naturality and this remaining polygon. This red-build repair adds no node or sorry.

Change record: `coord/changes/module-cup-source-lax.md`.

## Second reading by XR9e6d7250028f1981

I independently read request.json, the returned delivery.diff, both complete
Lean modules, both nodes, the change record, and the repository stage-3 briefs,
AGENTS.md §§4–5, roles/lead.md §3, and the cube unit record. I did not rely on
the earlier A2 review or its successful module-mode compiles.

1. Interface and mathematics: PASS. The existing target theorem signature is
   byte-for-byte identical to the repository and its node. The comparison
   natural transformation's signature and entire body are unchanged. The
   source lax structure remains exactly the canonical inferred structure; the
   recorded def-to-abbrev change only changes transparency. The shared tensor
   instances have the same bodies as the original instances. I renamed seven
   anonymous local instances without changing their types or bodies. No target
   hypothesis, conclusion, tensor construction or derived functor changed.

2. Compilation and trust: PASS. Both touched modules compiled with lcompile.py,
   each below 60 seconds (after import pruning and instance renaming: polygon
   15.8 seconds, target 37.6 seconds). The initial renamed target emitted five
   line-length warnings; I wrapped those declarations without changing tokens.
   Final warning-free compilation is also required by the delivery dry run.
   The unchanged direct importer ModuleCupNaiveDerivedCompatibility compiled
   cleanly against the repaired overlay in 45.1 seconds. A scratch non-module
   batch probe using tools/build.py's BATCH_PROBE reproduced the exact returned
   duplicate-instance error before my repair, then passed after renaming:
   SHEAF-PROBED reports 8 polygon declarations and 11 target declarations, with
   no SHEAF-AXIOM entries. The only SHEAF-SORRY entry is the recorded polygon
   theorem. Explicit #print axioms shows only propext, Classical.choice and
   Quot.sound for both definitions, and additionally sorryAx for the polygon
   and the dependent existential theorem. There is no new axiom, unsafe,
   opaque, extern, implemented_by, skipped kernel check or hollow definition.
   Every compile used lcompile.py locally; no lake or server compile was run.

3. Remaining split: PASS as a decomposition, not a complete proof. The polygon
   fixes μ to the adjunction transpose and β and qLax to their canonical maps.
   Its tensor, counit and ordinary normalization hypotheses are independently
   supplied by the target proof. It proves only compatibility, whereas the
   target genuinely constructs μ and proves naturality. It is strictly a part
   of the argument, not an existential restatement. I checked the transpose
   calculation against [Stacks 0FP3](https://stacks.math.columbia.edu/tag/0FP3),
   with [0FP0](https://stacks.math.columbia.edu/tag/0FP0) supplying the tensor
   polygon and [0FP1](https://stacks.math.columbia.edu/tag/0FP1) the counit square.
   For degree-zero complexes the ordinary counit equation gives tensor-section
   evaluation; for zero φ both routes are zero; shifts and unbounded complexes
   use the same degreewise summand identities, without a boundedness hypothesis.
   Independent grep, Loogle and LeanFinder searches found supporting monoidal
   counit and derived-adjunction lemmas, not the remaining totalization identity.
   Its complete proof in words and matching node remain present. No new hole
   was introduced to repair the compiler failure, and no short existing theorem
   found by these searches closes the remaining polygon.

4. Route and pruning: PASS. The actual proof constructs the derived adjunction
   from Mathlib Adjunction.derived, proves naturality with the Hom-equivalence
   square and counit naturality, then supplies the actual normalization equations
   to the polygon. Data obtained from the pullback existence theorem occur only
   inside this existential theorem proof, never in a definition. I removed seven
   redundant public imports from the polygon; its two remaining public imports
   supply declarations used in its statement. The target's added proof imports
   remain nonpublic. The report accounts for every old proof dependency removed.
   No unit-level route is bypassed or unit record changed; sk-prop-av-cube's
   current realized lists are empty, and this remains its supporting cup route.

5. DAG and report: PASS. Both lean.statement fields match the complete Lean
   signatures exactly, the existing node's mathematical statement and stmt_deps
   are unchanged, and each proof_deps is exactly the union of its proof-step
   uses. The target node describes the construction, naturality and polygon
   application actually written. The polygon node records the explicit maps
   and assumed equations, its source, complete proof plan and blueprint route.
   The report correctly calls the result one upper hole replaced by one lower
   hole (net zero), and distinguishes this red-build collision from earlier H10.

Second-reader changes: reproduced and repaired the actual non-module import
failure by assigning unique moduleCupTarget... instance names; removed seven
redundant polygon imports; wrapped the renamed declarations to meet the style
limit; corrected the report's obsolete validation and public-import claims;
updated the change record and its status to open. No proof or statement was
weakened, and the retained polygon sorry was not changed.

The first dry run compiled the final wrapped source and ran the per-file axiom
probes successfully, then stopped on metadata: the returned new polygon node
still named A2 rather than this repair group, the change record omitted six
textually matched downstream anonymous-instance users, and that run had read
the report before this second-reading section was appended. I corrected the
new node's created.group and lean.by, listed those users with their unchanged
local constructions, and restored the existing target node's reviewed_proof
field to the repository version (historical review fields are not owned by this
repair). These metadata edits do not change either mathematical statement.

As an additional interface check, I compiled a scratch module containing the
repository's original theorem statement under the repository's original local
instance types and bodies (only their names were made unique in the scratch).
Its proof is exactly `moduleCup_exists_kinjective_target_pairing X` from the
repaired module. Lean accepted it in 24.5 seconds, confirming that the repaired
elaborated theorem supplies the original interface, not only identical source
text. The scratch's longer helper names produced line-length warnings only;
this file is not delivered.

Final dry run: deliver3.py --no-push printed `OK (dry run)` at commit
`23b4b32a12`: both final delivered modules compiled without errors or warnings,
the per-file axiom probes ran, and all stage-3 preflight checks passed. The
normal delivery follows with .check and this independent reading in place.
