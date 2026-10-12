## What changed

Replaced the proof of `AlgebraicGeometry.leray_complex_cocycle_comparison` with the
node's direct kernel/cokernel argument. No declaration signature, definition, or
existing docstring changed. Transport on sections is restriction along
`Opens.map_top`. Evaluation preserves the kernel defining cycles, so its mapped
kernel universal property constructs the lift `c`. Kernel uniqueness proves both
naturality of `c` and its compatibility with incoming boundaries. Composing with
the sheaf homology quotient kills those boundaries. The scalar-forgetful functor
preserves the cokernel defining homology, giving the component `δ`; its cokernel
universal property and the naturality of `c` give the natural transformation `τ`.
The two elementwise equations follow by evaluating the kernel and cokernel lift
identities at the given cycle.

The proof works uniformly at degree zero: it uses the short complex's `toCycles`
rather than assuming that a predecessor degree exists. It also imposes no conditions
on the complex or on the schemes, so zero complexes and empty schemes need no
special treatment. The argument follows the existing node's three steps and keeps
the unit route.

Removed two redundant ordinary imports. Both remain available through the unchanged
public import `Sheaf.Paper.PQFCohomology`. Added a local heartbeat limit because
elaboration of mapped kernels, cokernels, and composed functors exceeds the default
limit; single-file compilation takes approximately 16 seconds.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.leray_complex_cocycle_comparison`
(node `lem-pc-leray-complex-cocycle-comparison`).

There are no remaining `sorry`s in the item, no added holes, and no split-off
statements or new modules. This is a proof from the existing library and Mathlib
APIs, not a decomposition. Existing library instances remain dependencies; in
particular the direct-image additive instance is supplied by
`RingedSpace.moduleDirectImage_additive_proof` in its existing module.

Validation: the second reader independently compiled the file without errors or
warnings (14.6 seconds), and compiled a scratch copy with `#print axioms`. The
result is `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`: the item
has no direct hole but still rests on existing open library statements, including
`RingedSpace.moduleDirectImage_additive_proof`. This does not certify the final
axiom-free target criterion. The delivery dry run supplies the comprehensive
local axiom probe and preflight checks; server compilation is disabled by default
in the launcher, and the maintainer global build verifies the landing.

## No longer needed

Removed redundant explicit imports:
- `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage`
- `Sheaf.Topology.RingedSpaceModuleCohomology`

Their definitions are still used and their modules remain transitively imported
through `Sheaf.Paper.PQFCohomology`; this removal does not prune them from the target
closure. No DAG nodes or dependency modules are no longer needed. The existing
proof-dependency list and node plan remain accurate, so no node update is needed.

## Where the brief, the DAG or earlier work was wrong

None. The three elementary steps of the node are realized using
`KernelFork.mapIsLimit`, `Fork.IsLimit.hom_ext`,
`CokernelCofork.mapIsColimit`, and `Cofork.IsColimit.hom_ext`.
Mathlib's `ShortComplex.homologyIsCokernel` makes the quotient step explicit.
No injective resolution, spectral sequence, acyclicity, or new intermediate
statement is required.


## Second reading by B2

1. **Visible declarations unchanged — pass.** Read the whole module and its diff
   against the repository. Independently compared the original and delivered
   theorem signature byte for byte: identical. No definitions, existing docstrings,
   public imports, or other declarations changed; only the proof, local elaboration
   options, and two redundant ordinary imports differ. No change record is needed.
2. **Proof and axioms — pass, conditional on existing dependencies.** Independently
   compiled the delivered file cleanly with `lcompile.py`. A scratch copy with
   `#print axioms AlgebraicGeometry.leray_complex_cocycle_comparison` compiled
   cleanly and reported only `propext`, `Classical.choice`, `Quot.sound`, and
   `sorryAx`. There is no direct `sorry`, new axiom, unsafe declaration, opaque
   declaration, external implementation, or hollow definition in the delivery.
   Read the existing direct-image additive proof and instance: that library proof
   remains open. The lifts used here are the canonical kernel and cokernel
   universal constructions, uniquely determined by their inclusion/quotient
   equations; no arbitrary witness is extracted from mere existence.
3. **Split-off statements — pass (none).** No new statements, nodes, modules, or
   holes are added. Degree zero is covered by `sc q` and `toCycles`, including its
   zero incoming differential. The argument uses no nonemptiness assumption and
   works for the zero complex and empty schemes.
4. **Route and pruning — pass.** Read the kernel lift, its naturality and boundary
   identity, the cokernel descent, and the two final elementwise identities.
   Independently searched the library and Mathlib for section/homology comparisons
   and `mapCyclesIso`. The latter is a related kernel-identification API, but does
   not supply this natural transformation and its elementwise equations directly;
   the existing universal-property proof is correct and needs no rewrite.
   `PQFCohomology` publicly imports both removed ordinary imports, whose definitions
   remain used. Therefore no module or old proof-dependency node is pruned.
   Read `dag/units/sk-thm-picard-rr.json`: this lemma is below the unit, its
   `realized` fields are unchanged, and the unit's route is not bypassed.
5. **DAG agrees with Lean — pass.** Read the item node and the Lean records of
   every old proof dependency. All five dependencies still describe notions used
   by the proof: direct image, sections, sheaves of modules, cochain complexes, and
   abelian homology. The three proof steps are realized by kernel lifting,
   annihilation of boundaries and cokernel descent, then naturality. The existing
   `proof`, `proof_deps`, and source-based `proof_origin` remain accurate. There
   are no new node fields to validate and no node update is needed.

Second reading changed only this report: recorded the independent compilation
and explicit axiom result, clarified the remaining dependency holes, corrected
its claim that the launcher dry run necessarily performs a server compile, and
added this five-point review. The Lean proof needed no repair.
