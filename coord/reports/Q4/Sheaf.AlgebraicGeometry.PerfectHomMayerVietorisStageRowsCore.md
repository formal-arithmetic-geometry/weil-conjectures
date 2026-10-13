## What changed

The statement and public imports of
`Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisStageRowsCore` are unchanged.
Its proof now constructs the five-term group rows from a cocone of distinguished
triangles in the fixed category D(O_Y), rather than leaving their construction,
zero composites, and short-complex presentations as one hole.

`PerfectHomTriangleRow` contains actual constructions of the row, its functorial
maps, and the row map induced by a triangle cocone. The boundary square uses
`Functor.homologySequenceδ_naturality`; identity and composition are checked on
all five components. Its proved theorem `perfectHomTriangleRow_presentations`
constructs all three distinguished-triangle presentations, including the sign
and shift isomorphisms. The proof extracts the explicit isomorphisms used by
Mathlib's `homologySequence_exact₁`, `homologySequence_exact₂`, and
`homologySequence_exact₃`; it does not infer a triangle presentation merely from
exactness. The three private window helpers are proved, with no holes.

`PerfectHomMayerVietorisTriangleCocone` states the remaining geometric step:
existence of a coherent cocone of Mayer--Vietoris triangles pushed to Y, the
adjunction identifications of its first components with canonical stage and
limit Hom transport, and the four local column comparisons. It has one named
whole-proof `sorry`. It supplies neither abelian-group rows nor complex or
short-complex presentation witnesses. Those are constructed and proved in the
item from the triangle cocone. Thus this is a decomposition, not a complete
geometric proof and not a claimed positive net hole reduction.

The item now imports the two new modules for its proof. Its seven former
geometric proof imports moved to the geometric intermediate module, where the
same dependency route remains available for its next worker. All writes are in
the item sandbox; no dependency interfaces or consumer files are changed.

## Proved and sorry left

Closed in the item:
`AlgebraicGeometry.perfect_hom_mayerVietoris_stage_rows_core`
(node `lem-pc-perfect-hom-mayer-vietoris-stage-rows-core`), from the new geometric
intermediate statement and the fully proved row construction/presentation lemma.
The item has no remaining textual `sorry`.

Proved in the new categorical module:
`AlgebraicGeometry.perfectHomTriangleRow_presentations`
(node `lem-pc-perfect-hom-triangle-row-presentations`). Its actual data
constructions are `perfectHomTriangleRow`, `perfectHomTriangleRowFunctor`, and
`perfectHomTriangleRowCoconeMap`. Its three private window isomorphisms also
contain no `sorry`.

Added and left open:
`AlgebraicGeometry.perfect_hom_mayerVietoris_triangle_cocone`
(node `lem-pc-perfect-hom-mayer-vietoris-triangle-cocone`). This is the only new
hole. One upper hole closed and one lower geometric hole added: a decomposition
with net zero textual holes in this delivery. The existing holes of dependencies
are not changed.

All three delivered modules compile with lcompile.py. The delivery dry run
printed OK, with only the independent second-reading section deferred to the
second reader; nothing was pushed. No target statement,
existing declaration signature, definition, or visibility is changed.

## No longer needed

No geometric dependency node or module is globally pruned. These proof imports
were removed from the item and relocated to the new geometric module:

- `Sheaf.AlgebraicGeometry.PerfectThickClosure`
  (`lem-pc-perfect-thick-closure`);
- `Sheaf.AlgebraicGeometry.LocalizedPullbackPerfectModel`
  (`lem-pc-localized-pullback-perfect-model`);
- `Sheaf.AlgebraicGeometry.PerfectImpliesQCoh`
  (`lem-sc-perfect-qcoherent`);
- `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`
  (`lem-pc-affine-derived-pullback-tensor-tilde`);
- `Sheaf.AlgebraicGeometry.DerivedAdjoint`
  (`lem-pc-ringed-spaces-derived-adjoint`);
- `Sheaf.AlgebraicGeometry.DerivedMayerVietorisFunctorial`
  (`lem-pc-derived-mayer-vietoris-functorial` and its triangle dependency);
- `Sheaf.AlgebraicGeometry.PerfectHomStageColimit`
  (`lem-pc-perfect-hom-stage-colimit`).

The categorical module needs only the scheme derived-category carrier, so it
imports `Sheaf.AlgebraicGeometry.DerivedCategory`, not `PerfectHomTransport`.
All existing public imports of the item are preserved. The unit record
`sk-thm-picard-semicon` has empty realized statement/step entries; this split
keeps the Mayer--Vietoris route and bypasses no realized unit step.

## Where the brief, the DAG or earlier work was wrong

No signature correction or forced adaptation was needed. The sources were read
online at Stacks Tags 09RE, 08BW, and 0149 because this checkout lacks their
literature tex files. Searches were run via msearch.py (LeanFinder, Loogle, grep,
and LeanSearch). LeanSearch returned Internal Server Error, recorded as
unavailable rather than as a no-match result. Mathlib supplied the canonical
boundary naturality and all three window isomorphisms, but no geometric triangle
cocone with the specified transport.

The existing `schemeDerived_mayerVietoris_directImage` dependency is already
marked STATEMENT-DISPUTED: arbitrary choices of direct-image comparison
isomorphisms do not supply canonical unit compatibility. This delivery neither
changes nor silently uses that missing compatibility. The remaining geometric
lemma's proof explicitly requires comparisons pinned by the right-derived
functor's derivation unit, with identity and composition justified by uniqueness
of the derived lift. That compatibility remains part of the open geometric work.

Edge cases: the categorical proof works for zero/split triangles, arbitrary
objects M, and each r allowed by r+2≤4. It does not assume nonzero local Hom
groups. A single-stage diagram has the same functor and cocone constructions.
Empty opens use zero local Hom groups in the geometric plan and are not excluded.
No arbitrary existence witness supplies data in a definition: all new definitions
are explicit constructions from supplied triangles, morphisms, and cocones.

## New nodes

`lem-pc-perfect-hom-triangle-row-presentations` records the actual canonical
five-term Hom-row construction and its proved three-window presentation theorem
in `Sheaf.AlgebraicGeometry.PerfectHomTriangleRow`. The windows use T.rotate[-1],
T.invRotate[0], and T[0]. Its proof steps are direct categorical constructions
from Mathlib, with no geometric proof dependencies and no new hole.

`lem-pc-perfect-hom-mayer-vietoris-triangle-cocone` records the remaining
geometric cocone, central adjunction comparison equations, and local column
comparisons in `Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisTriangleCocone`.
It inherits the geometric dependency route of the item; the categorical
complex/presentation work has been removed from that remaining hole.

The item's node proof, proof_deps, and proof_origin are updated to the actual
triangle-cocone-to-row argument. No change record is needed: existing interfaces
and all target statements are unchanged.

## Second reading by Q4

1. **Statements and interfaces.** Compared the delivered core module with the repository version byte for byte at every existing declaration. The target signature and all existing declarations are unchanged; only proof imports and the proof body changed. The two added modules introduce the stated row construction/presentation theorem and the geometric cocone split exactly as recorded in their DAG nodes. Verdict: pass.

2. **Proof and axioms.** Compiled all three delivered modules with `lcompile.py --all`. There are no forbidden declarations and no `sorry` in the proved row module or target module. `perfectHomTriangleRow_presentations` has only `propext`, `Classical.choice`, and `Quot.sound`; the geometric cocone is the single named `sorry` listed in this report, and the target inherits that `sorryAx` as intended. Verdict: pass.

3. **New statements.** Checked the row construction on all three finite windows, including zero/split triangles and arbitrary objects, and checked that the geometric cocone theorem supplies only the remaining geometric data. The split-off cocone is strictly simpler than the target and has its source, proof description, and DAG node; no duplicate library statement was found. Verdict: pass.

4. **Pruning and route.** The target proof uses the cocone theorem and the fully proved categorical row/presentation theorem. Removed geometric imports from the target and relocated them to the geometric intermediate module; no further proof dependency can be removed without changing the remaining geometric route. The unit route remains the Mayer–Vietoris route, with no unit step bypassed. Verdict: pass.

5. **DAG agreement.** The target and both new node records match the declarations, proof dependencies, proof origins, and split status in the delivered files. The report's added hole is exactly `AlgebraicGeometry.perfect_hom_mayerVietoris_triangle_cocone`; no definition contains a hole. Verdict: pass.

Changed during second reading: no Lean proof or statement changes were necessary; added this review section and removed the temporary `lean/Check.lean` scratch file before delivery.
