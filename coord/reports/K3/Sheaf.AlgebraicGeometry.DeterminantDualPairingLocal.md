## What changed

`Sheaf.AlgebraicGeometry.DeterminantDualPairingLocal` now proves
`AlgebraicGeometry.exterior_dual_pairing_app_bijective` without changing its signature.
The proof imports the new module `Sheaf.AlgebraicGeometry.DeterminantDualLocalFrames`.
It obtains local primal and dual wedge bases and the internal dual evaluation equivalence,
uses the given determinant formula and Mathlib `exteriorPower.basis_coord` to show that the
map sends the source basis to the target dual basis, and identifies the map with the resulting
linear equivalence by basis extensionality. Both modules compile with the required launcher. The second reader moved the exterior basis
and dual basis imports out of the frame module and made them plain proof imports of the target;
the frame signature needs neither additional import.

The target node copy records this route. The new frame statement has no pairing morphism `f`
and no determinant hypothesis: it isolates the geometric steps 1-2 of the old plan. The old
step 3 (the determinant calculation and bijectivity) is now an actual Lean proof. Frames are
eliminated only inside the theorem proof; no definition chooses data from the new existence
statement. There are no changed existing public signatures, definitions, instances or attributes.

## Proved and sorry left

Closed: `AlgebraicGeometry.exterior_dual_pairing_app_bijective`
(node `lem-sc-exterior-dual-pairing-local-bijective`).

Added and left: `AlgebraicGeometry.exterior_dual_local_frames`
(node `lem-sc-exterior-dual-local-frames`), in its own new module. Its proof is exactly
`by sorry`, with its source, full coordinate reconstruction and sheafification argument in
its docstring and node. The item itself has no remaining `sorry`.

This is a decomposition: one upper hole closed, one strictly lower geometric hole added,
net zero holes closed. The determinant calculation and basis-equivalence conclusion are proved.
The remaining task is restriction of finite-free sheafification and internal Hom evaluation,
independent of any determinant pairing. Edge cases checked mathematically: n=0 gives the
single empty wedge, n>r gives empty wedge bases and zero modules, and zero rings and empty
opens require no nontriviality assumption. Both modules compile cleanly.

## No longer needed

Removed the redundant explicit proof import
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom` from the target module;
it remains available transitively through the unchanged public `Dual` import.

The target's direct proof dependencies are now `lem-sc-exterior-dual-local-frames` and
`lem-weil-pbc-exterior-power-free-basis`. The old dependencies `def-pur-sheaf-hom`,
`def-sc-sheaf-exterior-power`, `def-weil-pbc-free-module` and
`lem-pc-sites-module-sheafification-interface` are used by the new geometric frame node,
so they are not pruned from the argument. The standalone planned application of
`lem-sc-exterior-power-dual-pairing` is unnecessary: the proof computes the determinant via
`exteriorPower.ιMultiDual_apply_ιMulti` and `exteriorPower.basis_coord`. Mathlib's Pairing
module remains a transitive import of Basis; no entire library module is claimed pruned.
No unit statement or unit proof step is bypassed. Every old direct dependency is accounted
for above: four move into the frame argument, the exterior basis remains direct, and
`lem-sc-exterior-power-dual-pairing` is no longer a direct node dependency.
The frame module no longer publicly imports `Mathlib.LinearAlgebra.ExteriorPower.Basis` or
`Mathlib.LinearAlgebra.Dual.Basis`; both are used only by the target proof and imported there
without `public`. No complete library module becomes unreachable.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt ended without a reduction after finding no complete geometric proof.
The existing DAG dependencies supply the exterior basis theorem, sheafification adjunction
and internal Hom definition, but do not directly state the needed local sheaf coordinate
identifications. The new node makes precisely those identifications a separate work item.
The injectivity/surjectivity split explored during this session was discarded completely.

[Stacks Tag 0BRT](https://stacks.math.columbia.edu/tag/0BRT) motivates determinant inversion
but does not explicitly state or prove this finite-free frame lemma. Accordingly the new
node marks the expanded coordinate argument as agent-written, rather than claiming it is
verbatim in that source. Mathlib source basis and dual basis declarations were read directly.

## New nodes

`lem-sc-exterior-dual-local-frames` is in
`dag/nodes/sec-picard-framework/lem-sc-exterior-dual-local-frames.json` and realized by
`AlgebraicGeometry.exterior_dual_local_frames` in
`lean/Sheaf/AlgebraicGeometry/DeterminantDualLocalFrames.lean`.
It provides section bases, wedge formulas, internal dual coordinate sections, and the
identity-open evaluation linear equivalence on any subopen of a finite-free trivialization.
Its complete proof in words expands old plan steps 1-2; no hypothesis mentions `f`.
LeanFinder returned ring exterior-power and pairing results, with no sheaf frame theorem;
Mathlib grep returned no matching local frame theorem. LeanSearch was unavailable (HTTP 500)
and is recorded as unavailable. Blueprint search found no matching exterior-dual node.
No change record is needed: no existing statement or definition changed.

## Second reading by K3

1. Compared the whole delivered target module with the repository using `diff`, and checked
   its theorem signature byte for byte by extraction. Only the proof and plain proof imports
   change; the existing docstrings, signature, public imports, definitions and attributes
   are unchanged. No change record is required. Verdict: pass.
2. Compiled both modules in import order through `lcompile.py`, with no errors or warnings.
   A scratch module printed axioms of both declarations: exactly `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`. The latter is expected from the explicitly listed frame hole
   and existing exterior-sheaf dependencies. There is exactly one delivered `sorry`, in the
   named frame theorem, and no forbidden declarations or new definitions. The theorem proof
   eliminates the existential frames locally; it never defines an object by arbitrary choice
   from an unproved existence result. Verdict: pass as a decomposition, not a closed proof.
3. Read the frame signature, complete coordinate/sheafification docstring, and new node.
   It is true on arbitrary subopens, since a finite free sheaf is a finite product of the
   structure sheaf there; its coordinate restrictions make the exterior presheaves sheaves,
   and natural maps to the structure sheaf are recovered from their basis values. Tested
   r=0, n=0, n>r, zero section rings, and empty opens mathematically. In degree zero the
   singleton empty wedge is the unit; above rank the index set and modules are empty/zero.
   The lemma has no f or determinant formula and isolates the geometric identifications;
   the determinant computation and basis equivalence remain actual checked Lean proofs.
   Repeated searches with different words: LeanFinder query "sections of locally trivial
   vector bundle dual sheaf evaluate isomorphism on affine open", launcher grep query
   "homObj.*free|free.*homObj|exterior.*sheafification", and rg over Mathlib and both library
   roots. Read upstream `homObjFreeIso`, `homObjFreeUnitIso`, and
   `bidual_app_bijective_of_iso_free`: these support the internal-dual coordinate argument
   but neither assert the exterior sheaf frames nor the evaluation equivalence in this lemma.
   Found no duplicate or few-minute proof of the full geometric remainder. Verdict: pass.
4. Read the proof downward: local frames, determinant evaluation on every pair of basis
   vectors, equality with the transported dual basis, then bijectivity of a linear
   equivalence. Mathlib's exterior basis coordinate formula supplies the ring calculation;
   a complete ring pairing theorem alone cannot supply the sheaf identifications. The
   remaining frame problem is independent of the pairing. Checked every old proof dependency
   against the No longer needed section. Read `dag/units/sk-thm-picard-duality.json`: the
   item's node is not a realized unit statement or step (the realized lists are empty);
   this reduction stays below the unit level and changes none of its route. Verdict: pass.
5. The existing node differs only in `proof`, `proof_deps`, and `proof_origin`. Its steps
   describe the written Lean argument and its dependencies are their union. Checked the
   new node's required source, provenance, search, blueprint, chapter/unit, creation and Lean
   fields; its stored Lean statement is byte-for-byte the declaration signature and its
   dependencies are exactly the union of step uses. Its proof is honestly marked agent-written
   expansion of the local argument, not a claim that Stacks states the frame lemma.
   Verdict: pass.

Changed only import placement: removed both extra public Mathlib basis imports from the new
frame module, whose signature already elaborates from its two sheaf imports, and added them
as plain proof imports in the target module. Updated the report to record that pruning and
this second reading. No proof, signature, definition, node statement or unit was rewritten.
