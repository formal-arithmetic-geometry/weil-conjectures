## What changed

Proved `AlgebraicGeometry.Scheme.Modules.affine_module_tensor_hom_bijective` in
`lean/Sheaf/AlgebraicGeometry/AffineModuleTensorHomBijective.lean`, keeping its signature,
visibility, and existing docstrings unchanged. Added proof-only imports of
`Sheaf.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsAdjunction` and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TopologicalPullback`.

The proof follows all three steps of `lem-sc-affine-module-tensor-hom-bijective`:
compose the two change-of-rings Hom equivalences (transporting along the given object
identities), compose with the inverse-image Hom equivalence, and identify the target
pushforward using the ring adjunction triangle and `ht`. The section formulas `hH`
and `hP` cancel the equality transports and the inverse/hom components of `κ`.
Finally `hβ` identifies this composite equivalence with the specified function.
The component adjunctions already have proofs in the supplied library.

A local continuity instance resolves the different presentations of the underlying
scheme topologies. A theorem-local heartbeat allowance covers elaboration of the
composite scalar restrictions. Explicit applications of the section formulas avoid
expensive unrestricted rewrite matching. The single-file compile completed without
warnings in 41.7 seconds, within the 60-second limit.

Searches: LeanFinder for the composite scalar-extension/inverse-image Hom bijection
returned general module/sheaf lemmas but no exact match; Loogle found
`SheafOfModules.pushforwardComp` and its component formulas; the search-service grep
returned no hits. Local `rg` found the component adjunctions and existing analogous
section calculations in `TensorPullbackAdjunction` and `AffineModuleTensorUnitLift`.
Both new proof-import directions were checked and are acyclic.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.Modules.affine_module_tensor_hom_bijective`
(node `lem-sc-affine-module-tensor-hom-bijective`).

No sorry remains in the item. No holes, modules, definitions, or declarations were added.
This is a proof, not a decomposition: one hole closed, zero holes added.

## No longer needed

None. No imports were removed. All four original proof-dependency nodes remain used:
`def-weil-pbc-topological-inverse-image`, `lem-pc-module-change-of-rings-adjunction`,
`lem-pc-module-inverse-image-adjunction`, and `lem-pc-module-pullback-adjunction`.
The unit `sk-thm-picard-duality` has no realized nodes for this item that the proof bypasses.
The route matches the existing node's proof, so no node-file changes are necessary.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface errors found. The module originally imported only the
ordinary tensor-pullback adjunction; the component adjunctions used in its DAG proof
need their own proof-only imports under Lean's module visibility rules.

The object equalities and section formulas suffice: no additional naturality formula
for the maps of `P` or `H`, affineness, quasi-coherence, or nontriviality hypothesis is used.
Zero rings, zero modules, empty schemes and empty opens require no separate exclusion.

## Second reading by F1

1. Interface preservation: PASS. Read the complete module and compared its diff with
   the repository version. After removing one extra space before `:=`, the existing
   theorem signature is byte-for-byte identical. Its docstring, visibility, section
   variables and local notations are unchanged. The only added imports are private
   proof imports; no definitions, statements or other modules are changed.
2. Kernel proof: PASS. Independently compiled the delivered module with `lcompile.py`
   without errors or warnings (32.9 seconds). A scratch copy with `#print axioms
   AlgebraicGeometry.Scheme.Modules.affine_module_tensor_hom_bijective` compiled in
   31.0 seconds and reports exactly `propext`, `Classical.choice`, `Quot.sound`.
   Scanned the source: no sorry, axiom, unsafe, opaque, implemented_by or extern.
   The local existential eliminations select proved Hom equivalences inside a proof;
   no public data is constructed from an arbitrary unproved existence statement.
3. Split statements: PASS, none. No holes or declarations were added. Checked the
   actual component adjunction statements and their section formulas. The argument
   uses only transport isomorphisms, Hom equivalences and sectionwise equality, so
   zero rings/modules and empty schemes/opens introduce no exceptional case.
4. Route and pruning: PASS. Read the proof from its conclusion through `he` and the
   equivalence `e`: it composes the two scalar-extension correspondences, then the
   inverse-image correspondence, then `pushforwardCongr` from the ring triangle
   identity. The section calculation cancels hobj/pobj transports and κ inverse/hom,
   and hβ identifies the given function. Independent local searches for composite
   Hom bijections and compatible adjunctions found no directly applicable shorter
   declaration; Loogle confirms the Mathlib `pushforwardCongr` and identity-on-section
   formulas already used. The public import supplies the statement's tensor pullback
   and adjunction; both added private imports supply component proof declarations.
   All four old proof dependencies remain used, so `No longer needed: None` is complete.
   Read `dag/units/sk-thm-picard-duality.json`: realized statement and step lists are
   empty; the proof bypasses no required unit realization.
5. DAG agreement: PASS. Read `lem-sc-affine-module-tensor-hom-bijective` and matched
   its three proof steps, four proof_deps and source/proof_origin against the Lean
   argument. The existing record accurately describes this proof; no node changes
   or new-node records are needed.

Second-reading changes: removed the extra space before the proof delimiter to restore
byte-for-byte signature formatting, and added this independent review. No mathematical
proof repair was necessary. One existing hole closed, zero holes added; no pruning.
