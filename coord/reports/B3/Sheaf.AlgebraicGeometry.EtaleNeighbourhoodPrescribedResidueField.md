## What changed

Filled the proof of `AlgebraicGeometry.Scheme.exists_etale_neighbourhood_prescribed_residueField`
in `lean/Sheaf/AlgebraicGeometry/EtaleNeighbourhoodPrescribedResidueField.lean`.
The signature, docstring, and imports are unchanged. The proof follows the existing five-step
DAG plan: take an affine chart, transport the finite separable extension along its residue-field
isomorphism, apply the proved ring-level realization theorem, compose the étale morphisms,
and verify compatibility using the proved Spec residue-field naturality equation.
`Module.Finite.of_equiv_equiv` and `Algebra.IsSeparable.of_equiv_equiv` perform the transport.
The supplied `k : Type v` is used directly by the ring theorem, which returns a ring in `Type u`;
no universe restriction or arbitrary data definition is introduced.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.Scheme.exists_etale_neighbourhood_prescribed_residueField`
(node `lem-weil-pbc-etale-neighbourhood-prescribed-residue-field`).
No sorry remains in the delivered module; no holes or new declarations were added.
The proof uses the existing proved `Algebra.exists_etale_residueField_equiv` and
`AlgebraicGeometry.Spec.residueFieldMap_residueFieldIso_hom`.
Local single-file compilation is clean. The delivery dry run checks the declaration's axioms.

## No longer needed

None. Both existing proof imports are used. The affine chart, finite separable ring realization,
Spec naturality, and étale composition steps of the existing DAG remain necessary; no planned
node or module is pruned. Public statement imports are unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The historical reviewed_lean note says the ring-level sibling had
no Lean statement yet; the current node now attaches the proved source-library theorem, so this
is no longer an obstacle. No new nodes, statement corrections, or change records are needed.

## Second reading by B3

1. **Unchanged interface — pass.** Compared the delivered module with the repository using
   `diff -u`. The only change is replacing the existing theorem's `sorry` with its proof.
   The full signature, universes, docstring, imports, and public exposure are byte for byte
   unchanged. There are no definitions or other declarations added, and no change record
   is needed.
2. **Kernel proof — pass.** Independently compiled the delivered file with `lcompile.py`
   (exit 0, no warnings). Compiled a scratch copy with
   `#print axioms AlgebraicGeometry.Scheme.exists_etale_neighbourhood_prescribed_residueField`:
   exactly `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`.
   Read the entire proof: no forbidden declarations, no sorry, no hollow definitions.
   Both existential witnesses are eliminated inside the theorem proof, not used to define
   public data. The ring-level theorem is already proved; the chosen algebra and point are
   legitimate existential witnesses for the conclusion.
3. **Split statements — pass (none).** No statements are split off, and no new holes or
   nodes are introduced. Checked the directions of the transported algebra map and residue
   isomorphisms, the comap equality, and the final compatibility equation. The trivial
   extension and affine base require no extra assumption; an empty scheme has no input
   point. Independent universe levels are retained, using the upstream theorem's algebra
   in `Type u` for the supplied extension in `Type v`.
4. **Shortest route and pruning — pass.** Repeated LeanFinder search using “realize a finite
   separable extension at a scheme point by an etale neighbourhood with isomorphic residue
   field”; its results concern ring-level realization or residue-field-preserving etale
   extensions, not a shorter scheme theorem. Searched repository Lean files for this
   conclusion and transport lemmas, and read both upstream declarations actually used.
   The proof uses the proved ring realization and Spec naturality directly. Both ordinary
   imports are used by named declarations; all three public imports supply notions in the
   public signature. No proof-only import is public. Every old proof dependency is still
   represented by the affine chart, field identifications, transport, ring realization,
   etale composition, and residue-map compatibility. `## No longer needed` is complete.
   Read `dag/units/sk-thm-p1.json`: this subordinate lemma preserves the unit's `realized`
   route and bypasses no unit step.
5. **DAG agreement — pass.** Read the item's node and checked its five proof steps and
   `proof_deps` against the code. The implementation follows exactly the recorded route;
   the Stacks 02LF/00UD proof origin remains accurate. The two attached upstream nodes
   name `Algebra.exists_etale_residueField_equiv` and
   `AlgebraicGeometry.Spec.residueFieldMap_residueFieldIso_hom`, respectively, matching
   the proof. No node edits are needed.

Second reading changed only this report to record the independent checks. The Lean proof
was correct and is delivered unchanged. Closed one hole and added zero holes.
