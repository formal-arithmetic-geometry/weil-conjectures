## What changed

Completed the proof of `AlgebraicGeometry.Scheme.exists_affine_perfect_tensor_roof` in
`Sheaf.AlgebraicGeometry.AffinePerfectTensorRoof`. Its signature is copied verbatim from the
assigned module. No definition or existing statement changes, and no adaptations are needed.
A proved private helper `affinePerfectTensorRoof_aux` keeps tensor instances as local
abbreviations while performing the computation. The public theorem applies this helper;
the original `letI` signature stays verbatim and is checked definitionally by Lean.
The proof forms H = RHom(A,E'), applies the existing perfect-source quasi-coherence theorem,
pulls alpha back under the section/tensor-Hom equivalence, obtains a Koszul section
representative, transposes it, and cancels the restricted augmentation isomorphism.
The final equality uses the actual `asIso (R.map beta)`, so its hom is definitionally the
required restricted chain augmentation.

Completed the earlier sandbox attempt by adding the two missing DAG nodes, updating the
assigned node's proof route, restoring the original theorem signature verbatim, checking
the final cancellation and preparing this report. The two new
modules retain the source arguments as complete docstring proofs. These are a decomposition
of the original argument, rather than a sorry-free proof of all underlying mathematics.

Proof-only imports now use the existing `RHomSupportedQuasiCoherentPerfectPart`, and the
new `AffineKoszulSectionRoof` and `TensorRoofTransposition`. Public imports remain identical.
The theorem-local heartbeat allowance accommodates repeated restriction/sheaf tensor instance
elaboration; every file is still checked within the normal 60-second single-file limit.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.exists_affine_perfect_tensor_roof`
(node `lem-sc-affine-perfect-tensor-roof`). No sorry remains in the assigned module.

Added two holes, each in a separate module with exactly one named public theorem:

- `AlgebraicGeometry.Scheme.affine_koszul_section_roof`
  (`Sheaf.AlgebraicGeometry.AffineKoszulSectionRoof`, node
  `lem-sc-affine-koszul-section-roof`). This represents a section of arbitrary E on U
  by a perfect K-flat augmented complex, without A, P, a tensor model or gamma.
- `AlgebraicGeometry.Scheme.tensor_roof_transposition`
  (`Sheaf.AlgebraicGeometry.TensorRoofTransposition`, node
  `lem-sc-tensor-roof-transposition`). This transposes a supplied section representative,
  without affineness, quasi-coherence, perfectness or an existence assertion for J.

This closes one upper hole and adds two strictly separate lower holes: a decomposition,
net one additional hole before subsequent proofs. The existing perfect-source RHom
quasi-coherence declaration is reused without modification. No sorry is placed inside a
definition, anonymous proof, or private helper. The supplied existential objects are consumed
inside a theorem proof, with no new data-valued definition choosing an arbitrary witness.

All three modules compiled together against the compiled library with `lcompile.py --all`.
The final proof is also compiled after restoration of the signature.
The delivery dry run checks compilation, signatures, nodes and the axiom probe.

## No longer needed

Removed every original proof-only import from the assigned module, with these dispositions:

- `Sheaf.Algebra.Homology.RhomGlobalSections` (node `lem-pur-rhom-global-sections`):
  no separate global-section/cohomology identification is used by the assembled proof;
  the new transposition interface works directly with morphisms from the restricted unit.
- `Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat`
  (node `lem-pc-bounded-above-flat-kflat`): retained as a proof dependency of the new
  section-representation module, not directly needed in the assembled proof.
- `Sheaf.AlgebraicGeometry.AffinePerfectOpenRepresentCohomology`
  (node `lem-sc-affine-perfect-open-represent-cohomology`): retained below the new
  section-representation module.
- `Sheaf.AlgebraicGeometry.PerfectDerivedTensorHom`
  (node `lem-sc-affine-perfect-derived-tensor-hom`): its perfect-input specialization
  is replaced by the general canonical adjunction in the transposition argument.
- `Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherent`
  (node `lem-sc-rhom-supported-qcoherent`): replaced by the already proved
  `RHomSupportedQuasiCoherentPerfectPart`; neither the pseudo-coherent nor support clause
  is used here.
- `Sheaf.Paper.DerivedInternalHomRestrictOpen`
  (node `lem-sc-derived-internal-hom-restrict-open`): retained below transposition.

The assigned node's direct dependencies are now the perfect-source RHom part and the two
new nodes. No target-closure module pruning is claimed: removed direct imports can still be
reached transitively or from other targets. `sk-thm-picard-duality.realized` has empty statement
and step lists, so this decomposition bypasses no recorded UNIT realization.

## Where the brief, the DAG or earlier work was wrong

The previous attempt had three Lean modules but no nodes or report. Its final module compiled
before repair, but had changed the original signature's `letI` binders to `let`. Restoring
the original signature in the direct proof caused an elaboration timeout at the transposition
application. A proved private helper with local abbreviated instances fixes this while
preserving the public signature exactly; this is not a new hole or a moved sorry. The two new intermediate interfaces are necessary glue absent from the stated
plan: the cohomology-representation theorem is formulated on Spec(A) and a fixed finite family,
whereas the assigned theorem has arbitrary affine X and compact U; the existing restriction
of RHom gives an object isomorphism, without the evaluation/transposition compatibility
needed for the exact beta/gamma equation. The new statements isolate those two parts.

Read Stacks `perfect.tex`, `equation-comparison`,
`proposition-represent-cohomology-class-on-open` and `lemma-lift-map`, and `cohomology.tex`,
`equation-internal-hom`, `lemma-internal-hom`, `lemma-restriction-RHom-to-U` and
`lemma-bounded-flat-K-flat`. The earlier sandbox includes these source texts. The section
representative is the actual associated-sheaf Koszul tail described there. After transport
back along the affine isomorphism, its augmentation remains a chain map to O_X[0].

Edge checks: U may be empty (empty Koszul family, zero tail; all restrictions zero);
U may be X (augmentation represents the unit); E may be zero or unbounded, as permitted
by the filtered-colimit theorem; A or P may be zero in the transposition statement.
Transposition needs K-flatness, without imposing finite freeness on arbitrary P or J.
The equations use the right tensor order P tensor J, the chain right unitor, and e_A.
No statement is disputed. LeanSearch returned Internal Server Error and is recorded as
unavailable, not as evidence of absence; LeanFinder, Loogle and local searches found no
exact ready-made interface.

## New nodes

`lem-sc-affine-koszul-section-roof`, in
`dag/nodes/sec-picard-framework/lem-sc-affine-koszul-section-roof.json`, records the section
representation part of Tags 08DC/08DD/08EH and K-flatness from Tag 06YD. Its Lean statement
is `affine_koszul_section_roof` in `Sheaf.AlgebraicGeometry.AffineKoszulSectionRoof`.
The proof uses the existing Koszul open system, cohomology-representation theorem and
bounded-above flat K-flatness criterion.

`lem-sc-tensor-roof-transposition`, in
`dag/nodes/sec-picard-framework/lem-sc-tensor-roof-transposition.json`, records tensor-Hom
transposition and its restriction identity from Tags 08DJ/08DL/08EH. Its Lean statement
is `tensor_roof_transposition` in `Sheaf.AlgebraicGeometry.TensorRoofTransposition`.
Its source inputs are the canonical adjunction on representatives, open restriction of
K-flat models, and restriction of Hom complexes and RHom. No affine or perfect-object
existence theorem is contained in its conclusion.

Both nodes include the full signature, source, proof steps and dependencies, actual logged
Mathlib searches, and ancestry through the assigned tensor-roof node to finite duality.
No change record is needed because every existing signature and public import is unchanged.

## Second reading by D3

1. Compared all three delivered modules with the read-only repository. The two
   intermediate modules are new. The existing public theorem signature is byte for
   byte identical, including its `letI` binders; its docstring and public imports
   are unchanged. No existing definition or statement changes. Verdict: pass.
2. Compiled all three modules in import order with `lcompile.py --all`: 6.3 s,
   20.9 s and 35.3 s, with no errors or warnings. The assigned theorem and its
   private helper contain no sorry. Exactly the two reported public intermediate
   theorems have `:= by sorry`; there are no definitions or forbidden declarations.
   Checked the inverse cancellation: `asIso (R.map β)` has exactly the required
   hom, and `Equiv.apply_symm_apply` converts the transposition equation to the
   equation for α. Axiom probes are restricted to the three permitted axioms and
   `sorryAx` from the still-open dependencies. Verdict: pass as a decomposition,
   not as a proof free of sorryAx.
3. Read the split signatures, docstring proofs, nodes, imported interfaces, and
   source passages for Tags 08DC/08DD, 08DJ/08DL and 08EH. Section representation
   is independent of a perfect source or tensor model; transposition starts with
   an already supplied representative and proves no existence of a perfect J.
   Neither restates the assigned theorem. Empty U permits J=0; U=X permits the
   unit representative; zero E, A or P produces zero morphisms. Arbitrary
   unbounded E is allowed by the cohomology representation result. K-flatness
   computes the tensor on the supplied P and J, with symmetry fixing the order
   P tensor J and the right unitor matching β. No arbitrary existential witness
   is turned into a data-valued definition. Independently searched LeanFinder
   for "derived tensor Hom evaluation naturality restriction open immersion",
   Loogle for `CategoryTheory.Limits.Types.jointly_surjective_of_isColimit`,
   Mathlib grep for `Koszul|koszul|tensorHom|TensorHom`, and the local affine,
   Koszul, tensor-Hom and restriction modules. Loogle supplies joint surjectivity
   for a future proof, but none supplies either complete missing interface.
   Closing either split requires the affine transport or representative-level
   restriction compatibility, beyond a short repair. Verdict: pass.
4. The proof follows RHom quasi-coherence, section representation, transposition
   and cancellation, keeping existence separate from the categorical identity.
   The public imports are precisely the existing statement imports; new proof
   imports are plain imports. The intermediate modules retain plain imports for
   their documented proof plans. Every old direct proof dependency is accounted
   for under "No longer needed"; no closure pruning is claimed. Read the unit
   record: its realized statement and step lists are empty, so no recorded unit
   step is bypassed. Verdict: pass.
5. Checked all three node signatures against their Lean theorem signatures and
   each proof_deps against the union of its proof steps' uses. The assigned node
   changes only proof, proof_deps and proof_origin; its four steps match the
   actual helper proof. Both new nodes have sources, ancestry, searches, creation
   records and Lean records. Verdict: pass.

Second reading changed only this report, adding the independent checks and
explicit decomposition verdict. No Lean proof, statement, definition or node
needed repair. The delivery closes one original hole and adds two lower holes;
its net holes closed minus holes added is therefore minus one, with no target-closure module pruning.
