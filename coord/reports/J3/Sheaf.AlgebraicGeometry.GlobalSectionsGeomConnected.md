## What changed

Proved `AlgebraicGeometry.Scheme.globalSectionsRingHom_bijective_iff_geometricallyConnected`
without changing its signature. The forward implication installs `GlobalSectionsBijective`,
uses its field-extension pullback instance, and proves connectedness of every pullback via
`GlobalSectionsBijective.connectedSpace` and Mathlib's field-extension criterion. The reverse
implication uses the existing `GlobalSectionsBijective.of_geometricallyConnected` instance.
The node now records these Lean realizations of its original argument. No unit statement or
unit step is bypassed (`sk-thm-picard-rr.realized` is empty).

The module compiles cleanly through `lcompile.py`, including after removing all five private
imports. The public import and all declaration signatures are unchanged. No definitions,
intermediate statements, or other modules were changed.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.globalSectionsRingHom_bijective_iff_geometricallyConnected`
(node `lem-pc-h0-geom-connected`). No sorry remains in the item. Added 0 holes; split off 0.

The reverse implication still depends transitively on the library's existing finiteness of
proper coherent cohomology. This delivery proves the item from existing declarations; it
makes no claim that the entire dependency closure is free of sorry.

## No longer needed

Removed the following five direct proof imports:

- `Sheaf.AlgebraicGeometry.BaseChangeConventions`: field base change here uses Mathlib's
  pullback and the source's existing preservation instance; the module-specific module
  pullback and geometric-fibre conventions are unused.
- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`: node
  `pqf-lem-coherent-ft-locnoeth` is unnecessary on this route; the source finiteness proof
  uses finite presentation of the finite locally free structure sheaf directly.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex`: no direct
  declaration used in this module; proper-cohomology finiteness remains a transitive input
  of the reused source proof, so node `lem-pc-coherent-hi` stays.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Scheme`: the idempotent criterion is already
  supplied and used by `GlobalSectionsBijective`; its node remains a transitive input.
- `WeilConjectures.Mathlib.RingTheory.Artinian.Ring`: the reduced algebra dimension-one
  lemma is already supplied and used by `GlobalSectionsBijective`; its node stays.

Retained the remaining original node dependencies because the reused source proofs carry
out those steps. These are removals of direct imports, not claims that each module leaves
all targets' transitive import closures.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The five-step argument already has source-library implementations
of the reverse implication, preservation under field extension, and connectedness. Reusing
those implementations closes the hole with no additional theorem. The DAG's explicit
coherence conversion was unnecessary for the source's finite-presentation route.

Edge cases: the forward proof uses the source's nonemptiness theorem, so an empty scheme
cannot satisfy the bijective hypothesis. The reverse proof retains both properness and
geometric reducedness; no connected-but-geometrically-disconnected example is admitted.

## Second reading by J3

1. Compared the delivered module with the repository version. The theorem statement and all
existing declaration signatures are byte-for-byte unchanged; only the proof and proof-only
imports differ.
2. Compiled the module with `lcompile.py`; it succeeds with no errors. The item contains no
`sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. A scratch `#print axioms`
shows only the allowed foundational axioms plus transitive `sorryAx` from still-open upstream
proofs.
3. Checked the proof route against the source and the existing `GlobalSectionsBijective`
declarations. No new statement was split off, and no declaration duplicates Mathlib or the
upstream library. The theorem proved is exactly the unchanged target statement.
4. Checked pruning and imports. The five proof-only imports removed are unused by compilation;
the public import remains necessary. The unit route is retained through the existing
`GlobalSectionsBijective` declarations, and the node records the revised proof route and
dependency pruning.
5. Checked the node and report consistency: the Lean declaration, proof origin, proof steps,
and `proof_deps` agree with the delivered proof, and no unit statement is bypassed.

Changed after this reading: only this second-reading record was added to `report.md`; no Lean
code or theorem statement required repair.
