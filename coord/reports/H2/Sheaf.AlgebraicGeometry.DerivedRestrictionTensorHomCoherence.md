## What changed

The signature of `AlgebraicGeometry.Scheme.exists_derivedRestriction_tensorHom_coherence`
is unchanged. Its proof now obtains a natural tensor comparison, explicitly constructs the
Hom comparison by currying restricted evaluation, uses invertibility of that map, and proves
compatibility for every derived morphism from the naturality of the canonical tensor-Hom
families. A proved private helper `restriction_mate_equation` checks the cancellation
calculation over arbitrary monoidal categories before specializing to sheaves.
No comparison data is chosen from a mere unproved existence theorem in a definition.
The constructions of both comparison families occur locally in the theorem proof.

Two new modules make the reduction independently reviewable:

- `Sheaf.AlgebraicGeometry.DerivedRestrictionTensorNaturality` proves tensor naturality from
  `exists_derivedPullbackMonoidalModel`, the exact-functor localization factorization,
  uniqueness of left derived functors, and transport of monoidal structures.
- `Sheaf.AlgebraicGeometry.DerivedRestrictionEvaluationMateIsIso` states invertibility of
  the explicitly given evaluation mate for any natural tensor comparison. Its docstring
  supplies the extension-by-zero adjunction argument, including supported tensor objects,
  restriction detecting isomorphisms, and Yoneda.

The original node's proof and proof dependencies follow the new Lean argument. No existing
statement, definition, visibility, public import or target signature changes. No forced
adaptations are necessary. The unit's realized statement and steps are untouched.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.exists_derivedRestriction_tensorHom_coherence`
(`lem-sc-derived-restriction-tensor-hom-coherence`).

Also proved the new theorem
`AlgebraicGeometry.Scheme.exists_derivedRestriction_tensor_natural`
(`lem-sc-derived-restriction-tensor-naturality`) from existing named declarations.

One new hole remains:
`AlgebraicGeometry.Scheme.derivedRestriction_evaluationMate_isIso`
(`lem-sc-derived-restriction-evaluation-mate-is-iso`). Its whole proof is `by sorry`
in its own module. It asserts only invertibility of a fixed map, not existence of coherent
comparison families or the arbitrary-map evaluation equation. The main module contains no
sorry. This is a decomposition: one original hole closed, one lower hole added, net zero
holes at this layer. Dependencies of the already stated monoidal model remain open elsewhere.

## No longer needed

Removed all eight former proof-only imports from the item's module:

- `Sheaf.AlgebraicGeometry.DerivedTensorOpenRestrictionUniverses`
  (`lem-pc-derived-tensor-open-restriction-universes`).
- `Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison`
  (`lem-pc-kflat-derived-tensor-comparison`).
- `Sheaf.AlgebraicGeometry.OpenRestrictionKFlatModel`
  (`lem-pc-open-restriction-kflat-model`).
- `Sheaf.AlgebraicGeometry.OpenRestrictionTotalTensor`
  (`lem-pc-open-restriction-total-tensor`).
- `Sheaf.Algebra.Homology.HomComplexRestrictOpen`
  (`lem-sc-hom-complex-restrict-open`).
- `Sheaf.Algebra.Homology.KInjectiveRestrictOpen`
  (`lem-sc-derived-k-injective-restrict-open`).
- `Sheaf.Algebra.Homology.KInjectiveHomComplex`
  (`lem-pur-hom-kflat-into-kinjective`).
- `Sheaf.Paper.DerivedInternalHomRestrictOpen`
  (`lem-sc-derived-internal-hom-restrict-open`).

The tensor proof takes the existing derived-pullback monoidal model rather than constructing
new K-flat tensor comparisons. The Hom compatibility proof takes naturality rather than
transporting chain representatives through Hom-complex comparisons. The new invertibility
node's mathematical plan still uses K-flat computation of supported tensor objects; therefore
`lem-pc-kflat-derived-tensor-comparison` remains in that lower node's proof dependencies,
along with the existing K-flat resolution and derived tensor stalk vanishing nodes.
The canonical tensor-Hom definition and existence theorem remain necessary. These are removals
of direct proof dependencies, not claims that other target branches no longer reach the
listed modules; several remain indirectly imported elsewhere.

## Where the brief, the DAG or earlier work was wrong

The original dependencies supply separate object isomorphisms but do not expose their
component maps or derived naturality. Those signatures cannot directly prove simultaneous
coherence. A shorter categorical route constructs the Hom comparison as the evaluation mate,
so the arbitrary-map evaluation equation is formal once tensor naturality is known.

Care is needed with `X.Modules`: it has a separate category instance. The exact-functor
transport uses an explicitly typed functor between the shared `SheafOfModules` categories,
preserving the supplied localizations. No global family of scheme localizations is required.

The new invertibility statement was checked mathematically for arbitrary natural tensor
comparisons (including compositions with natural tensor automorphisms), the full open,
the empty open, zero factors, and unbounded complexes. Its adjunction proof uses only
bifunctorial tensor naturality; it does not silently impose a unit or associativity law.

The cited Stacks source files are absent from this remote checkout. Read the actual source
statements and proofs at https://stacks.math.columbia.edu/tag/079U,
https://stacks.math.columbia.edu/tag/08DJ, https://stacks.math.columbia.edu/tag/08DL,
https://stacks.math.columbia.edu/tag/08BS and https://stacks.math.columbia.edu/tag/00A7.
The detailed mate argument is marked agent-written, since Stacks leaves the restriction
compatibility implicit. LeanSearch was unavailable; actual searches are recorded in
`searches.jsonl`, with LeanFinder and Mathlib grep providing the other search kinds.

## New nodes

`lem-sc-derived-restriction-tensor-naturality` in
`dag/nodes/sec-picard-framework/lem-sc-derived-restriction-tensor-naturality.json`
records the proved bifunctorial tensor comparison and its transport proof. Its module is
`lean/Sheaf/AlgebraicGeometry/DerivedRestrictionTensorNaturality.lean`.

`lem-sc-derived-restriction-evaluation-mate-is-iso` in
`dag/nodes/sec-picard-framework/lem-sc-derived-restriction-evaluation-mate-is-iso.json`
records invertibility of the fixed evaluation mate, with the extension-by-zero proof plan.
Its module is `lean/Sheaf/AlgebraicGeometry/DerivedRestrictionEvaluationMateIsIso.lean`.

There are no change records because no existing interface is changed.

## Second reading by H2

1. Compared the delivered main module with the repository version. The target declaration
   signature is byte-for-byte unchanged; removed proof-only imports are recorded above, and the
   two added modules and DAG nodes are the only additional files.
2. Compiled all three sandbox modules with `lcompile.py`; they compile without errors. Searched
   declarations for forbidden `axiom`, `unsafe`, `opaque`, `implemented_by`, and `extern`; none
   occur. The only remaining `sorry` is the named split theorem
   `derivedRestriction_evaluationMate_isIso`.
3. Read both split-off statements, docstrings, and DAG records. The naturality theorem is proved,
   and the evaluation-mate theorem is a strictly lower invertibility claim with its own source,
   proof plan, and node; neither restates the original target. No duplicate declaration was found.
4. Checked the proof route against the unit record: it retains the canonical derived-pullback
   monoidal model, transports it to restriction, and uses the explicit mate. Removed imports are
   unused by the delivered proof; node proof dependencies match the declarations referenced.
5. Checked DAG and Lean metadata: module names, declarations, statements, proof steps, proof
   dependencies, and `proof_origin` agree. No statement or definition changed, and no forced
   adaptation is needed.

Changed during second reading: appended this review section only; no Lean proof or interface
changes were needed.
