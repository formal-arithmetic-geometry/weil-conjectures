## What changed

The item theorem `AlgebraicGeometry.Etale.ordinaryAffineCounit_tensor_normalization` now cancels the specified invertible compact-support projection, uses the structural projection/reassociation comparison, and applies the actual ordered tower counit tensor square. Its signature is unchanged. The ordered affine-line route of the blueprint unit is retained.

The five existing canonical map definitions were moved byte-identically to `Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorMaps`, publicly reexported by the item. This permits the structural comparison to mention the maps without an import cycle. See `coord/changes/ordinary-affine-counit-map-ownership.md`; no target meaning changes, and no existing consumer requires adaptation.

New categorical modules prove the trace-normalized coefficient-action calculation, the open counit square, transport of the projection along a right-adjoint comparison, pasting of two counit squares, and induction over ordered towers. The concrete one-step statements use the actual signed derived projections. The projective-line action and open counit identifications remain named holes; the abstract normalized action calculation is proved. The affine tensor actions and strengths are explicit constructions; the line and tower counit identities are proved by pasting.

The main theorem, line and tower squares and all categorical helpers compile through lcompile.py. The final delivery runs the independent preflight.

## Proved and sorry left

This delivery is a decomposition: one original hole is closed and three genuinely separate holes are added; net holes closed is minus two. No sorry remains inside the item theorem, and none occurs in a definition.

Closed: `AlgebraicGeometry.Etale.ordinaryAffineCounit_tensor_normalization`.

Remaining: `AlgebraicGeometry.Etale.ordinaryFiniteP1Counit_tensorAction` (node `lem-pur-ordinary-finite-p1-tensor-action`, module `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1TensorAction`), the coefficient square for the concrete normalized projective-line datum; `AlgebraicGeometry.Etale.derivedOpenCounit_tensorAction` (node `lem-pur-derived-open-counit-tensor-action`, module `Sheaf.AlgebraicGeometry.DerivedOpenCounitTensorAction`), identifying the exact/left-derived transported open counit square; and `AlgebraicGeometry.Etale.ordinaryAffine_projection_reassociation` (node `lem-pur-ordinary-affine-projection-reassociation`, module `Sheaf.AlgebraicGeometry.OrdinaryAffineProjectionReassociation`). It compares the canonical compact-support projection with the pasted proper/open tensor action and the explicit ordered source reassociation. Its statement contains neither projective-line adjunction data nor any counit, trace or normalization equation. It is the geometric coherence portion of the original proof, strictly independent of the counit portion; its full coordinate-induction proof is in its docstring and node. The proposed structural argument includes dimension zero, the empty scheme and the zero ring; these edge cases require only the canonical identity and zero-object equations, without a nonvanishing assumption.

The following new theorem bodies are complete (no sorry):

- `CategoryTheory.Adjunction.openCounit_tensorAction`.
- `CategoryTheory.counitTensor_tower`.
- `CategoryTheory.Adjunction.tensorProjection_ofNatIsoRight`.
- `CategoryTheory.normalizedTensorCounit_action`.
- `CategoryTheory.counitTensor_pasting`.
- `AlgebraicGeometry.Etale.ordinaryAffineLine_tensorCounit`.
- `AlgebraicGeometry.Etale.ordinaryAffineTower_tensorCounit`.

No axioms or arbitrary data choices were added. The three retained holes are a decomposition, not three proved results. All new constructions use specified functors, tensor constraints and existing canonical comparisons.

## No longer needed

No original public imports were removed: preserving their visibility also preserves the original public interface. No existing module is withdrawn. No source-library declaration, signature, attribute or import is changed.

The old proof plan's separate open-action associativity, composite-action associativity, recollement, signed-pullback construction and ringed-topos projection-composition routes are not used: the proof works directly with the canonical derived monoidal structure, the open projection transport, and pasted counit squares. Accordingly the item withdraws these obsolete tool approvals, preserving the order of all others: `lem-pur-open-left-projection-action`, `lem-pur-composite-left-projection-action`, `prop-weil-open-closed-recollement-adjunctions`, `lem-pur-exact-pullback-signed-comparison`, `lem-sf-ringed-derived-closed-symmetric-monoidal`, `lem-sfb-ringed-projection-tensor-composition`. Their corresponding modules need not be imported by this proof. This is local pruning only; no claim is made that another consumer does not need them.

The proper projection action, open tensor projection, finite projective-line datum, unbounded compact-support composition, canonical pullback composition, and ordered affine trace construction remain needed, directly or through the new statements. The blueprint unit and its ordered projective/open route remain intact.

## Where the brief, the DAG or earlier work was wrong

The categorical action and counit steps were described mathematically but the existing statements do not expose the actual derived right-adjoint transport or the coefficient-square pasting interface needed by these definitions. The abstract interfaces are now proved; the two concrete one-step counit squares remain stated with full proof descriptions. Their statements use the same cached actions and strengths as the tower proof, so they introduce no choice of isomorphism. The remaining structural comparison must account for the specific recursive descent, rather than silently identifying every reassociation by its endpoints. A direct proof of the open square typechecked in 98.7 seconds, beyond the per-file limit. Profiling found tactic execution in seconds followed by expensive kernel conversion of the derived monoidal-instance terms. A generic coefficient helper also exceeded the limit; it was not retained. The proper specialization similarly hit a reduction timeout before its concrete application. The proved generic calculations are retained as the precise next interfaces, while both concrete squares remain honest named holes. No false statement or weakened conclusion is used.

## New nodes

`def-pur-ordinary-affine-counit-tensor-maps` — Canonical descent, reassociation, counit and trace of the ordered affine tower. Module `Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorMaps`. Explicit definitions only; no holes.

`def-pur-ordinary-affine-tensor-actions` — Specified tensor actions and strengths on the ordered affine tower. Module `Sheaf.AlgebraicGeometry.OrdinaryAffineTensorActions`. Explicit definitions only; no holes.

`lem-pur-counit-tensor-pasting` — Pasting two coefficient counit squares. Module `Sheaf.CategoryTheory.CounitTensorPasting`. Proved; no holes.

`lem-pur-counit-tensor-tower` — Coefficient counit squares paste along an ordered tower. Module `Sheaf.CategoryTheory.CounitTensorTower`. Proved; no holes.

`lem-pur-derived-open-counit-tensor-action` — Tensor counit square for derived open extension. Module `Sheaf.AlgebraicGeometry.DerivedOpenCounitTensorAction`. One named theorem remains sorry; its complete categorical proof is recorded in the declaration docstring.

`lem-pur-normalized-tensor-counit-action` — A trace-normalized tensor counit respects the coefficient action. Module `Sheaf.CategoryTheory.NormalizedTensorCounitAction`. Proved; no holes.

`lem-pur-open-counit-tensor-action` — The inverse open projection respects the counit. Module `Sheaf.CategoryTheory.OpenCounitTensorAction`. Proved; no holes.

`lem-pur-ordinary-affine-line-tensor-counit` — Tensor counit square for one ordered affine line. Module `Sheaf.AlgebraicGeometry.OrdinaryAffineLineTensorCounit`. Proved; no holes.

`lem-pur-ordinary-affine-projection-reassociation` — Canonical projection comparison with the ordered affine tensor action. Module `Sheaf.AlgebraicGeometry.OrdinaryAffineProjectionReassociation`. The structural comparison remains sorry.

`lem-pur-ordinary-affine-tower-tensor-counit` — Tensor counit square for the ordered affine tower. Module `Sheaf.AlgebraicGeometry.OrdinaryAffineTowerTensorCounit`. Proved; no holes.

`lem-pur-ordinary-finite-p1-tensor-action` — Coefficient action of the normalized projective line counit. Module `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1TensorAction`. One named theorem remains sorry; its proof is recorded in its docstring.

`lem-pur-tensor-projection-right-transport` — Projection transport along a right adjoint comparison. Module `Sheaf.CategoryTheory.TensorProjectionRightTransport`. Proved; no holes.

Change record: `coord/changes/ordinary-affine-counit-map-ownership.md`.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
