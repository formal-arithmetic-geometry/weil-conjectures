## What changed

Retired `Sheaf.AlgebraicGeometry.Modules.ExteriorTensorLiftHomExt` in favor of
`WeilConjectures.AlgebraicGeometry.Modules.ExteriorTensorLiftHomExt`, as requested
by the 2026-10-20 hand-off. The retired file is absent from the sandbox and listed
in deleted.txt. Its DAG node now points to the exact official theorem signature.

The official theorem uses `exteriorPower` and `wedge`. Added the proved
`ExteriorSheafPowerComparison` module: identity maps on sectionwise exterior powers
form a presheaf isomorphism by uniqueness of the restriction extension; sheafification
gives `exteriorSheafPowerIso`. Naturality of the adjunction unit proves its inverse
wedge formula. Tensoring these isomorphisms transfers the official extensionality
theorem to the older construction under `exteriorSheafTensor_lift_hom_ext`.

Adapted DeterminantShortExact, DeterminantWedgeQuotientFactor,
ExteriorTensorKernelRelations and ExteriorTensorQuotient to this compatibility API.
ExteriorSheafRankWedgeZero now proves the restriction formula locally instead of
importing a private helper from the retired module. Its needed FreeGenerator import
is explicit. All existing consumer signatures are preserved; no upstream file or
target statement changes. Updated the consumer proof records to match these calls.

Change record: coord/changes/retire-exterior-tensor-lift-hom-ext-p7-20261020.md.

## Proved and sorry left

The retired item had zero sorry before this session. Closed zero holes, added zero
holes, split off zero holes. No sorry remains in the retired item or the delivery.
The compatibility construction and both public theorems are proved:
`AlgebraicGeometry.Scheme.Modules.exteriorSheafPowerIso`,
`AlgebraicGeometry.Scheme.Modules.exteriorSheafPowerIso_inv_wedge`, and
`AlgebraicGeometry.Scheme.Modules.exteriorSheafTensor_lift_hom_ext`.
All five adapted consumer proofs are retained, including their private helpers.
All six delivered Lean modules compiled cleanly in import order with lcompile.py:
comparison 24.3 s, rank vanishing 12.2 s, determinant short exact 3.7 s, kernel
relations 3.6 s, exterior quotient 32.0 s, quotient factorization 3.2 s.
This delivery is a retirement and API adaptation, not a new hole-closure claim.

## No longer needed

Pruned module `Sheaf.AlgebraicGeometry.Modules.ExteriorTensorLiftHomExt` and its
imports in all five direct consumers. No remaining source import names that module.
The four extensionality consumers use the official theorem through the comparison;
none repeats the old local-lift/local-generation proof. ExteriorSheafRankWedgeZero
no longer needs the extensionality node at all; its DAG edge is removed. The retired
node remains in the DAG and points to the official twin. No other mathematical
proof dependency, module, or unit step is pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier packet was an unchanged copy of an already proved zero-hole module and
was refused with “nothing is proved.” The current explicit RETIRE assignment fixes
that stale task: the work is the migration, not another proof of its theorem.

The constructions differ in their restriction-map implementation, so replacing only
imports is insufficient. The comparison uses the proved universal property and is a
real construction, not an assumed equality. A direct dependent rewrite expanded too
much of sheafification; the transport uses an explicit comparison isomorphism instead.
All five consumers were unclaimed when read; no held consumer or source declaration
is changed. The unit's mathematical route is preserved.

## New nodes

`lem-sc-exterior-sheaf-power-comparison` records the constructed comparison, inverse
wedge formula and transport of the official extensionality theorem. Every part is
proved. The two presheaves have identical objects and restriction formulas, so identity
components give the comparison even in degree zero, on empty opens, on the empty
scheme and over zero rings. The epi hypothesis is retained exactly. Searches in
LeanSearch, LeanFinder and the sources found the generic isomorphism/sheafification
tools but no comparison of these two project-specific implementations.

## Second reading by P7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
