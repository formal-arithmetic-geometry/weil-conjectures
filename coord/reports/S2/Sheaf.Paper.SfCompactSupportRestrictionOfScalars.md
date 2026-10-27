## What changed

Filled `AlgebraicGeometry.Scheme.sfRealizationRestriction_existsUnique` in
`Sheaf.Paper.SfCompactSupportRestrictionOfScalars`, following its existing
sectionwise proof from Stacks Tags 00YV and 03DA.

The private, proved lemma `sheafify_restrict_smul` compares sheafified scalar
actions through a semilinear map by lifting the scalar and the section on a
common covering sieve. The private theorem `realization_restrict_smul`
specializes that calculation to the realization functors. The private theorem
`lift_module_iso` lifts an underlying abelian-sheaf isomorphism after proving
linearity, reflects invertibility, and proves uniqueness by extensionality.
`realization_restrict_existsUnique` combines these with identity section maps. Its private abbreviation `moduleRealization` is precisely the
existing fixed-module-presheaf/sheafification construction. Proving this over an
abstract site avoids repeatedly normalizing the concrete pro-etale site during
kernel checking. Remote `lcompile.py` accepted the resulting file in 33.4 seconds;
profiling options were removed before delivery. The public proof specializes it
and supplies the coefficient
square by naturality of `toSheafify`.

No existing public signature, definition body, attribute, or import changed.
The finite-ring hypotheses are preserved. Local bijectivity and separatedness
also handle empty schemes, zero coefficient rings and identity ring maps;
no flatness or nontriviality assumption is introduced.

## Proved and sorry left

Closed one of the two original holes:
`AlgebraicGeometry.Scheme.sfRealizationRestriction_existsUnique`.

One original hole remains, unchanged:
`AlgebraicGeometry.Scheme.sfCompactSupportRestriction_comp`
(blueprint: `lem-sf-compact-support-restriction-of-scalars`).

Added zero holes and split off zero statements. All four private helper theorems
are fully proved; the private abbreviation constructs its data explicitly.
The composition theorem is not claimed as proved or decomposed by this delivery.

## No longer needed

None. No import, module, node, or proof dependency is pruned. The existing public
imports continue to supply the definitions and statements throughout the module.

## Where the brief, the DAG or earlier work was wrong

The current node `lem-sf-compact-support-restriction-of-scalars` records
`Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction` as its primary module.
Its current proof concerns the intrinsic ring-sheaf direct-image presentation,
whereas this item's compact-support candidate uses
`proEtaleConstantDerivedDirectImage`. The node's open-coherence dependency also
imports this item, so importing it here would create a cycle. Neither this node's
current proof nor its Lean attachment is changed: this delivery closes the
realization theorem using its existing sectionwise proof, and leaves the
composition theorem untouched. Searches through leanfinder, loogle, project grep,
and the source library found Mathlib's scalar restriction and sheafification API;
`PresheafOfModules.Sheafify.map_smul_eq` supplies the required local computation.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
