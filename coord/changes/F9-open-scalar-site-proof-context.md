# AlgebraicGeometry.ProEtale.OpenScalarSite

## Reason

Complete all eight proofs using exact derived functor coherence and adjunction
mates. New private helpers use the same local transparency options as their
existing proved categorical APIs. A separate fully proved finite-coefficient
realization lemma records the constant-scalar coordinate comparison; its narrow
proof environment avoids conflicting coefficient instances in the main proof.
This is a proof-context change, not a change to an existing statement or object.

## Old

The original file environment, verbatim:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.OpenScalarSite
```

All existing public signatures, definition bodies, and public imports are retained.
The eight theorem proofs were `by sorry`.

## New

The same environment additionally has these file-local options:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
```

All new helpers in the item are private and proved or explicitly constructed.
The new public theorem is
`AlgebraicGeometry.ProEtale.OpenScalarFlatModel.finiteCoefficientRealization_flat`
in `Sheaf.Paper.OpenScalarFlatModelRealization`; its exact signature is in
`dag/nodes/sec-smooth-purity/lem-sp-finite-coefficient-realization-flat.json`.
It constructs the linear sheafification unit and proves its invertibility;
there is no arbitrary witness chosen from existence and no new hole.
New proof imports are private. Existing public statements, definitions, attributes
and public imports are unchanged. No other existing module is adapted.

## Users

A read-only traversal of every source import in both library roots found zero
current Lean importers of the item and zero users of the new module. This is not
used as a withdrawal justification: both existing node attachments are retained,
and the parents whose proofs are unfinished still need these statements.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.OpenScalarSiteCoherence | F9 | Complete proofs; same public interface |
| Sheaf.Paper.OpenScalarFlatModelRealization | F9, new | Proved realization lemma used privately by item |

## Status

landed 20261021T203504-L-3786821 2026-10-21 (merge of deliver/F9/Sheaf.Paper.OpenScalarSiteCoherence)
