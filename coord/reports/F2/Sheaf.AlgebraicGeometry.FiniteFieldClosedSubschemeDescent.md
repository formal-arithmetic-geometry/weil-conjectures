## What changed

Retained and reviewed the complete proof draft of
`WeilConjectures.FiniteFieldDatum.exists_closed_subscheme_finiteField_descent`
in `Sheaf.AlgebraicGeometry.FiniteFieldClosedSubschemeDescent`, preserving its signature.
The construction uses the directed system of finitely generated base-field subalgebras
of the closure. Its explicit ring colimit and the pullback universal property construct
the ambient scheme limit. The existing finite-presentation descent theorem descends the
closed immersion directly over this limit; the existing eventual-closed-immersion theorem
makes its stage model closed. This avoids descending the object and its embedding separately.

Each coefficient subalgebra is integral and finite-dimensional, hence a finite field.
Its finrank gives the positive extension degree. The unique-subfield theorem identifies it
with the prescribed extensionSubfield, compatibly with the base embedding and inclusion
into the closure. Transporting the closed stage model gives the actual subscheme,
isomorphism over Spec k, and required embedding equation. Finally the geometric field
Frobenius power fixes that subfield. The descended pullback square lifts this coefficient
automorphism and its inverse; pullback uniqueness proves their inverse equations and the
embedding's Frobenius equivariance.

All added constructions and supporting lemmas are private and have complete proof terms.
The stage instances are local, and the transparency option is scoped to individual
declarations. Removed the unused `open Opposite`. The DAG proof and proof dependencies
now describe this route. No public definition or statement changed; the interface and
reader-risk checks both report no changes. No consumer adaptation or change record is
needed. The final module compiles without warnings in 23.5 seconds through lcompile.py.
The resumed required dry run passed compilation, its axiom probe, and the full preflight
(commit `aa6ca5db07`; review class CODEX because the DAG node is updated).

## Proved and sorry left

The sole original hole,
`WeilConjectures.FiniteFieldDatum.exists_closed_subscheme_finiteField_descent`
(node `lem-zl-bertini-finite-field-descent`), is replaced by complete proof text.
The sandbox has zero holes and adds zero holes: one original hole closed, zero added.
The complete proof compiles. The delivery tool verifies every declaration with its
axiom probe; the initial probe passed.
No statements were split off, and no new modules or nodes were added.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.LimitAffineTransition` and dependency
`lem-weil-pbc-limit-affine-transition`. An explicit cone obtained from the ring colimit,
Spec, and connected pullback limits supplies the limit used here; no arbitrary affine
inverse-limit existence or open-restriction theorem is needed. Removed its obsolete
entry from the node's approved tool list.

Removed the redundant explicit import `Sheaf.FieldTheory.UniqueSubfieldOfClosure`;
its theorem is still used, already available through the public finite-field datum
imports. The corresponding node `lem-weil-unique-subfield-of-closure` remains a dependency.
Removed the proof import `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`;
the Mathlib pullback API already constructs every comparison and projection equation
needed here. The base-change convention node remains: its scheme constructions are
used directly. The existing AffineTransitionLimit module remains imported for the two
finite-stage descent theorems. Also removed the redundant draft imports
`Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic`,
`Mathlib.FieldTheory.IntermediateField.Algebraic`, and
`Mathlib.CategoryTheory.Filtered.Connected`: each is already publicly imported through
the retained imports.

The morphism clause of `thm-pd-spreading-out` is unnecessary, as is the separate
finite-presentation argument for the descended inclusion. The object clause and eventual
closed-immersion result still are used; their nodes and module must remain. Every other
original proof-dependency node still supplies a definition or finiteness property used
by the proof, often through Mathlib instances.

## Where the brief, the DAG or earlier work was wrong

The previous session could not obtain a response from the compile service. In this
session the service returned successfully: the retained proof passed compilation
and the axiom probe. The initial dry run then requested a change record for its
file-level `open` and transparency option. Removed the unused `open Opposite`, scoped
the option to individual declarations, and made both private instances local. The
interface checker now reports no changes and no downstream reader risks. The corrected
module compiles cleanly in 23.5 seconds. The theorem's signature is unchanged, confirmed
by the delivery declaration parser and a direct comparison with the current source.

The current module, DAG dependencies and source paragraph were reread. Only the DAG
fields `proof`, `proof_deps`, `proof_origin`, and the obsolete top-level tool approval
are changed. No new module, new node or definition repair is needed.

The original DAG's route is valid but longer: it descended the source and morphism
separately. Applying finite-presentation descent directly to the closed immersion over
the ambient limit removes that detour. This stays within the blueprint's final
finite-coefficient descent paragraph and preserves scheme structure, including nilpotents.
The argument also covers the empty closed subscheme and nonseparated finite-type models;
local Noetherianity supplies the required quasi-separatedness without separatedness.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
