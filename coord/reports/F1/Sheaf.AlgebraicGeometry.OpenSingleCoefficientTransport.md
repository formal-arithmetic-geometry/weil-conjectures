## What changed

Restored `Sheaf.AlgebraicGeometry.OpenSingleCoefficientTransport` from its assigned
quarantine archive. Replaced its retired proof-only
`Sheaf.AlgebraicGeometry.IsomorphismPullbackCounit` import with the adopted
`WeilConjectures.AlgebraicGeometry.IsomorphismPullbackCounit` and removed the redundant
local irreducibility attribute on `derivedPullback`, now irreducible upstream.

The original full proof then exceeded the normal file limit. Profiling identified repeated
checking of the nested counit choice. The private calculations now reuse the existing
`SingleComplexBaseChange.counit` definition for exactly that selected counit, with a
fixed canonical tensor-additivity instance in the explicit sheaf-module categories.
This removes the generic private additivity parameter and its two local introductions.
The open comparison and its universal-property factorization are named explicitly.
Apply that factorization before normalizing the underived comparison; subsequent
calculations keep the fixed counit abstract. Proved private lemmas lift single-complex
naturality in general abelian categories and paste the final coefficient diagram in an
abstract category, avoiding repeated checking of the concrete comparison terms. Scoped `cleanup.letToHave false`
retains local term sharing. No source-library module,
public definition, target meaning, file limit, or kernel check is changed.

Preserved the public theorem `AlgebraicGeometry.exists_openSingle_coefficient_transport`,
its public imports, all original docstrings, the coefficient construction, and the unit
route. The node retains its attachment and dependencies, and records this restoration.
Change record: `coord/changes/F1-open-single-coefficient-transport-restore.md`.

LeanFinder, Loogle, and the required `msearch.py` grep were run before editing.
Their hits supply ordinary pullback/single-complex constituents, not this pinned derived
coefficient equation. Searches of the current source library confirm that the existing
composition/counit route remains appropriate.

Validation: the complete candidate, including the required axiom probe, compiles in
47.3 seconds under the normal 60-second limit. The probe reports `SHEAF-PROBED 4`
and no direct holes or disallowed axioms. The only warning is in the appended tool
probe, not in the restored module. The public declaration signature was compared
with the archive and is identical; import-cycle checks pass. The original archived
attribute failure was reproduced independently. The new private instance was checked
against both module-category and explicit sheaf-module usages.

## Proved and sorry left

This is a restoration/compatibility repair of an archive with zero holes. The theorem
`AlgebraicGeometry.exists_openSingle_coefficient_transport` (node
`lem-pc-open-single-coefficient-transport`) and every private helper retain complete
proofs. Zero existing holes, zero holes closed, zero holes added, zero split off, and zero
`sorry` left in the delivery.

## No longer needed

No DAG node or mathematical dependency is pruned. The retired proof-only Sheaf
isomorphism-counit import is replaced by its existing adopted source module, preserving
the dependency on `lem-pc-isomorphism-pullback-counit`. Removed the proof-only
`WeilConjectures.AlgebraicGeometry.PinnedPullbackCounitShifts` import, since its counit
abbreviation is replaced by the already imported source counit definition. No shift
result is used. All three public imports remain
necessary for the theorem's signature. The archived parent
`Sheaf.AlgebraicGeometry.StandardSingleBaseChangeTopRestrictionAux` still needs this
node, despite there being no current live importers. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The module was reverted into quarantine during the 2026-10-20 cluster restoration. Its
archived proof had zero holes; this assignment repairs and restores that proof rather
than closing a new hole. The retired import and obsolete attribute require compatibility
changes. The complete archive also exceeded the file limit; naming the existing fixed
counit and using a single explicit sheaf-module additivity instance repairs the repeated
choice/typeclass checking. The mathematical statement and planned argument remain
valid, including zero modules, empty opens, and empty schemes.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
