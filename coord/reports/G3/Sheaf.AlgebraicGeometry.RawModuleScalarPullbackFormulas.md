## What changed

Restore `Sheaf.AlgebraicGeometry.RawModuleScalarPullbackFormulas` from its quarantine archive.
Remove the private upstream module-formula import that collides with the Sheaf coefficient
factor declarations. A proved private categorical lemma factors `rawTriangleMap` after source
precomposition; its specialization proves the module identity. Retain the proved abelian
component and combine the two identities by conjunction. Use Mathlib's `Over.w_assoc` for the
same triangle equalities. The original universes, binders, class type, conclusions, docstring,
option and public imports are preserved; only proof terms in the triangle arguments differ.

In `Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientFactors`, name the existing
`higherDirectImageRawOverComplex` endpoints in the module factor's type. Its body is
byte-for-byte unchanged, and its endpoints are definitionally equal to the old explicit single
complexes. This reduced the assigned module's compile from 58.2 to 44.3 seconds. The abelian
factor and every adopted upstream file are unchanged. Update the two existing nodes to match
the proof route and endpoint presentation.

Single-file checks passed for both delivered files and all six unchanged consumers. The
assigned module took 45.6 seconds in this set; the slowest consumer took 50.3 seconds. No
adaptation was needed. One pre-existing 101-character coefficient-module import line is
wrapped without changing its visibility or module.

Change records:
`coord/changes/G3-restore-raw-module-scalar-pullback-formulas.md` and
`coord/changes/G3-raw-module-coefficient-factor-endpoints.md`.

## Proved and sorry left

This assigned quarantine repair began with zero holes. Closed: none (0). Added: none (0).
Remaining in both delivered modules: none (0).
`AlgebraicGeometry.Etale.rawModuleScalar_pullback_formulas`
(`lem-sbc-raw-scalar-pullback-formulas`) has a complete proof.
The new private helper `rawTriangleMap_factorization` is proved by categorical associativity.
No new public declaration, node, split, axiom or hollow definition is introduced.

## No longer needed

Remove the private import
`WeilConjectures.AlgebraicGeometry.RawModuleScalarPullbackModuleFormula` and the proof edge
to `lem-sbc-raw-scalar-pullback-module-formula`: the module identity is calculated locally.
The upstream module and theorem themselves remain in the library unchanged. No global module
or node withdrawal is claimed. The abelian component remains necessary. Existing public
imports are preserved as the restored interface; the scalar coherence theorems they expose
are not used by this factorization.

## Where the brief, the DAG or earlier work was wrong

The source is quarantined at the path in `coord/rework.tsv`, not withdrawn. Its zero hole
count is reported honestly; this delivery repairs its duplicate-declaration import failure.
The archived file reproduced the error on `abelianCoefficientFactor` before editing.

Broad simplification expanded large derived comparisons and exceeded 60 seconds. Keeping the
maps folded and sharing the named coefficient-complex endpoints avoids that cost without
changing any constructed map. The final proof uses no scalar-comparison coherence or relation
between the independent module and abelian classes. Degree zero, zero classes, the zero ring,
and identity arrows require no extra hypothesis: this is associativity of the same maps.

LeanFinder, Loogle and Mathlib grep searches found the associativity API; a local Mathlib
search identified `Over.w_assoc`. The source-library boundary is respected throughout. The
unit `sk-lem-failure-field` has no realized step or statement attached to this node, and its
route is unchanged. The coefficient factor's six tracked consumers are checked unchanged;
there are no consumers of the restored module itself. No forced adaptation is included.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
