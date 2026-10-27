## What changed

In `Sheaf.CategoryTheory.ToposFiniteFreeCompactConstituents`, prove
`CategoryTheory.ToposFiniteFreeCompact.finiteFreeCompactConstituents` from the
already stated coordinate theorem. Move that coordinate statement and its
supporting definitions before their first use, preserving every public signature
and definition. Add private proved finite-matrix, reflection, and transpose helpers.
The matrix inverse is the finite sum of projection/inclusion composites, including
an empty basis. Scalar restriction reflects derived isomorphisms through homology;
no faithfulness of derived scalar restriction is assumed. The prescribed compact
comparison transpose follows from the geometric and scalar mate equations and
naturality of the restriction/direct-image comparison.

A private proof import provides additivity of derived direct image. Update the
existing node's proof narrative to record the formal reduction. The unit route
is unchanged.

## Proved and sorry left

Closed one of the original seven holes:
`CategoryTheory.ToposFiniteFreeCompact.finiteFreeCompactConstituents`.
Added zero holes and split off zero statements. This is a proof from the existing
coordinate declaration, which remains an open dependency.

The following six declarations retain their original whole-proof `sorry`, all
attached to `lem-pur-topos-finite-free-compact-constituents`:

- `CategoryTheory.ToposFiniteFreeCompact.scalar_exact`
- `CategoryTheory.ToposFiniteFreeCompact.tensorPullbackInv_isIso`
- `CategoryTheory.ToposFiniteFreeCompact.restrictionOpen_isIso`
- `CategoryTheory.ToposFiniteFreeCompact.finiteFreeCompactCoordinates`
- `CategoryTheory.ToposFiniteFreeCompact.chi_comp`
- `CategoryTheory.ToposFiniteFreeCompact.beta_comp`

## No longer needed

None. No original import, dependency node, module, or approved tool use is removed.
The unresolved coordinate and composition assertions still need the original
proof dependencies. No declaration of the adopted source library changes.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction. The existing finite-coordinate theorem already
contains the matrix data needed for direct-image invertibility. The transpose
identities needed to combine the constituents are formal consequences of the
specified mate definitions, so no new scalar-normalization assumption is needed.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
