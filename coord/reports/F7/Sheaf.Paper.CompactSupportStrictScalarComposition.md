## What changed

Proved `WeilConjectures.PurStrictScalar.compositionOpen` from ordinary
module-sheaf balancing and exact localization. The new
`ordinaryBaseOpenTensor_composition` is proved using the existing ordinary
coefficient-composition and normalized conjugate-cocycle helpers of
`Sheaf.SecSmoothPurity.ProEtaleOpenScalarCocycle`. Its ordinary-ring helper has
no finiteness or torsion hypothesis, so it applies to the integral rings here.
Mathlib's iterated-mate identity gives the exact normalization of the open maps;
`leftAdjointCompIso` identifies the specified coefficient associators.

Natural-transformation extensionality assembles the equation on ordinary towers.
The existing proved `localize_scalar_square` helper of
`ConstantCompletedScalarAssociativity` passes the equation through exact
localization, with the specified associators. `openTensor_ordinary` identifies
the localized maps with the original strict scalar mates. No equality on a
derived diagram is inferred solely from its evaluations.

The new ordinary module uses `import all` to access the proved localization
helper of `ConstantCompletedScalarAssociativity`; the item retains its normal
proof import of that module. The item imports the new module with `import all`
to use its proved private helpers. Eight generic, proved private helpers were
moved from the large item. The localization calculation and arithmetic-limit
calculation are also packaged there, with the ordinary associators and index
equality as explicit arguments. The item applies them to its existing maps.
A proved ordinary-tower normalization avoids repeatedly unfolding the double
mate. Local irreducibility attributes protect large adjunction and pullback
terms while checking these proofs. All existing public signatures, definitions,
attributes and public imports are unchanged.

Validation: `lcompile.py --all` completed with exit code 0 for both delivered
modules, with the 60-second limit enforced for each file. No profiling options
remain. The delivery compile additionally required the unused private arithmetic
positivity binder to be named `_hh`; this preserves its type and calling convention.

## Proved and sorry left

Closed one of the four original holes:
`WeilConjectures.PurStrictScalar.compositionOpen`.
The new public theorem
`WeilConjectures.PurStrictScalar.ordinaryBaseOpenTensor_composition`
and every private helper have complete proofs. No holes are added or split off.

Three original holes remain unchanged, all attached to
`lem-pur-compact-support-strict-scalar-composition`:

- `WeilConjectures.PurStrictScalar.compositionProper`;
- `WeilConjectures.PurStrictScalar.compactSupportStrictScalarComposition`;
- `WeilConjectures.PurStrictScalar.compactSupportStrictScalarIdentity`.

The delivered Lean files contain exactly these three `sorry` bodies. Each is
an existing named theorem with its original source and complete proof in words.

## No longer needed

No existing import, node or module is withdrawn. The open-factor proof needs
no additional K-flat construction: scalar and open extension are exact and the
existing whole-diagram localization helper applies. The other clauses retain
their original plans and dependencies, which remain needed.

## Where the brief, the DAG or earlier work was wrong

The ordinary coefficient-cocycle helper already supplies the right comparison
calculation, although the public derived theorem in its module is stated for
finite torsion coefficient rings. Reusing its proved ordinary and generic
helpers closes the integral open square without a new postponed lemma.
Checked zero modules, empty opens and identity embeddings: the mate and
restriction identities impose no nonzero or nonempty assumption. Localization
works on whole unbounded strict diagrams, without a finite-Tor restriction.
No statement correction was needed. The historical quarantine row was read;
the current item source exists, and its attachment and declarations are retained.

## New nodes

`lem-pur-ordinary-open-scalar-composition`, in
`dag/nodes/sec-smooth-purity/lem-pur-ordinary-open-scalar-composition.json`,
records the proved ordinary Step 4, before towers and derived localization.
Its statement uses the existing coefficient and open-extension constructions;
its proof records the right-square cocycle and precise conjugate normalizations.
Source: Stacks 0E8I and 07A6, the original auxiliary Step 4, and the existing
proved coefficient-cocycle calculation. LeanSearch, LeanFinder, Loogle and local
source searches found generic tensor and mate laws; source inspection located
the reusable ordinary and generic helpers. The dependency graph has no path
from those reused nodes back to this item.

The item node records the ordinary-tower assembly and exact-localization route.
No other existing module or node is changed; no change record is needed.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
