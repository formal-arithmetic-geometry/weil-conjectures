## What changed

Proved `CategoryTheory.ringed_signed_bidual_localization` in
`Sheaf.Algebra.Homology.RingedSignedBidualLocalization`, preserving its statement.
The private construction works for any target complex: localized signed evaluation
maps into the actual Hom product, commutes with the Hom differential, and is natural.
Specializing to the coefficient complex gives the zero components and uniqueness.
The derived equation uses the two existing K-flat resolutions, normalized uncurrying,
the stipulated signed symmetry, and naturality of the fixed localization factorization.
The augmentation hypotheses package the two comparison morphisms as isomorphisms.

Added a private proof import of
`WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso` to reuse its proved
presheaf curry and uncurry constructions at independent universes. Added the direct
proof import `WeilConjectures.Algebra.Homology.HomComplexComponents` for the
product and differential projection API (node `lem-sc-hom-complex-projections`). All new helpers
are private and proved; there are no new public declarations or definition repairs.
Updated the existing node's proof and proof dependencies to describe this argument.
The final file compiled without diagnostics in 51.8 seconds through `lcompile.py`.
The preflight-requested record of private section commands is
`coord/changes/ringed-signed-bidual-private-proof.md`; no public signature changes.

## Proved and sorry left

Closed the one original hole in `CategoryTheory.ringed_signed_bidual_localization`
(node `lem-sfb-ringed-signed-bidual-localization`). Added zero holes. There are no
remaining `sorry` declarations in this delivery and no split-off statements.

## No longer needed

Removed the private import
`WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap` and the proof dependency
`lem-pur-rhom-well-defined`: naturality of the inverse `Localization.fac` comparison
provides the required compatibility directly. Removed its obsolete top-level
`tool_uses` entry. The adopted source module and its existing declarations remain
intact; this is no claim that its other consumers or dependencies are unnecessary.
Removed redundant private imports of
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Sheaf.Paper.CoefficientHomRepresentativeEvaluation`, and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: their needed interfaces
are already publicly available through the retained imports. These nodes remain needed.
No modules are withdrawn. The unit's two-resolution and normalized symmetry route
is retained. No other declared proof dependencies are pruned.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The original plan's quasi-isomorphism-invariance
step is stronger than needed. The derived comparison holds as an equality of
morphisms before imposing either augmentation hypothesis; those hypotheses are
needed only to obtain the specified isomorphisms. For the chain condition, working
with an arbitrary target complex lets the two target-differential terms cancel and
avoids a case split on the coefficient degree.

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
