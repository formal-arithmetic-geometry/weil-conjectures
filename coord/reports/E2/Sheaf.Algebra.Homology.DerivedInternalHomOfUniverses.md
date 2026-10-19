## What changed

Proved all three original theorems in
`Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses` without changing their
signatures, the derived internal Hom definition, or its public imports.
Naturality and two-out-of-three prove invariance; localization factorization
and comparison through the composite replacement prove the natural comparison;
transport along representative isomorphisms proves the object comparison.
Explicit Hom-bifunctor universes resolve the retained universe metavariable.

Added twelve fully proved universe companions of the existing specialized
invariance proof chain, each in a new module with its own node. Coefficients and
module elements live in `max u v r`, independently of the site universes.
The chain includes sectionwise quasi-isomorphism detection, degreewise cochains,
differential compatibility, homotopy and derived comparison naturality, exact
localized restriction, and its preservation of K-injectivity. The exact left
adjoint is constructed from the existing direct-sum presheaf and sheafification;
its adjunction and exactness are proved. It is not chosen from a mere existence
statement. Existing specialized declarations and modules are unchanged.

The existing `siteAbelianHasSheafify` and
`siteAbelianWEqualsLocallyBijective` instances, exposed by
`Sheaf.CategoryTheory.Sites.RGammaDerivedLimit`, provide slice-site
sheafification at the coefficient universe. No new sheafification instance is
introduced. New comparison dependencies are imported privately where only their
proofs are needed. See
`coord/changes/DerivedInternalHomCoefficientUniverse.md`.

## Proved and sorry left

Closed 3 of 3 original holes, all attached to `def-pur-derived-internal-hom`:

- `CategoryTheory.derivedInternalHomOfUniverses_inverts`
- `CategoryTheory.derivedInternalHomOfUniverses_comparison`
- `CategoryTheory.derivedInternalHomOfUniverses_obj_iso`

Added zero holes; split off zero unfinished obligations. Every declaration in
all thirteen delivered Lean files is proved or is a construction without
`sorry`. The twelve new public theorems are:

- `CategoryTheory.quasiIso_homComplex_mapOfUniverses`
- `CategoryTheory.quasiIso_of_sectionsOfUniverses`
- `CategoryTheory.homComplex_sections_quasiIsoOfUniverses`
- `CategoryTheory.homComplex_sections_derived_naturalityOfUniverses`
- `CategoryTheory.homComplex_sections_homotopy_naturalityOfUniverses`
- `CategoryTheory.homComplex_sections_canonical_comparisonOfUniverses`
- `CategoryTheory.homComplex_sections_cochainsOfUniverses`
- `CategoryTheory.homComplex_sections_cochains_commOfUniverses`
- `CategoryTheory.isKInjective_restrict_localizedOfUniverses`
- `CategoryTheory.localizedModule_restriction_quasiIsoOfUniverses`
- `CategoryTheory.localized_restriction_adjunctionOfUniverses`
- `CategoryTheory.localized_restriction_extension_existsOfUniverses`

Verification: `lcompile.py --all` passes for all thirteen modules in dependency
order, with no warnings. The retained uncached run took 1.8–50.7 seconds per
module; the continuation run verified all current files against the remote
compile cache. On resuming at 2026-10-19 06:18, compared the retained item
with current sources: the only Lean changes to the existing module are its
three proofs and private proof imports. A fresh `lcompile.py --all` run passed
all thirteen modules through the remote compile cache without diagnostics.
All thirteen node records have valid dependency IDs, and each `proof_deps`
equals the union of its proof-step uses. No target type or existing definition changes. This reports
local holes closed, not a claim that every pre-existing dependency of the
library is already free of `sorry`.

## No longer needed

Removed the assigned module's direct proof imports
`Sheaf.Algebra.Homology.HomComplex` and
`Sheaf.Algebra.Homology.QuasiIsoHomComplexMap`. Hom-complex definitions remain
available through the retained public import of `DerivedInternalHom` and are
used. The specialized invariance theorem is replaced in the new proofs by
`QuasiIsoHomComplexMapOfUniverses`; the original specialized chain remains used
by the existing `DerivedInternalHom` module and is not globally pruned.

No module is withdrawn or claimed to leave the target import closure. The
original node's direct proof dependency `lem-pur-rhom-well-defined` becomes
`lem-pur-rhom-well-defined-universes`. Its other direct proof dependencies remain.
All twelve new modules are used by the completed chain. No blueprint unit step
is bypassed; the unit `sk-def-sf-operations` has no numbered proof steps.

## Where the brief, the DAG or earlier work was wrong

The stated invariance declaration exists and is proved, but its coefficient
universe is `max u v`; it cannot be applied to this item's complexes in
`max c v r`. The same restriction occurs throughout its specialized proof chain.
The source statements have no mathematical restriction equating these universe
parameters. The new companions generalize the actual existing proofs, with
explicit base-site sheafification hypotheses already present in this item and
the existing proved slice-site instances. The independent coefficient universe
is preserved throughout; no target binder or conclusion is weakened.

The retained report described a four-module decomposition with one sectionwise
hole. Subsequent retained work completed the expanded comparison chain, and the
current compile confirms it. That old report is superseded by this report.
Scratch sheafification probes are unnecessary because the library now exposes
the required essentially-small-site instances. Scratch experiments and logs are
not delivered.

The constructions cover zero complexes, identity maps, empty sites, arbitrary
integers and unbounded complexes. In differential degree zero the formula is
`d_I f - f d_L`, and in degree minus one it is `d_I f + f d_L`; the Lean proof
uses Mathlib's `negOnePow` shift conventions. Empty direct sums are zero. All
new equivalences carry their component or naturality formulas, so their
existential statements determine the maps used downstream.

Search evidence retained in `searches.jsonl`: LeanFinder found K-injective
localization bijectivity; Loogle found `Localization.fac`; LeanSearch and
repository/Mathlib searches found sheafification and small-model transport but
no matching independent-universe sheaf Hom theorem. The proof uses the already
proved specialized route, Stacks 0A95, 0A94, 0A8Y, and exact extension by zero
from 03DI and 03DJ. The twelve new nodes record the searches and sources.

## New nodes

`lem-pur-rhom-well-defined-universes`: quasi-isomorphism invariance at independent
coefficient size, proved by sectionwise invariance and detection (Stacks 0A95).

`lem-pur-quasi-iso-of-sections-universes`: detection through sections, proved by
exact abelian sheafification and reflection through module forgetting (0A95).

`lem-pur-hom-complex-sections-quasi-iso-universes`: sectionwise invariance, proved
by derived naturality and composition with two derived isomorphisms (0A95/0A94).

`lem-pur-hom-complex-sections-derived-naturality-universes`: shifted derived
comparison naturality, proved from homotopy naturality and K-injective
localization bijectivity (0A8Y/0A94).

`lem-pur-hom-complex-sections-homotopy-naturality-universes`: homotopy comparison
naturality, proved on cocycle representatives and descended to homology (0A8Y).

`lem-pur-hom-complex-sections-canonical-comparison-universes`: canonical cycles
and homology comparisons, proved using cochains, differential compatibility and
Mathlib's external Hom cohomology comparison (0A8Y).

`lem-pur-hom-complex-sections-cochains-universes`: degreewise section/cochain
additive equivalences from the Hom-complex product projections (0A8Y).

`lem-pur-hom-complex-sections-cochains-comm-universes`: differential compatibility
from the Hom-complex differential projection formula (0A8X/0A8Y).

`lem-pur-kinjective-restrict-localized-universes`: K-injective restriction,
proved using its exact left adjoint (08FI).

`lem-pur-localized-module-restriction-quasi-iso-universes`: preservation of
quasi-isomorphisms by exact restriction, proved by finite-limit and
finite-colimit preservation reflected through abelian-sheaf forgetting (03DK).

`lem-pur-kinjective-restrict-localized-adjunction-universes`: packages the exact
left adjoint and sectionwise additivity of restriction (08FI; 03DI/03DJ).

`new-localized-restriction-extension-exists-universes`: constructs the sheafified
direct-sum left adjoint and proves its adjunction and exactness (03DI/03DJ).

Each new node has a Lean record and a complete proof. The change record is
`coord/changes/DerivedInternalHomCoefficientUniverse.md`.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
