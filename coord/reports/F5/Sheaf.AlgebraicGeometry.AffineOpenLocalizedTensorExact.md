## What changed

Reapplied the upstream-sync repair after the return of branch head 33b0f38f6e,
whose base was e0d550965. Read the current coord/rework.tsv row and the current
quarantine archive: the live item is absent because of the recorded import
collision. Rebuilt all three restored modules from the current quarantine files,
then reapplied the canonical import to the root. Rebuilt the two adapted live
dependencies from their current sources and reapplied the retained proof repair.
The two consumer files match their current quarantine archives byte for byte;
the root differs only in its canonical public import. Refreshed the node copy
from the current DAG, retaining only this repair's proof-owned fields.
Repaired the upstream-sync import collision in
Sheaf.AlgebraicGeometry.AffineOpenLocalizedTensorExact and restored its original
Lean path. The item now publicly imports the canonical upstream
DerivedTensorCohomologyVanishes module. Its theorem signature and proof are
unchanged. PrincipalLocalizationRestrictionModel and
PrincipalLocalizationSheafTorBounds use that same public statement dependency,
so the proof path loads one definition of schemeDerivedTensorCohomologyVanishes.

Reproved AlgebraicGeometry.principal_localization_sheaf_tor_bounds using the proved
upstream openImmersion_tensor_vanishing_test. The proof tests hamp on the direct
image of the test sheaf and transports its representing isomorphism through
Functor.mapDerivedCategoryNatIso and the existing localization comparison.
The finite-limit instance is transported along the functor isomorphism.
The theorem signature and its vanishing interval are unchanged.

Restored both quarantined consumers verbatim:
Sheaf.AlgebraicGeometry.AffineTruncationKernelFlat and
Sheaf.AlgebraicGeometry.AffineTruncationKernelFiniteLocallyFree.
All five delivered modules compile in dependency order without warnings on the
repair retry using lcompile.py --all. The item itself has zero textual holes;
the retained restriction-model dependency still contributes its named hole.
The Tor-bound node now records the actual upstream proof dependency.
The change record is
coord/changes/affine-open-localized-tensor-canonical-vanishing.md.
No source-library files, target statements, definitions or universes are changed.

## Proved and sorry left

This is an assigned quarantine repair with zero original holes in the item:
AlgebraicGeometry.affine_open_localized_tensor_exact remains fully proved from
its named dependencies. Holes closed: 0. Holes added: 0. Split off: 0.
The two restored consumers also have zero holes.
AlgebraicGeometry.principal_localization_sheaf_tor_bounds is fully reproved.

One pre-existing hole is retained unchanged in an adapted dependency:
AlgebraicGeometry.principalLocalization_restriction_model
(node lem-sc-principal-localization-restriction-model), whose entire proof is
`:= by sorry`. This delivery does not claim that dependency or the targets are
axiom-free. No new statement or definition is introduced.

## No longer needed

Removed the public import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
from the item, PrincipalLocalizationSheafTorBounds and
PrincipalLocalizationRestrictionModel, replacing it with the canonical upstream
module of the same notion.

Removed the private import Sheaf.AlgebraicGeometry.OpenImmersionTensorVanishing
from PrincipalLocalizationSheafTorBounds. Its node
lem-sc-open-immersion-tensor-vanishing and the proof-only dependency chain through
Sheaf.AlgebraicGeometry.Modules.IsKFlatRestriction are no longer needed by this
proof. The proved upstream lem-pc-open-immersion-tensor-vanishing-test supplies
the needed assertion directly, with derived-functor transport in this module.
No global module deletion or global closure pruning count is claimed: other
modules may still import these old twins. No unit statement or realized proof
step is bypassed (sk-thm-picard-duality has empty realized lists).

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a module containing sorry. The actual queue item is
an upstream-sync rework root: its source is in quarantine rather than lean, and
it already has zero holes. coord/rework.tsv records a duplicate-definition import
failure, not a missing proof. The restored cluster has three modules.

The old Sheaf vanishing definition and its upstream twin have the same fully
qualified name. They cannot coexist in one import closure. Their K-flat predicates
have different names but identical bodies, so selecting the upstream definition
preserves the mathematical statement. The old Tor-bound proof import unnecessarily
loads the Sheaf twin; the upstream test theorem replaces that route.

LeanFinder returned ordinary tensor exactness and localization exactness lemmas;
Loogle returned no ExactAt/ModuleCat match. Local rg located the proved upstream
openImmersion_tensor_vanishing_test and the exact-functor natural-isomorphism API,
whose signatures were read. msearch.py calls were made for all three search types;
its grep service returned no hits, so local source searches supplied the matches.
Edge cases remain unchanged: zero rings, f=0, empty U, zero modules and a>b use
the same comparisons and interval-widening argument; no hypothesis is added.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
