## What changed

Proved all three theorems in
Sheaf.CategoryTheory.RestrictedTowerResolutionAcyclicity, preserving their statements and
all existing public definitions.

Exactness follows from exact evaluation of strict systems and exact scalar restriction.
For acyclicity, the proof constructs the ordinary left adjoint of restriction on towers,
using the existing normalized scalar-extension models and transition maps. Constant-ring
strict systems supply componentwise K-flat tower resolutions. The generic
isIso_map_of_adjoints theorem underlying ringed-topos derived composition then proves
inverse-limit acyclicity. Projection naturality and cancellation give the asserted equation.

Resolution transitions are obtained from the K-injective Hom comparison. Their uniqueness,
fractions, preservation under additive functors, comparison square, and both normalized
projection identities are proved directly using homotopies.

Updated the existing node's proof, proof_deps and proof_origin to describe this argument.
Only private proved helpers and proof imports were added; no other module was adapted.
The generic comparison is proved with abstract categories and localization choices to
avoid repeatedly unfolding the concrete sheaf constructions. Projection cancellation
is likewise checked in an abstract category before specialization. Restriction and
projection constructions are locally irreducible after their interface lemmas. The complete module compiled
without warnings in 46.5 seconds through lcompile.py, with no diagnostic options retained.

## Proved and sorry left

Closed the three original holes:

- SheafOfModules.RestrictedTowerResolution.restrictionFunctor_exact
- SheafOfModules.RestrictedTowerResolution.acyclicity
- SheafOfModules.RestrictedTowerResolution.resolutionTransitions

The item contains zero remaining sorry occurrences. Added zero holes and split off zero
statements. All private helpers are proved.

## No longer needed

Removed the following direct proof imports and their direct proof dependencies:

- Sheaf.CategoryTheory.RestrictionRingedToposModuleDirectImage
  (lem-weil-pbc-restriction-ringed-topos-module-direct-image): the ordinary functor is
  already constructed in the item, and exactness follows componentwise.
- Sheaf.CategoryTheory.KInjectiveDerivedMapComputation
  (lem-sf-kinjective-derived-map-computation): the stated transition conclusions follow
  directly from the Hom comparison and homotopy equivalences.
- Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
  (prop-pur-kinjective-resolutions-exist): the hypotheses already supply all K-injectives
  used by these theorems.

These are dependency-edge removals for this proof. No module is withdrawn, and no claim is
made that another consumer no longer needs these results. Existing public imports stay.

## Where the brief, the DAG or earlier work was wrong

The named ringed-topos composition theorem and restriction-morphism interface are stated
for small sites with coincident coefficient and site universes. The item permits independent
universes and an essentially small site. Its acyclicity proof therefore uses the generic
resolving-adjunction comparison already proved in the composition module, together with the
existing independent-coefficient scalar models and sequence-site K-flat resolutions.
The mathematical route and all three public conclusions are preserved.

K-injective existence and the more elaborate derived-map computation interface were
unnecessary for the already supplied resolutions and the explicit homotopy conclusions.
No disputed statement, definition change, or new node is involved.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
