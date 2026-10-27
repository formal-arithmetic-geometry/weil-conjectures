## What changed

Proved `CategoryTheory.PrincipalQuotientCompletion.exists_derivedQuotientRoos` in
`Sheaf.Algebra.Homology.PrincipalQuotientRoosDerived`, preserving its statement,
coefficient/site universes, exact-countable-products hypothesis, and computation on
all K-flat complexes. The proof constructs tensor homotopies compatible with the
quotient tower, proves Roos invariance using exact products and the cone triangle,
and applies the existing resolving-class and pointwise Kan-extension declarations.
Private proved helpers transport the universal pair through the homotopy quotient.
No public definitions, instances, or statements were changed.

Added proof imports for strict Roos homotopies, signed total tensor, K-flat
resolutions, quasi-isomorphism fraction calculus, resolving-class essential
constancy, its Kan bridge, initial functors, and the existing exact-limit
quasi-isomorphism theorem. Updated only this item's node proof fields.

Search: Lean Finder found general total-left-derived and pointwise-derived APIs;
Loogle `"IsLeftDerivedFunctor"` found the general Kan/localization interface;
the prescribed grep search found pointwise Kan-extension APIs. Local searches
found existing private implementations of the general Kan-transport glue in
`DerivedChangeOfRingsCochainModel` and `CompletedConstantDerivedTensorTower`;
the proof reuses their argument as proved private helpers. The existing
`leftDerived_from_resolvingClass` also asks for triangulated functor data, which
this theorem does not need, so only its general essential-constancy/Kan argument
is used here.

Validation: the final proof compiled cleanly through `lcompile.py` in 46.3 seconds,
within the 60-second limit, with no errors or warnings. A source-signature comparison
confirmed the existing theorem statement is unchanged; the node proof-dependency
union was also checked. Delivery additionally runs its required compiler/axiom
probe and preflight. The proof has no conditions on t, so zero,
unit, and zero-ring cases are included. Tensor invariance never requires the given
K-flat complexes to have flat terms. No new statements or hollow constructions
were introduced.

## Proved and sorry left

Closed the single original hole in
`CategoryTheory.PrincipalQuotientCompletion.exists_derivedQuotientRoos`
(node `lem-pur-principal-quotient-roos-derived`). Proved 1 of 1 original sorries;
0 holes added and 0 split off. No sorry remains in any delivered Lean file.
All private helpers have complete proofs.

## No longer needed

Removed `lem-pe-kflat-roos-representative-invariance` from this item's proof
dependencies. Its module `Sheaf.Algebra.Homology.KFlatRoosRepresentativeInvariance`
is not imported: its flat-term hypotheses and separate concrete Roos presentation
are unnecessary. The proof instead uses signed total tensor, resolves the fixed
quotient factor, and works with the actual `roosF` of the item's model.

Removed `lem-weil-pbc-localization-universal-property` from this item's proof
dependencies: the universal pair is assembled from pointwise Kan limits, and
cochain transport is proved directly with initial structured-arrow functors.
The generic `Localization.lift` declaration attached to that node is not used.

The exploratory import `Sheaf.CategoryTheory.KFlatRoosTensorDescent` was not
retained: its tensor-invariance corollary follows directly from
`SheafOfModules.TotalTensorSigns.totalTensorHomotopyConeSigns`. No original
public import was removed. No existing module or declaration is withdrawn;
other consumers may continue to use the omitted planned dependencies.

## Where the brief, the DAG or earlier work was wrong

The planned representative-invariance lemma is not needed and would require
additional representation comparisons and flat-term hypotheses. Its needed
content follows directly from the recorded signed-tensor theorem, K-flat
resolutions, exact products, and the actual cone definition. The resolving-class
argument needs no triangulated-functor instance on quotientRoos, as the item's
docstring already observes. No mathematical statement correction was necessary.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
