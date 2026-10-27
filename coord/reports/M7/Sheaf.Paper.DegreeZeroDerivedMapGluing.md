## What changed

Filled `AlgebraicGeometry.DegreeZeroMapGluing.degreeZeroDerivedMapGluing` in
`lean/Sheaf/Paper/DegreeZeroDerivedMapGluing.lean`. All existing public signatures,
definitions and public imports are unchanged. Private proved helpers assemble the
existing good-truncation normalization with exact cohomology coherence and direct
fixed-ring sheaf gluing on the two small sites.

The site gluing arguments adapt the proved source constructions in
`Etale.Derived.HeartGluing` and `ProEtale.Adic.LisseCover.SheafGluing`, allowing the
arbitrary index universe required here. They use Mathlib's sheaf of morphisms and
its covering-family amalgamation theorem. Compatibility on intersections is
transported by the existing pullback/localization compositor coherence and
naturality on site-object isomorphisms. The existing conservativity results give
zero detection and uniqueness. This handles empty families without an exception.

## Proved and sorry left

Closed: `AlgebraicGeometry.DegreeZeroMapGluing.degreeZeroDerivedMapGluing`
(node `lem-pur-degree-zero-derived-map-gluing`), the sole original hole.
Added holes: none. Sorries left in delivered Lean files: zero. Split-off statements: none.
The proof also uses the existing pullback existence theorem through its two
projection equations, so the intersection construction is not unfolded during
section-map transport.

The site helpers are proved for an abstract Grothendieck abelian coefficient
category and instantiated with `ModuleCat A` only at the final assembly. This
avoids expanding categorical composition into linear-map composition during
checking. The geometric transport is proved for arbitrary localized sheaf maps before
instantiating those maps with the pullback comparison. This keeps the adjunction
construction out of the sectionwise calculation.

All private helpers have complete proofs. The complete module compiled in 21.4 seconds
with the prescribed single-file compiler. The final cleaned packet is checked again
by delivery preflight; no local Lake build is used. Generic categorical congruence,
associativity and natural-isomorphism cancellation keep adjunction constructions
out of concrete kernel reductions; no existing definition needed alteration.

## No longer needed

The following proof imports were removed from the item:

- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.CategoryTheory.TruncationDescends`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.CategoryTheory.Sites.CoverLifting`
- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.Paper.SfCommonStageWeilCohomology`

The item's route no longer needs `lem-pur-open-cover-cohomology-detection` or its
module `Sheaf.AlgebraicGeometry.OpenCoverCohomologyDetection`: the statement uses
fixed-ring module-valued sheaves, and the existing fixed-ring restriction
conservativity directly detects zero cohomology sheaves. It also no longer needs
`lem-pur-sheaf-hom-cover-gluing` and the retired
`Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing` module: direct application
of Mathlib's presheaf-Hom sheaf axiom avoids converting to ringed-module sheaves.
The upstream `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`
declaration is preserved and is not withdrawn.

The old standalone truncation-descends, localized ringed-module, finite-coefficient
realization, affine-basis and quasi-separatedness proof imports are unnecessary
here. Normalization and exact cohomology coherence supply precisely their needed
consequences; open covering membership uses the already proved precoverage
comparison. Removed obsolete `tool_uses` entries:
`lem-weil-pbc-truncation-descends`, `lem-pur-sheaf-hom-cover-gluing`.
These are pruning claims for this item's direct proof route only; dependencies
still used by other declarations remain in the library. In particular,
`TruncationsAndHomotopyColimits` is still a public dependency of the normalization
module, and `Localization.Predicate` is still a private dependency of exact
cohomology coherence. Their direct imports are redundant here; this delivery does
not claim those modules have left the targets' transitive import closure.

## Where the brief, the DAG or earlier work was wrong

The stated open-cover detection and module-Hom gluing interfaces use modules over
a sheaf of rings, whereas this item's signature uses sheaves valued in the fixed
category `ModuleCat A`. Applying those declarations literally requires a coefficient
realization comparison. A shorter route uses the already proved fixed-ring source
restriction APIs and Mathlib sheaf-Hom gluing directly. No mathematical statement
or unit route is changed. The existing etale sheaf-gluing theorem restricts its
index to `Type u`, while this item allows `Type wI`; its proof works unchanged for
a covering sieve indexed in an arbitrary universe, so private helpers make this
extension explicit. The pro-etale source gluing proof is similarly extended from
one cover arrow to an open covering family.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
