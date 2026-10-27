## What changed

Proved `AlgebraicGeometry.Scheme.etaleSheaf_isZero_of_isZero_over_cover` in
`Sheaf.AlgebraicGeometry.EtaleSheafZeroOnCover` with its signature unchanged.
The covering family generates a covering sieve on the identity etale X-scheme.
Pulling that sieve back to an arbitrary test object gives a covering sieve;
every member factors through a covering member and is an object of that slice.
Evaluating the local identity-equals-zero equation gives zero section modules.
Mathlib sheaf separatedness then proves the global identity is zero.

The DAG copy records this sieve formulation of the original argument. All public
imports are preserved; the three unused private imports are removed.

Searches used leanfinder, loogle, msearch grep, and local rg. Mathlib
`Presheaf.IsSheaf.hom_ext`, `Scheme.ofArrows_mem_smallEtaleTopology_iff`,
`GrothendieckTopology.pullback_stable`, and `IsZero.iff_id_eq_zero` provide all
required tools. The similarly named `Scheme.zero_of_zero_cover` applies only to
structure-sheaf sections and is not used. Read the master proof and its identical
main-20261015 version under sec-smooth-purity/sk-lem-sp-tower.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.etaleSheaf_isZero_of_isZero_over_cover`
(node `lem-sf-sheaf-zero-on-open-cover`). No holes remain; no holes added or split off.
The proof uses no project theorem with sorry. Compilation through lcompile.py
passed. The argument includes the empty index type, arbitrary infinite covers,
the identity cover, the zero sheaf, and zero coefficient rings without adding
hypotheses or making a choice of a covering index.

## No longer needed

Removed private imports `Sheaf.CategoryTheory.RingedSiteModules`,
`Sheaf.CategoryTheory.SiteCoveringAxioms`, and
`Mathlib.CategoryTheory.Sites.Sheaf` (already public through the slice-site API).
The first two modules and nodes `def-weil-sheaf-of-modules-category` and
`def-weil-pbc-sites-and-cohomology` are unnecessary for this proof: fixed-coefficient
ModuleCat-valued sheaves have the generic Mathlib sheaf condition, and the existing
Grothendieck topology supplies pullback stability directly. Their proof-dependency
edges are removed. This does not claim they are unnecessary to other consumers.
No declarations or modules are withdrawn, and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original argument was correct. Its explicit fibre products and product of zero
modules are unnecessary: pullback of the generated covering sieve and categorical
separatedness express the same argument directly. The node source.place refers to
“Step 5”, although the blueprint proof has no numbered steps; the declaration
and proof steps already cite the actual first and last sentences. No statement
or definition was changed, and no new nodes were needed.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
