## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.geometricStalkToposPoint` with explicit
constructions for both sites. A private general gluing argument proves the function
presheaves are sheaves, using cofiltered pointed refinements and surjectivity on covering
lifts. For the etale site, Mathlib's point supplies the lifts and colimit API. For the
pro-etale site, a covering point gives a point of the pullback; the existing
`exists_comp_eq_id_of_weaklyEtale` supplies its section. Explicit mutually inverse maps
between colimit maps and sheaf maps give the two adjunctions. Sectionwise limits and
filtered colimits of sets give finite-limit preservation. All public signatures and
definitions are unchanged. Updated the node's proof to describe the actual covering-lift
and gluing arguments.

## Proved and sorry left

The delivery replaces the one hole in `AlgebraicGeometry.Scheme.geometricStalkToposPoint`
(node `lem-fix-geometric-stalk-topos-point`). No holes are added; no split-off modules or
nodes are introduced. Actual hole count: zero. On resuming, the module compiled cleanly through
`lcompile.py` against the current published library in 2.7 seconds, with no warnings.

## No longer needed

The proof uses the existing weakly-etale section theorem directly; it does not need the
algebraic residue-field construction in `Sheaf.RingTheory.WeaklyEtaleField`, nor the
ind-principal-Zariski definitions in `Sheaf.RingTheory.IndPrincipalZariski`. It also does
not need the generic skyscraper adjunction: the direct colimit hom equivalence ensures
the requested function presheaf equality literally. The separate covering-family
base-change lemma `lem-galois-fpqc-covering-base-change` and the standalone fpqc-covering
definition `def-weil-pbc-fpqc-covering` are no longer proof dependencies: selecting a
covering point and forming its pullback suffices. All other statement and proof
dependencies remain. Removed the proof imports `Mathlib.CategoryTheory.Sites.Point.Skyscraper`,
`Mathlib.AlgebraicGeometry.Sites.Fpqc`, `Sheaf.RingTheory.IndPrincipalZariski`,
`Sheaf.RingTheory.WeaklyEtaleField`,
`Sheaf.AlgebraicGeometry.PointedEtaleStalk`, and
`Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor`. The etale stalk is supplied directly
by Mathlib and the needed set-valued pro-etale stalk declarations are already public in
`Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk`; the module-stalk packaging is unused.
The existing direct import
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale` supplies the section
theorem. Removed the stale `tool_uses` approval for
`lem-weil-pbc-weak-etale-field`; the node itself is retained.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The proof plan's detailed residue-field construction is
already encapsulated by the declared weakly-etale section theorem; the delivery uses that
theorem. Mathlib's general point finite-limit instance requires an `AB5OfSize` instance
that does not synthesize for the coefficient universe here. Unfolding the stalk functor
and applying the existing filtered-set-colimit preservation instance proves the required
finite-limit preservation directly.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
