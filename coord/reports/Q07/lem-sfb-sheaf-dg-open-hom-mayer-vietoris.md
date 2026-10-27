## Worker report

The module `Sheaf.CategoryTheory.SheafDgOpenHomMayerVietoris` states
`CategoryTheory.SheafDg.sheaf_dg_open_hom_mayer_vietoris`, with `sorry`.
The auxiliary structures describe its data; none chooses data from an existence
proof, and all helper definitions have explicit bodies. No node statement is changed.

Hypothesis and clause correspondence:

- The space is `X : TopCat.{u}`; the sheaf of commutative rings is `S`.
  `EssentiallySmall.{w} (Opens X)` is the explicit size convention, with independent
  site and coefficient universes. `Algebra S`, `LeftModule`, `Derived`,
  `derivedHasShift`, `cone`, and `IsConeTriangle` are the recorded localization
  dependency, not private replicas. No commutativity of the dg algebra is assumed.
- `U V : Opens X` and `hcover : U ⊔ V = ⊤` give the two-open cover;
  the intersection is always `U ⊓ V`.
- `OpenHom A Z P Q n` is exactly the indicated Hom between the restricted objects,
  shifting the second after restriction. All degrees are integers and all derived
  objects are quantified, without perfectness, flatness or boundedness restrictions.
- `homCoverRestrict` is the pair of canonical restrictions, with their shift
  identifications. `homCoverDifference` subtracts the restrictions to the intersection.
  `homRestrictNested` expresses ordinary nested restriction by its open adjunction
  mate, using extension maps fixed by the counit characterization.
- `HomCoverExact` requires all three consecutive exactness positions for every
  integer. `HomCoverAdditive` also requires each arrow to preserve sums. The product of two additive Hom groups is their finite direct sum.
- `OpenHomGeometry` supplies ordinary and derived lower shriek with adjunctions to
  the recorded actual restrictions. The comparison and counit equations normalize
  the derived adjunction by the ordinary one. Thus this is extension by zero, which
  has the specified stalks, rather than an arbitrary functor with unconstrained maps.
- `OpenHomInclusions.ordinary_characterization` fixes the positive inclusion maps.
  `ordinaryCoverFirst` takes the U component and minus the V component;
  `ordinaryCoverSecond` is the pair of counits. The derived triangle uses the same
  signs and maps. `OpenHomTriangles.cone_normalization` fixes q=(b,0), requires its
  localized invertibility and identifies the boundary with the negative cone
  projection composed with its inverse. `homCoverBoundary` is its contravariant
  shifted-adjunct formula, including the canonical shift-add comparison.
- `HomCoverNatural` writes the three arrow squares for arbitrary a:P'→P and b:Q→Q'.
- `HomScalarSystem.extension` uses the recorded `DerivedExtension`, including its
  universal comparison to the actual balanced tensor. Its adjunction counit is
  required to be `derivedActionCounit`. Restriction is fixed on localized modules.
  Open support comparisons commute with the open counits, fixing the adjunction mate.
- `scalarHom` applies the derived functor and its shift comparison; `scalarOpenHom`
  is the same map on an open expressed via the open adjunction. `HomCoverScalar`
  includes additivity, both restriction squares, every connecting square, and the
  comparison of the triangle boundaries themselves.
- `scalarIdentityIso` and `scalarCompositionIso` are Mathlib's adjunction uniqueness
  comparisons, with restriction comparisons fixed as identity maps on underlying
  complexes. `HomScalarCoherent` gives their equations on every global and open Hom
  term, hence on the whole sequence by the preceding arrow squares.
- The existence statement packages these data and assertions in
  `Nonempty (OpenHomMayerVietoris S U V)`; none of them is an extra hypothesis.

Dependencies read and used:
`Sheaf.CategoryTheory.SheafDgModuleLocalization`, namespace
`CategoryTheory.SheafDg`, especially `Derived`, `derivedRestriction`,
`restrictAlgebra`, `DerivedExtension`, `derivedActionCounit`, `cone`,
`coneConnecting`, `shiftObjectIso`, and the exact localization equations.
`Sheaf.CategoryTheory.RingedDgScalarAdjunction` is imported for its recorded
right/opposite scalar theorem; the statement supplies a normalized left interface
on the already mandated localization, not a second localization. Its
`RingedSiteDg.complexMonoidal` instance overlaps the left-interface tensor instance;
the module disables that imported instance to retain the recorded left tensor.
The other recorded proof dependencies with modules are imported as proof imports.
The four presently unstated dg-calculus proof nodes are documented in the theorem's
seven-step natural-language proof plan. `def-weil-size-convention` is a convention
record, with no module or declaration to import.

Edge cases checked: empty X; U empty or V empty; disjoint opens; U=V=X;
P or Q zero; all negative degrees and n=0; noncommutative dg algebras; nonflat scalar
maps. The formulas impose no exclusions in these cases. No STATEMENT-DISPUTED fault
was found. Ordinary lower shriek is determined up to unique adjunction-compatible
isomorphism; the specified comparisons transport the triangle through that freedom.

Searches: msearch LeanFinder, “Mayer Vietoris long exact sequence for derived Hom of
sheaf differential graded modules natural under derived extension of scalars”:
ordinary MayerVietorisSquare shortComplex results only. msearch Loogle,
“MayerVietoris, DerivedCategory”: no match (unknown identifier MayerVietoris).
msearch grep, “Mayer.Vietoris|mayer.vietoris|SheafDg”: 14 Mathlib hits, ordinary
sheaf cohomology only. msearch LeanSearch, “Mayer Vietoris long exact sequence for
derived Hom of sheaf dg modules compatible with derived extension of scalars”:
eight ordinary MayerVietorisSquare results. Direct rg in `lean/WeilConjectures`
and `lean/Sheaf` found ordinary derived module Mayer–Vietoris and the dg localization,
not the dg sequence and scalar boundary compatibility. Direct search for this
node id in `lean/WeilConjectures` found no declaration.

Source reading: local Stacks `cohomology.tex`, lemma-mayer-vietoris-hom and its proof;
`sdga.tex`, lemma-extension-by-zero-dg and lemma-tensor-with-extension-by-zero-dg.
The scalar refinement follows the seven proof steps in the supplied DAG node,
which explicitly identify it as stronger than Tag 08BW alone.

## Review by Q07

Author's second pass, not an independent review: checked each field against the node
and inspected the dependency source signatures and docstrings. Corrected an inferred
natural-number shift to an explicitly integer shift, and made the scalar restriction
identity/composition maps explicit on dg modules. Verified that the main theorem
assumes only the space/coefficient size convention and the stated two-open cover.
The maintainer performs the independent mathematical review.

## Second reading by Q07

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
