## Worker report

The module `Sheaf.Paper.RefinementCoefficientMate` states
`AlgebraicGeometry.refinementCoefficientMate`.  It has no definitions with
postponed data.  Its proof is `sorry`, as required for a stage-2 statement.
The module imports the existing normalized coefficient-refinement construction
and the canonical pro-etale proper/open transport.

The first conjunct is the coefficient equation.  Its hypotheses are rendered as
follows:

- `A` and `B` are `Type (u + 1)` with `[CommRing]` and `[Finite]` instances;
  `φ : A →+* B` is the unital coefficient map.
- `X`, `T₁`, and `T₂` are `Scheme.{u}` with `[IsNoetherian]` instances.
- `u : T₁ ⟶ T₂` has `[IsProper u]`; `j₁ : X ⟶ T₁` and
  `j₂ : X ⟶ T₂` have `[IsOpenImmersion]` instances and
  `h : j₁ ≫ u = j₂`.
- `L` is a bounded-below object of
  `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)`, and `hL` says its
  scalar extension is bounded below.

The first displayed composite is
`scalarExtension φ T₂` applied to the normalized etale proper/open map,
followed by the etale scalar mate `scalarMate φ u`, followed by the normalized
open coefficient isomorphism for `j₁`.  Its target is the normalized
`j₂` coefficient isomorphism followed by the proper/open map over `B`, applied
to the scalar extension of `L`.  Thus it renders both sides of the coefficient
square, including their directions, in the unbounded derived category.

The second conjunct is universally quantified over a finite commutative ring
`R` and a bounded-below etale input `K`.  The left-hand side is
`properOpenSiteExtensionIso R j₂` followed by
`properOpenProEtaleIsoPlus R u j₁ j₂ h K`; this is the site comparison
`e_{j₂}` followed by the pro-etale alpha.  The right-hand side is the etale
`properOpenComparison R u j₁ j₂ h K`, transported by the comparison inverse
image on `T₂`, followed by
`Functor.rightDerivedFunctorPlusBaseChange (lowerStarComparisonUpperStarBaseChange u ...)`
and then the lower-star image of `properOpenSiteExtensionIso R j₁`.  These are
respectively the canonical direct-image mate `d_u` and the site comparison
`e_{j₁}` in the node's notation.  The equality is in the bounded-below
presentation of the unbounded derived categories, on exactly the etale-origin
inputs quantified by the node.

The coefficient square is the concrete statement already supplied by
`AlgebraicGeometry.Etale.properOpenComparison_coefficient_refinement`; the
module restates its type so that the node has one theorem containing both the
coefficient and site clauses.  The site maps are the canonical maps from
`AlgebraicGeometry.ProEtale.properOpenSiteExtensionIso` and
`AlgebraicGeometry.ProEtale.properOpenProEtaleIsoPlus`; no arbitrary
isomorphism is chosen.

Dependencies used (module and declaration):

- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `AlgebraicGeometry.ProEtale.FiniteCoefficientModules`.
- `Sheaf.AlgebraicGeometry.ProperOpenComparison`:
  `AlgebraicGeometry.Etale.properOpenComparison`.
- `Sheaf.AlgebraicGeometry.DerivedOpenRestriction`:
  `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_openImmersion`.
- `Sheaf.AlgebraicGeometry.ClopenSectionDirectImage`:
  `AlgebraicGeometry.Etale.clopenSectionDirectImage`.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`:
  `AlgebraicGeometry.ProEtale.openImmersionLowerShriekComparison_coherence`.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`:
  `AlgebraicGeometry.ProEtale.fixedComparisonDirectImageMatePlus`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology` and the derived
  category infrastructure it imports.
- Mathlib leaves `AlgebraicGeometry.Scheme`,
  `Mathlib.RingTheory.Noetherian.Defs.IsNoetherianRing`,
  `AlgebraicGeometry.IsProper`, and `AlgebraicGeometry.IsOpenImmersion`.

Edge cases checked: the statement permits arbitrary universe `u`; zero rings
and zero complexes are allowed by the finite commutative-ring and derived
category binders; `L` may be zero; the identity refinement (`u = 𝟙`) and either
identity open immersion are included; no nonempty scheme, flatness of `φ`,
constructibility, finite Tor amplitude, or cartesianness of `j₁ ≫ u = j₂` is
added.  The pro-etale clause quantifies all finite commutative `R`, including
`R = 0`, and does not assert that scalar extension preserves `D+`.

Searches for an existing declaration were made as required:

- `msearch.py leanfinder` query “coefficient change and etale proetale comparison
  commute with proper open refinement”: eight hits, all generic etale/ring
  homomorphism declarations; no match for this square.
- `msearch.py loogle` query `properOpenProEtaleIsoPlus, properOpenComparison,
  scalarMate`: zero hits (the service did not know the project-specific name).
- `msearch.py grep` query `properOpen.*(coefficient|site)|scalar.*properOpen`
  in `AlgebraicGeometry`: no duplicate declaration.
- `rg` over `WeilConjectures/` and `lean/Sheaf` for
  `refinementCoefficientMate` and the node id found no existing declaration
  or module.  `rg` found only the node-id citations in the unrelated
  `lem-sp-et-proet-coefficient-compatibility` and normalization records.
- The existing source files `ProperOpenCoefficientRefinement.lean` and
  `ProEtaleProperOpenComparison.lean` were opened in full.  They provide the
  canonical declarations used above, but neither declares this combined node.

Compilation with
`scompile.py NZ lem-sp-refinement-coefficient-mate` passed for the module with
no errors or warnings.  The long-line check is clean.

## Second reading by NZ

I reopened the node statement, its 11 proof steps, and the complete module.  The
first conjunct matches every coefficient hypothesis and the exact composite
order in the node: scalar extension of `alpha_A`, the B-linear direct-image
mate, and the `j₁` open tensor map equal the `j₂` open tensor map followed by
`alpha_B`.  The second conjunct matches the node's `N`, `e_j`, and `d_u`
notation through the canonical comparison and proper-open site declarations;
its source and target are the same comparison-image bounded-below objects.
No hypothesis was added or dropped, no conclusion was weakened, and no
additional definition or local notation was introduced.  The theorem remains a
statement with `sorry` only.
