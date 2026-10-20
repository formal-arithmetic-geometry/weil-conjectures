## What changed

Filled `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar_of_etale`
in `WeilConjectures.SixFunctors.Etale.Derived.EtaleLocalization`, preserving its signature,
all existing declarations, attributes, docstrings, and public imports.

The proof follows the existing node
`lem-etale-exceptional-locality-arbitrary-schemes`:

1. Substitute the given equality identifying `h` with `u ≫ f`. A compactification of
   this composite supplies the immersion `U ⟶ Z ×_Y X`; its second projection is proper.
   `HasCompactification.of_isImmersion` then compactifies the quasi-compact map `u`.
2. For the chosen compactification of `u`, the existing
   `canonicalEtaleCompactSupportComparison` identifies `Ru_!` with exact derived sum
   extension. Transport `derivedEtaleLowerShriekUpperStarAdjunction` to obtain
   `Ru_! ⊣ D(u^*)`.
3. Compose this adjunction with `Rf_! ⊣ Rf^!`, transport along
   `nonempty_iso_rightDerivedLowerShriek_comp`, and apply
   `Adjunction.rightAdjointUniq`. Whiskering the existing exact/left-derived pullback
   comparison gives exactly the required isomorphism.

Added four private proof imports: `WeilConjectures.Compactification.Constructions`,
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition`,
`WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection`, and
`Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphDerivedIso`.
Each supplies a declaration used above. No definition, public interface, or DAG route changed.
The argument retains arbitrary schemes and imposes no extra quasi-compactness on `f` or `h`.

Searches: launcher msearch Loogle for `CategoryTheory.Adjunction.rightAdjointUniq`,
LeanFinder for exceptional inverse-image restriction through composed adjunctions, and
msearch grep for `mapDerivedCategoryAdjunction`; direct source searches checked the
existing exact sum-extension adjunction, compactification construction, graph comparison,
and compact-support composition. The module compiled cleanly through `lcompile.py`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar_of_etale`
(node `lem-etale-exceptional-locality-arbitrary-schemes`).

There are zero `sorry`s left in the item module and zero added anywhere. No statements
were split off. The proof uses the existing graph-comparison dependencies as the DAG
specifies; this does not claim to close their separate proof obligations.
The existing surjective étale conservativity theorem is unchanged.

## No longer needed

None. Every declared proof dependency remains used by the planned argument. No imports,
declarations, nodes, or modules were removed or withdrawn. All existing public imports
are preserved under the source-library boundary.

## Where the brief, the DAG or earlier work was wrong

No correction to the statement or DAG plan was necessary. The newer source theorem
`isIso_compactificationEtaleComparison` provides a direct comparison, but its module
already reaches this item, as confirmed by `tools/import_direction.py may`; importing
it would create a cycle. The existing DAG graph comparison avoids that cycle and
provides the required comparison for arbitrary schemes with quasi-compact `u`.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
