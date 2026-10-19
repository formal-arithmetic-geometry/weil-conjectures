## What changed

Proved `WeilConjectures.smooth_affine_frontier_stratification`, preserving its signature,
universes, visibility, docstring and public imports. The proof constructs a geometric
closed filtration, descends it to one finite subfield, uses singleton component families,
classifies dimension-zero pieces by their diagonal, and factors geometric pieces through
the prescribed immersed strata.

Added two proved supporting modules, each with its own DAG node:

- `Sheaf.DeligneLaumon.SmoothAffineGeometricFiltration`: the concrete
  `SmoothAffineFiltration` structure and a Noetherian-induction construction. At each step
  it removes a nonempty smooth connected affine open lying in one partition part and
  continues on the reduced closed complement. All construction data and helpers are proved.
- `Sheaf.DeligneLaumon.SmoothAffineFiltrationFiniteFieldDescent`: simultaneous finite-field
  descent of an already prescribed geometric filtration. Finite-presentation object descent
  over the ambient inverse system gives models of the closed terms at a common stage.
  Faithfully flat descent makes them reduced closed subschemes. Unique factorization
  reconstructs the chain arrows; taking open complements reconstructs its pieces.
  Endpoint normalization identifies the first model with the actual ambient reduction
  and the last with the canonical empty scheme. The proof descends affineness and constant
  smooth dimensions, checks geometric connectedness after extension, and verifies the exact
  ambient comparison equations against both projections of the pullback.

Updated the item's proof route and dependencies and removed obsolete tool approvals.
The unit route through Noetherian induction, smooth affine pieces and one finite constant
extension is retained. No other group's module or existing statement/definition is changed.

## Proved and sorry left

Original item: 1 hole. Delivered item: 0 holes. Holes closed: 1. Holes added: 0.

Closed `WeilConjectures.smooth_affine_frontier_stratification`, node
`lem-zl-smooth-affine-frontier-stratification`.

Also fully proved:

- `WeilConjectures.exists_smooth_affine_geometric_filtration`, node
  `lem-zl-smooth-affine-geometric-filtration`;
- `WeilConjectures.exists_smooth_affine_filtration_finite_field_model`, node
  `lem-zl-smooth-affine-filtration-finite-field-descent`.

There are no remaining sorries in any delivered module, and no split-off proof obligations.
All private helpers are proved, and no definition contains a hole. This closes the original
hole from existing library results; it does not assert that every existing dependency of
those results is axiom-free. Each delivered file compiles through `lcompile.py --all`, with
no warnings; import direction checks accept the new dependency chain.

The empty geometric scheme has a length-zero geometric filtration. The final theorem
handles it with one empty layer and no components, satisfying its unchanged exact signature.
The finite-field model theorem preserves the literal reduced initial object in length zero.
Positive-length filtrations have a literally canonical empty last term. Covers can contain
empty parts and overlap. Reducible schemes are handled by successive choices within one
irreducible component. The zero-dimensional classification requires no chosen rational point.

## No longer needed

Removed these proof imports from the original item:

- `Sheaf.AlgebraicGeometry.DescendClosedImmersion`
- `Sheaf.AlgebraicGeometry.DescendSmoothQcqs`
- `Sheaf.AlgebraicGeometry.FiniteFieldClosedSubschemeDescent`
- `Sheaf.AlgebraicGeometry.GeometricReducedFiniteTypePerfectField`
- `Sheaf.AlgebraicGeometry.OpenImmersionInverseLimitDescent`
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`
- `Sheaf.DeligneLaumon.AffineGeometricComponentsFiniteExtension`
- `Sheaf.Topology.NoetherianGoodStratificationRefinement`
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`
- `WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat`
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`

Unneeded branches for this proof:

- `lem-sfb-noetherian-good-stratification-refinement`: removing one open at a time already
  gives the closed filtration, without a prior frontier refinement.
- `lem-zl-affine-geometric-components-finite-extension`: the geometric construction chooses
  connected pieces and faithful-flat descent preserves their geometric connectedness.
- `lem-zl-bertini-finite-field-descent`: closed objects descend over the ambient inverse
  system directly, without Frobenius automorphisms.
- `lem-weil-pbc-descend-smooth-qcqs`: specified smooth relative dimensions descend along the
  field extension, without an eventual-stage argument.
- `lem-weil-pbc-descend-open-immersion-qcqs` and
  `lem-weil-pbc-descend-closed-immersion`: the models are already cartesian over a faithfully
  flat projection, so fpqc descent gives closed immersions immediately. Their open
  complements are constructed directly, rather than descended separately.
- `lem-kun-geometric-reduced-perfect`: reducedness of closed models descends from the
  geometric terms; normalizing the initial reduced closed model avoids commuting reduction
  with field extension.
- `lem-pur-geometrically-reduced-dense-smooth-open`: Mathlib already proves the dense smooth
  locus theorem for reduced finite-type schemes over perfect fields.
- `lem-weil-pbc-noetherian-finite-components`: only the open-neighbourhood property of a
  single irreducible component is needed, without an enumeration of all components.
- `lem-weil-pbc-finite-diagram-lift-of-models`: descending closed objects over the ambient
  inverse system and reconstructing their unique arrows avoids diagram lifting.
- `lem-weil-geometrically-connected-algebraic-closure`: the existing general field-extension
  criterion directly applies to the prescribed geometrically connected pieces.

Removed the old tool approvals for good refinement, eventual smoothness, component splitting,
and eventual closed/open immersion descent. The spreading-out approval remains in order.
Reduced induced closed complements and constant smooth dimensions still serve the proved
geometric node, and finite-presentation descent serves the proved model node: their removed
imports from the item are not claimed as globally pruned. No target-wide pruning count is
claimed without the ledger calculation.

## Where the brief, the DAG or earlier work was wrong

The retained packet described the final assembly as compiling while its latest descent
helpers had errors and its model theorem was still a hole. This session repaired those
helpers, completed endpoint normalization, and proved that model theorem. The initial dry
run rejected the unfinished one-hole decomposition; the completed packet adds no holes.

The original DAG's preliminary frontier refinement and simultaneous component selection
are unnecessary below the unit level. A finite closed chain is obtained directly by
Noetherian induction. Its finite-field descent only needs the closed terms as objects over
the ambient system, since reduced closed immersions have unique factorization maps.

The informal empty-case proof requests literal length zero. That would require equality
of the actual reduction object with a separately constructed empty scheme; the exact Lean
signature does not require length zero. A one-step chain of empty objects proves every
clause of that unchanged signature.

The hypothesis `hTred` is retained unchanged but is unnecessary: the geometric pieces are
reduced, which suffices for factorization through an immersed stratum. There is no statement
correction, definition repair or forced adaptation in this delivery.

## New nodes

`lem-zl-smooth-affine-geometric-filtration` records the concrete filtration structure and
its proved geometric Noetherian-induction construction in
`Sheaf.DeligneLaumon.SmoothAffineGeometricFiltration`. Source: Stacks 0B8X and the geometric
stratum induction in blueprint `thm-zl-real-mixed-by-curves`, paragraphs 6-7.

`lem-zl-smooth-affine-filtration-finite-field-descent` records the proved finite-field model
theorem in `Sheaf.DeligneLaumon.SmoothAffineFiltrationFiniteFieldDescent`. Source: Stacks
01ZM, fpqc descent and 054N, and the simultaneous finite constant-extension step of that
blueprint proof. This statement assumes the entire geometric filtration and its prescribed
pieces; it contains no partition, dimension-zero classification or stratum factorization.

Both nodes' proofs and dependency lists follow the completed Lean proofs. No change record
is needed for an existing declaration, and no module is withdrawn.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
