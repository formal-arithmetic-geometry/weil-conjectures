## Worker report

The delivery states `AlgebraicGeometry.regular_pullback_unresolved_strata` in
`Sheaf.AlgebraicGeometry.RegularPullbackUnresolvedStrata`. Its only theorem has proof
`by sorry`. The module docstring identifies Temkin's source; the theorem docstring reproduces
all thirteen proof steps of the accepted DAG node, with their dependency IDs. No mathematical
statement, proof plan or proof dependency of the item is changed. `stmt_deps` gains the helper
node and the landed nodes for regular morphisms, ordinary towers/comparisons and regular ring
maps. There is no statement correction and no STATEMENT-DISPUTED flag.

Clause-by-clause correspondence:

- Reduced Noetherian quasi-excellent X and Y: `{X Y : Scheme.{u}}`, `[IsReduced X]`,
  `[IsReduced Y]`, `[IsNoetherian X]`, `[IsNoetherian Y]`, and `hX`, `hY`, each testing
  the recorded `IsQuasiExcellent` on every affine coordinate ring. Mathlib's `IsNoetherian`
  includes quasi-compactness, hence the finite-affine-cover convention, rather than only
  local Noetherianity. No characteristic, separatedness or finite-dimensionality is assumed.
- Regular h: `(h : Y ⟶ X) (hh : IsRegularSchemeMorphism h)`. The exact recorded definition
  is `Flat h` and `IsRegularScheme` of the fibre after every finite extension of the residue
  field. Its fields live in `Type u`, including the original residue field. There is no
  finite-type assumption on h. Thus arbitrary localizations and their base changes, whenever
  in the stated scheme class, are included rather than excluded by a smoothness assumption.
- Reducedness under base change: the first conjunct quantifies over every reduced locally
  Noetherian X-scheme `(T,f)` and asserts `IsReduced (pullback f h)`. This spells out the
  Noetherian setting of the node's proof step 3 without demanding that f be finite type.
- The singular-locus assertion is the literal set equality of nonregular stalk loci with
  inverse image along h. The stalk predicate is the existing `IsRegularLocalRing`.
- A finite ordinary tower R is `OrdinaryBlowupTower X`; its coherence binder uses the full
  recorded `RingedSpace.IsCoherent` on `(R.center i).toModules`, not a replacement predicate.
  `R.unresolvedSet` is exactly the terminal singular image union the singular images of every
  scheme-theoretic center. The conclusion asserts its closedness, existence of a contracted
  pullback tower, and the required equality for every tower equipped with the existing
  `OrdinaryResolutionComparison`. This comparison has cartesian level squares, extended
  center ideals, the retained order, and deletion if and only if the extended ideal is unit.
  Thus it specifies the actual contracted pullback up to its canonical identification,
  rather than choosing arbitrary comparison maps or assuming the unresolved-set equality.
- Z closed with no point below r is `(Z : TopologicalSpace.Closeds X)` and `_lowest` using
  `(r : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x)`. S is precisely
  `X.heightStratum Z r`; `.Finite` and its inclusion into `X.genericPointsIn Z` assert
  the finite set of component generic points. The value r is any natural number, including 0.
- The next set equality identifies the height-r points over Z with the generic points of
  `h ⁻¹' closure S`. Here `genericPointsIn` uses the actual subspace topology on the closed
  subset, so it does not mean the generic points of all of Y.
- C with reduced structure is `(X.reducedClosureIdeal S).subscheme`, using Mathlib's
  `vanishingIdeal` of `closure S`. The equality
  `Y.reducedClosureIdeal (Y.heightStratum (h ⁻¹' Z) r) =
   (X.reducedClosureIdeal S).comap h`
  asserts equality of the defining ideal sheaves of the reduced closure and actual
  scheme-theoretic pullback. `IdealSheafData.comapIso` identifies the right closed subscheme
  with the fibre product. This keeps scheme structure, not just equality of supports.
- At every generic point y of this inverse image the statement records `h y ∈ S`, the
  height equality for Y, and `(h.stalkMap y).hom.IsRegular`. The latter has exactly domain
  `X.presheaf.stalk (h y)` and codomain `Y.presheaf.stalk y`, so no transport or substituted
  local ring is hidden.
- The final clause takes P proper over X, its genuine ideal center J, a reduced
  `J.subscheme`, an arbitrary e, pure codimension of the image of `J.subschemeι ≫ p`, and
  `SchematicallyDenseOverGenericImage` for this map. The canonical fibre product over Y is
  either empty (the stated exception), or reduced and proper over Y, with image of the same
  pure codimension e and the same schematic-density property over its generic image points.
  The centre is the actual pullback of J's closed subscheme; the existing `comapIso` gives
  its standard presentation as a closed subscheme of `P ×_X Y`. Schematic density is the
  injectivity-on-functions formulation in the node: a section with zero germs at every
  point over a generic image point vanishes. It is not merely topological density.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`, sectionwise with
  the existing stalk equivalence.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian` and `IsNoetherian`.
- `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent` (Noetherian, G, J-2).
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`, which is local
  Noetherianity and the upstream stalkwise `IsRegular`.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, the actual glued blowup.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` and its public upstream coherence import:
  `RingedSpace.IsCoherent`; `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`:
  `Scheme.IdealSheafData.toModules`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat` and `Flat.iff_flat_stalkMap`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`; the regular morphism dependency uses exactly these maps.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper` (separated, universally closed,
  locally finite type, with quasi-compactness implied).
- `Sheaf.AlgebraicGeometry.RegularSchemeMorphism`: `IsRegularSchemeMorphism`.
- `Sheaf.AlgebraicGeometry.OrdinaryResolutionRule`: `OrdinaryBlowupTower`, `toBase`,
  `OrdinaryResolutionComparison`. Only these unrestricted interfaces are used; the unrelated
  rational-input/smooth-rule fields add no hypotheses to the statement.
- `WeilConjectures.RingTheory.GRing`: `RingHom.IsRegular`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`, valued in `WithBot ℕ∞`.
- `Mathlib.Topology.Sober`: `genericPoints` on a subspace.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic` and `.Functorial`: `vanishingIdeal`,
  `comap`, `comapIso`. The recorded theorem in
  `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme` justifies the reduced
  induced closed structure. It is publicly imported by the helper module.

All proof-dependency modules having declarations were included as proof imports (the public
statement imports already include the flatness, properness, coherence and dimension modules).
The audit-closed blowup comparison nodes use `WeilConjectures.Blowup.FlatBaseChange`.
`lem-per-quasi-excellent-finite-type-stability` and
`lem-trf-regular-locus-affine-chart-gluing` have no Lean declaration yet and so supply no import;
their full accepted arguments remain in the theorem's thirteen-step docstring. They are proof
prerequisites, not missing notions needed to type the statement.

Edge cases checked against the node and source:

- Empty X or Y: there are no pointwise obligations; empty centers are deleted by the
  existing comparison; the reduced closure and all strata are empty.
- Zero-length tower: the center union is empty; T(R) is exactly the singular locus of its
  only level, transported through the specified initial isomorphism.
- Zero and unit center ideals are permitted; no nonemptiness, nowhere-density, invertibility
  or reducedness is imposed on the arbitrary centers of the unresolved-set assertion.
- Empty S, Z with all component heights greater than r, and r=0 are all included.
- Pure codimension is tested only at generic image points; e=0 and empty center are allowed.
  The final disjunction expressly includes centers that disappear after pullback.
- A projection affine line over a field can increase heights at nongeneric fibre points;
  the theorem asserts height preservation only at the specified lowest/generic stratum.
- A reduced reducible base is allowed. No global dimension bound or equidimensionality of
  the whole base is imposed. Nonreduced centers are allowed in T(R), but the final center
  preservation clause correctly requires its input center to be reduced.

Searches: the exact tool records are in the new node's `mathlib_searches`, copied from the
wrapper's JSONL results, including LeanSearch, LeanFinder, Loogle and Mathlib grep. Queries
covered regular singular-locus pullback, unresolved sets, lowest-height strata, schematic
density and expected names. LeanFinder/LeanSearch supplied only flatness, properness, germs,
smoothness and spreading-out ingredients; no complete theorem or missing helper definition.
Loogle returned no hits for the new combined queries (one attempted scheme-regularity name
was not known to its Mathlib-only index). Mathlib grep for the helper names returned no hits.
Local rg searched the required `WeilConjectures`, `Sheaf`, DAG and upstream-name-index roots.
The source has regular rings and schemes, ordinary towers, generic points, dimension and
vanishing ideals, all reused. The open-only `SchematicallyDenseOpen` and the singular ideal
in `FormalCompletionGeometry` are different notions, not duplicated here. Blueprint searches
for unresolved, equicodimensional and lowest codimension returned zero nodes; the ancestor
query returned `lem-per-artin-gabber-affine-curve`. The node's own source was read at
https://math.huji.ac.il/~temkin/papers/Non_Embedded_Desingularization.pdf, specifically
§§2.1.4--2.1.10, 4.1.1--4.1.3 and the final §4.3 functoriality paragraph.

Validation: each delivered file compiled separately with the prescribed `scompile.py`, both
as a sandbox module and under its library module name, within about 2--3 seconds each. The
first compile found a missing public import for `toModules` and ambiguity of `IsEmpty`'s
coercion from the pullback scheme; both were repaired by the exact public import and an
explicit `: Scheme.{u}` type annotation. No extra mathematical hypothesis was introduced.
Final compiler checks were clean. Both files bind every variable/universe explicitly, use
module mode, contain no local notation or private definitions, and have lines at most 100
characters. The helper definitions have actual data and no postponed proof. The sole sorry
belongs to the item's named theorem with its complete DAG proof in the docstring.

## New nodes

`def-per-resolution-strata`, module `Sheaf.AlgebraicGeometry.ResolutionStrata`, supplies the
notation and definitions required by this node's unresolved-set and lowest-stratum assertion:
`OrdinaryBlowupTower.unresolvedSet`, `Scheme.heightStratum`, `Scheme.genericPointsIn`,
`Scheme.reducedClosureIdeal`, and `Scheme.Hom.SchematicallyDenseOverGenericImage`.
All five are direct formulas over existing towers, rings, generic points, sections, germs and
vanishing ideals. The source is Temkin §§2.1.4--2.1.6, 4.1.1--4.1.3 and §4.3; Stacks 01J3
supplies the reduced-closure construction. The searches above and in the node record found no
existing definition of this package. The new node's statement cites exactly the existing
scheme, tower, regularity, dimension and reduced-induced-closed-subscheme nodes that it uses.
There are no dependency-module repairs.

## Second reading by Q100

The dispatcher explicitly requires one worker, no other agents, and a subsequent independent
maintainer review. This section records the worker's second pass, not an invented independent
reader. I reopened the copied item, helper node and both Lean files. The correspondence above
checks each binder and each conjunct. In particular I checked that center singularity is on
`J.subscheme`, not on its support; the generic points are those of a subspace, not of the
ambient scheme; closure equality is an ideal-sheaf equality; the contracted comparison retains
all nonempty ideals in order; and density uses vanishing germs over generic image points.
The compiled signature has the original reduced/Noetherian/quasi-excellent assumptions,
no finite-type condition on h, and the final reduced-center assumption and empty exception.
Only `lean` and the authorized additions to `stmt_deps` changed on the item. No mismatch with
the mathematical node was found in this pass. The independent review is left to the maintainer
as the worker brief prescribes.

Dry-run repair: the live checker requires `import_flags` on a new definition node
(tools/stage2_delivery.py, added 2026-10-23). Added the required empty list; no mathematical
field or Lean declaration changed.
