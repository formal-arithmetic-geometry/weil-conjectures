## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothOpenSchematicGenericDensity` states
`AlgebraicGeometry.Scheme.Hom.smoothOpen_schematicGenericDensity`. Its sole theorem
has proof `sorry`; no definitions or extra theorems are introduced. The statement
is unchanged. The existing, landed definition node
`def-trf-schematically-dense-open` is added to `stmt_deps` to use its exact predicate.

Hypotheses and objects, clause by clause:

- Schemes and morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
- Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`, the recorded conjunction.
- Flatness: `[Flat f]`.
- Local finite presentation: `[LocallyOfFinitePresentation f]`.
- Irreducible base: `[IrreducibleSpace Y]`, which includes nonemptiness.
- Specified generic point: `(η : Y) (hη : IsGenericPoint η Set.univ)`.
- Geometrically reduced generic fibre:
  `[GeometricallyReduced (f.fiberToSpecResidueField η)]`.
- The union U of all smooth restrictions is the existing `f.smoothLocus`.
  This identification follows from `Scheme.Hom.preimage_smoothLocus_eq` and
  `Scheme.Hom.smoothLocus_eq_top_iff`: restriction to an open T is smooth
  exactly when T is contained in the locus. The locus itself has smooth
  restriction, so it is exactly the union, including the empty union case.
- The fibre U_y is represented canonically as the open
  `(f.fiberι y) ⁻¹ᵁ f.smoothLocus` in `f.fiber y`. Its inclusion followed by
  `f.fiberToSpecResidueField y` is its structure morphism over κ(y).
  Base change of an open subscheme is precisely this inverse-image open;
  no arbitrary identification or map is assumed.

Conclusions, clause by clause:

- Generic topological density is the first conjunct, `Dense` of that open
  as a `Set (f.fiber η)`.
- Injectivity of the generic structure sheaf map is the second conjunct,
  `SchematicallyDenseOpen ((f.fiberι η) ⁻¹ᵁ f.smoothLocus)`.
  This is the recorded definition, not a substitute for schematic density:
  for every ambient open W it asserts injectivity of the restriction from W
  to W intersected with U_η, exactly the map to the open pushforward.
- For every y, finite type over κ(y) is the conjunction
  `LocallyOfFiniteType (f.fiberToSpecResidueField y)` and
  `QuasiCompact (f.fiberToSpecResidueField y)`.
- Noetherianity of the underlying topological space is
  `TopologicalSpace.NoetherianSpace (f.fiber y)`. This is ACC on opens,
  equivalently DCC on closed subsets, equivalently eventual stabilization
  of descending sequences of closed subsets (classically). It imposes no
  Noetherian assumption on the original base.
- Every open immersion into the fibre is quantified as
  `∀ (T : Scheme.{u}) (j : T ⟶ f.fiber y), IsOpenImmersion j → ...`,
  with conclusion `QuasiCompact j ∧ QuasiSeparated j`. This covers arbitrary
  domains and not merely affine opens.
- The final conjunct is geometric reducedness of the structure morphism
  of the canonical inverse-image open for every y. This is precisely
  geometric reducedness of U_y over κ(y).

Dependency declarations read and used (the import paths below are module names):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; the recorded finite-type conjunction
  also uses `AlgebraicGeometry.QuasiCompact` from
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` (publicly imported there).
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.Topology.Irreducible`: `IrreducibleSpace`, `IsIrreducible`, and the
  recorded `irreducibleComponents`; only irreducibility is used here.
- `Mathlib.Topology.Sober`: `IsGenericPoint`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `Scheme.Hom.fiberι`,
  `Scheme.Hom.fiberToSpecResidueField`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`: public access to
  `AlgebraicGeometry.GeometricallyReduced`, from the recorded dependency's
  declaration list and its imported `Geometrically.Reduced` module.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`,
  `Scheme.Hom.smoothLocus`, `Scheme.Hom.preimage_smoothLocus_eq`,
  `Scheme.Hom.smoothLocus_eq_top_iff`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `AlgebraicGeometry.QuasiSeparated`.
- `Sheaf.TraceFormula.SchematicallyDenseOpen`:
  `AlgebraicGeometry.SchematicallyDenseOpen`.
- `Mathlib.Topology.NoetherianSpace`: `TopologicalSpace.NoetherianSpace`.

Proof dependency modules are imported nonpublicly: Mathlib's
`AlgebraicGeometry.Noetherian`, `Morphisms.Separated`,
`Morphisms.SchemeTheoreticallyDominant`, `IdealSheaf.Subscheme`, and
`WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced`.
The remaining proof dependencies are already supplied by the statement imports
(FiniteType/QuasiCompact and Smooth/Basic). The theorem docstring carries all
five proof steps and their DAG references. No proof import cycle was found.

Sources checked: local Stacks `more-morphisms.tex`,
`lemma-geometrically-reduced-generic-fibre` (0578), proof paragraph 2;
`varieties.tex`, `lemma-geometrically-reduced-dense-smooth-open` (056V);
`morphisms.tex`, `lemma-reduced-scheme-theoretically-dense` (056D).
The source explicitly gives generic density, schematic density and geometric
reducedness of the smooth-open fibres. Fibre Noetherianity follows from finite
type over residue fields as in the node's proof.

Edge cases checked before writing: X may be empty; the generic fibre and any
special fibre may be empty; U may be empty. Density in an empty generic fibre
holds, its sheaf restriction maps are maps between singleton rings, and empty
fibres remain reduced after every field extension. The base is irreducible and
nonempty as assumed, but may be nonreduced and need not be Noetherian. No
perfectness hypothesis on residue fields is imposed. All schemes and residue
fields use the same explicit arbitrary universe u, as in the recorded fibre
and geometric-reducedness APIs; open-immersion domains have that same universe.
No hypotheses or clauses have been added or removed. No statement fault or
STATEMENT-DISPUTED flag was found.

Searches for reuse:

- `msearch.py leanfinder`, query “For a flat finite type locally finitely
  presented morphism with geometrically reduced generic fibre the smooth locus
  has schematically dense generic fibre and geometrically reduced fibres”:
  8 hits, concerning smoothness, the algebraic smooth locus and relative
  dimension; none states this combined result.
- `msearch.py loogle`, query
  `AlgebraicGeometry.Scheme.Hom.smoothLocus, AlgebraicGeometry.GeometricallyReduced`:
  0 hits.
- `msearch.py grep`, query `smoothLocus|[Ss]chematicallyDense` in AlgebraicGeometry:
  found the existing Mathlib smooth locus and density over perfect fields,
  not the complete theorem.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, queries
  `schematic.*generic.*density|smooth_open_schematic|smoothOpenSchematic` and
  the item's exact id: no full statement match; hits concern other uses of
  schematic generic density. Searches of `smoothLocus` found the existing
  generic-fibre density and fibre-to-source smoothness tools.
- Mathlib source was read for all the signatures above, including the
  smooth-locus characterization and `NoetherianSpace` definition.

Validation: compile every delivered module using the prescribed `scompile.py`
server wrapper. An initial namespace error on `NoetherianSpace` was repaired by
writing its full name `TopologicalSpace.NoetherianSpace`. Final compile and
preflight results are recorded below after those commands complete.

Final validation: `scompile.py Q53 lem-trf-smooth-open-schematic-generic-density`
passed for the delivered module in both sandbox mode (9.3 s) and its actual
library module mode (4.4 s), with no errors or warnings. The `deliver2.py --no-push`
dry run passed the live server preflight and per-file compilation. Additional
exact-id grep of `lean/WeilConjectures` and name lookup in
`dag/lean_names_upstream.json` found no existing declaration for the full item.

## Second reading by Q53

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
