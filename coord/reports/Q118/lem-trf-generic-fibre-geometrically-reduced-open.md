## Worker report

The module `Sheaf.AlgebraicGeometry.GenericFibreGeometricallyReducedOpen` states
`AlgebraicGeometry.exists_nonempty_open_geometricallyReduced_fiber_of_generic`.
Its sole theorem proof is `sorry`; no definition, axiom, helper, or second copy of a notion
is introduced. The node is unchanged except for its `lean` record.

Source read: Stacks Project, `more-morphisms.tex`, Tag 0578,
`lemma-geometrically-reduced-generic-fibre`, statement and proof (lines 7214–7256).
The node agrees with all three source assumptions and its conclusion.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes and their morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
- Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the two properties
  recorded by `def-weil-finite-type-morphism`.
- Irreducible base: `[IrreducibleSpace Y]`. This includes nonemptiness, as the node's
  irreducibility definition requires.
- Specified generic point: `(η : Y) (hη : IsGenericPoint η Set.univ)` means that
  the closure of `{η}` is all of `Y`; it does not choose a different generic point.
- Geometrically reduced generic fibre over its residue field:
  `(hgeneric : GeometricallyReduced (f.fiberToSpecResidueField η))`.
  The map has domain `f.fiber η` and codomain `Spec (Y.residueField η)`.
- An open subset of the original base: `∃ V : Y.Opens`.
- Its required nonemptiness: `(V : Set Y).Nonempty`.
- Every fibre at a point of that open is geometrically reduced over its own residue field:
  `∀ y : Y, y ∈ V → GeometricallyReduced (f.fiberToSpecResidueField y)`.
- The last sentence excludes extra assumptions: there are no flatness, reduced-base,
  Noetherianity, nonempty-source or nonempty-fibre hypotheses in the signature.

Statement dependency interfaces read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`; and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`.
- `def-weil-irreducible-components`: the `mathlib_match` points to
  `Mathlib.Topology.Irreducible`; its `IrreducibleSpace` class is the node's
  irreducibility of the entire underlying space. No dependency-record repair is needed.
- `def-sc-generic-point`: `Mathlib.Topology.Sober`, `IsGenericPoint`.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`,
  `AlgebraicGeometry.Scheme.Hom.fiber` and
  `AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField` (the canonical second projection).
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField`.
- `def-pc-geometrically-irreducible`: its recorded module
  `Mathlib.AlgebraicGeometry.Geometrically.Integral` exports the required
  `AlgebraicGeometry.GeometricallyReduced`. Its definition and docstring were read in
  `Mathlib.AlgebraicGeometry.Geometrically.Reduced`. The equivalence
  `geometrically_iff_of_commRing` in `Geometrically.Basic` verifies that its specialization
  to a field spectrum is precisely reducedness after every field extension.

The proof docstring reproduces all eight node proof steps, including reduction of the
base, generic flatness, finiteness of fibre covers, density of the smooth locus,
schematic density on the generic fibre, spreading schematic density, preservation under
field-extension flat base change, and the final nilpotent-section argument. Stated proof
modules are imported without `public`. In particular the existing upstream smooth-fibre,
dense-smooth-locus, and flat schematic-image declarations are used, not redefined.
`lem-trf-schematic-density-generic-fibre-open` has no Lean record or Mathlib match on the
read base, so there is no recorded module to import for that proof-only dependency; the
proof explicitly names the node. It is not needed to type this statement.
The reduction theorem's local source was missing, so its actual current source and complete
signature/docstring were read with `scompile.py --source` as required.

Edge cases checked before writing:

- An empty source or an empty generic fibre is allowed: geometric reducedness is reducedness
  after field base change, and the empty scheme is reduced. No nonemptiness is inferred for
  any fibre. The conclusion remains about all points of `V`.
- An empty base is excluded by the explicit irreducibility assumption, not by a new premise.
- Nonreduced and non-Noetherian irreducible bases remain covered; the source proof passes
  through reduction and generic flatness, while the theorem's signature imposes neither.
- No separation or quasi-separatedness assumption on `f` is added. Finite type means the
  two recorded properties and not finite presentation.
- `u` is explicit, all variables are bound, and auto-implicit binding is disabled. No
  independent small universe is introduced for geometric field-extension tests.

Searches for an existing declaration:

- `msearch.py grep` query `geometrically.reduced.*generic|generic.*geometrically.reduced`: 0 hits; no generic geometric-reducedness spreading declaration.
- `msearch.py loogle` query `"GeometricallyReduced"`: 12 hits; definitions or reducedness/base-change facts, no exact spreading theorem.
- `msearch.py leanfinder` query `A finite type morphism of schemes over an irreducible base with geometrically reduced generic fibre has geometrically reduced fibres over a nonempty open subset`: 8 hits; definitions or reducedness/base-change facts, no exact spreading theorem.
- `msearch.py leansearch` query `Geometric reducedness of the generic fibre of a finite type morphism spreads to a nonempty open subset of an irreducible scheme`: 8 hits; definitions or reducedness/base-change facts, no exact spreading theorem.
- `rg` of the upstream `WeilConjectures` tree for generic geometric reducedness:
  no exact theorem; the direct item-id search also has no hits.
- `rg` of `lean/Sheaf` for generic geometric reducedness finds preparation/modification
  statements, and `GenericConstancyGeometricReducedness` (a stronger finite-presentation
  hypothesis and an equivalence of generic/fibre status), whose proof explicitly cites this
  item. None is this node's finite-type positive-case statement; using that consumer as a
  dependency would reverse the proof DAG.
- The proposed theorem name and item id were checked against the upstream declaration-name
  index, Mathlib, upstream sources and `lean/Sheaf`; the proposed name is unused.

Validation: `scompile.py Q118 lem-trf-generic-fibre-geometrically-reduced-open` on the
single delivered module returned exit code 0, with no errors or warnings. The wrapper
checked both sandbox and library module contexts. The JSON signature is extracted verbatim
from the theorem keyword through the end of the signature, before `:=`.

No statement correction, disputed statement, new node, or dependency module is needed.

## Second reading by Q118

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
