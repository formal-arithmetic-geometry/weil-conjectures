## Worker report

The module `Sheaf.AlgebraicGeometry.RegularMorphismAffineCriterion` states
`AlgebraicGeometry.isRegularSchemeMorphism_iff_regular_appLE`, with its sole proof
`sorry`. No definitions, new nodes, dependency repairs, or statement corrections are needed.
The item copy changes only `lean`.

The statement matches the node as follows:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Schemes X and Y | `{X Y : Scheme.{u}}` |
| Both schemes locally Noetherian | `[IsLocallyNoetherian X] [IsLocallyNoetherian Y]` |
| A morphism f : X → Y | `(f : X ⟶ Y)` |
| f is regular | `IsRegularSchemeMorphism f` |
| If and only if | `↔` |
| Every open U in X and V in Y | `∀ (U : X.Opens) (V : Y.Opens)` |
| U and V affine | `IsAffineOpen U → IsAffineOpen V →` |
| f(U) contained in V | `∀ (h : U ≤ f ⁻¹ᵁ V)` |
| The canonical map from O_Y(V) to O_X(U) | `(f.appLE V U h).hom` |
| Each such map is regular | `RingHom.IsRegular (f.appLE V U h).hom` |

The definition of `Scheme.Hom.appLE` in Mathlib is literally `f.app V` followed
by the restriction along `U ≤ f ⁻¹ᵁ V`. Thus this is the particular map in the
node, with the ring-map direction from target sections to source sections; no
arbitrary algebra structure or choice of ring map appears. The regular-ring-map
predicate receives this bare ring homomorphism, and internally provides its
canonical algebra structure. No applied instance lambda is needed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom`, and `Scheme.Hom.appLE`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.RegularSchemeMorphism`:
  `AlgebraicGeometry.IsRegularSchemeMorphism`. This is the flatness plus
  regularity of scheme fibres after every finite extension of their residue fields.
- `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`:
  `AlgebraicGeometry.LocallyRingedSpace.Hom`; scheme morphisms inherit this
  structure, including the underlying structure-sheaf map. It is already exposed
  through the scheme imports.
- `WeilConjectures.RingTheory.GRing`: `RingHom.IsRegular` and its underlying
  `Algebra.IsGeometricallyRegular`. Its fibre Noetherian condition is included,
  so this does not silently replace regularity by a weaker fibre condition.

The three public imports expose all the statement dependencies. The proof imports
also include `Mathlib.AlgebraicGeometry.ResidueField`,
`Mathlib.AlgebraicGeometry.Pullbacks`, and
`WeilConjectures.RingTheory.FibreRingNoetherian`, for the recorded residue-field
identification, open/affine fibre-product formulas, and `Ideal.isNoetherianRing_fiber`.
The flat affine criterion `AlgebraicGeometry.flat_iff` is exposed by the regular
scheme-morphism import. The proof dependency
`lem-per-geometric-regularity-affine-cover` has no recorded declaration/module at
this reading, so there is no module for it to import. Its role in both directions
is included in the full natural-language proof docstring, following all three
proof steps of the item.

Source checked: local `literature/stacks-project/more-morphisms.tex`,
`lemma-regular`, Tag 07R8, including its complete statement and proof. Conditions
(2) and (3) are exactly the equivalence here. The node's locally Noetherian source
ensures the source lemma's locally Noetherian fibre hypothesis: its affine fibre
rings are localizations followed by quotients of Noetherian source chart rings.
The locally Noetherian target is retained because it is expressly in the node.

Edge cases checked before writing:

- Empty X: flatness and the fibre regularity tests hold, and its affine chart
  maps have the zero target ring with zero fibres; neither side excludes this case.
- Empty Y: any morphism into it has empty X, reducing to the preceding case.
- Empty affine opens U or V: the quantified opens include them; if V is empty,
  the containment forces U empty. Zero rings and empty schemes are allowed by
  the imported predicates.
- Identity maps, including singular locally Noetherian schemes: the condition
  concerns the regularity of the morphism, not of the source scheme itself.
- A finite purely inseparable nontrivial extension of fields in positive
  characteristic: the morphism is flat but fails geometric regularity, so merely
  having regular ordinary fibres would not suffice; both imported predicates
  retain the geometric tests.
- There is no finite type, finite presentation, surjectivity, nonemptiness, or
  affine-global assumption. The single universe is the scheme-category universe
  already used by the dependency, and all opens are quantified without a size cut.

Searches for an exact existing statement (2026-10-24):

- `msearch.py ... leanfinder`: “A morphism of locally Noetherian schemes is
  regular if and only if every induced ring map on affine open charts is regular”.
  Eight hits, including `HasRingHomProperty.iff_appLE`, `affineLocally`, and
  `locallyOfFiniteType_iff`; none supplies the regular scheme/ring correspondence.
- `msearch.py ... loogle`: `AlgebraicGeometry.flat_iff, RingHom.IsRegular`.
  Zero hits, with unknown identifier `RingHom.IsRegular` in the external service.
  The latter's actual project definition was read directly in GRing.lean.
- `msearch.py ... leansearch`: “A morphism of locally Noetherian schemes is
  regular if and only if every affine coordinate ring map is regular”. Eight
  hits, concerning locally Noetherian schemes, smoothness and finite type; no
  exact match.
- `msearch.py ... grep`: `IsRegularMorphism|RegularMorphism|IsRegularSchemeMorphism|geometrically.?regular`
  in Mathlib/AlgebraicGeometry: zero hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`:
  `regular.*iff|IsRegularSchemeMorphism|IsRegular.*appLE` found the existing
  regular morphism definition and its consumers and unrelated regularity lemmas,
  but no chart criterion. `grep -rn` for the item's exact id in
  `lean/WeilConjectures` returned no hits.
- `rg` for `IsRegularSchemeMorphism|regular_appLE|IsRegularMorphism|RegularMorphism`
  in `dag/lean_names_upstream.json` and Mathlib/AlgebraicGeometry found no hits.
  The new theorem's name is absent from these sources and both project trees.

Validation: `scompile.py Q145 lem-per-regular-morphism-affine-criterion` on the
module succeeded in both sandbox and library modes (1.7 s and 1.5 s), with no
errors or unexpected warnings. All universes and binders are explicit, with
both auto-implicit options disabled. No node fault or statement dispute was found.

## Second reading by Q145

Self-check with the node and completed module open: X and Y have both required
Noetherian assumptions; the conclusion uses the recorded geometric regularity
predicate and a genuine equivalence. The opens range over all opens, with both
affineness hypotheses and the containment proof before the ring-map conclusion.
The order `f.appLE V U h` is target first, source second, giving exactly
O_Y(V) → O_X(U). There is no affine-global or finite-presentation restriction,
and empty opens remain included. No mismatch or change was found. This is the
worker's rereading, not a claim of independent review; the dispatch brief reserves
the independent reading for the maintainer and prohibits starting other agents.
