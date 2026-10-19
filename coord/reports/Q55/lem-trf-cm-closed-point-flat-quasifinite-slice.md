## Worker report

The module `Sheaf.AlgebraicGeometry.Morphisms.CohenMacaulayClosedPointSlice` states
`AlgebraicGeometry.exists_flat_locallyQuasiFinite_slice_of_closed_fibre_depth_eq_ringKrullDim`.
Its sole theorem has proof `sorry`. No definitions or other nodes are added, and the node
changes only in `lean`.

Read the current node, all nine statement-dependency nodes (including their Lean records or
Mathlib matches), and the corresponding declaration signatures and docstrings. Read Stacks
`more-morphisms.tex`, `lemma-slice-CM` (Tag 0570), lines 6357–6428. The node specializes its
flatness-at-the-point hypothesis to global flatness and forgets the regular-immersion
conclusion, exactly as recorded in its source. The preceding worker's stale-assignment
observation concerned the already reviewed stage-1 split; the present base has no Lean
record for this item, so there is still a stage-2 statement to deliver.

Hypotheses and clauses, in order:

- Schemes and morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Global flatness: `[Flat f]`.
- Local finite presentation: `[LocallyOfFinitePresentation f]`.
- Base point and scheme-theoretic fibre point: `(s : S) (x : f.fiber s)`.
- Closedness in that fibre: `(hx : x ∈ closedPoints (f.fiber s))`.
- The fibre local ring is exactly `((f.fiber s).presheaf.stalk x)`; its Noetherian
  hypothesis is `[IsNoetherianRing ((f.fiber s).presheaf.stalk x)]`.
- Equality of depth and Krull dimension is `hdepth`, with `IsLocalRing.depth` applied to
  this stalk as a module over itself. Its `ℕ∞` value is coerced to `WithBot ℕ∞`, the
  codomain of `ringKrullDim`; this preserves the equality in the node.
- The witnesses are `∃ (Z : Scheme.{u}) (i : Z ⟶ X) (z : (i ≫ f).fiber s)`.
  Thus the structural map of `Z` to `S` is the specified composite, and `z` is a point
  of its actual scheme-theoretic fibre.
- The image clause is `i ((i ≫ f).fiberι s z) = f.fiberι s x`. Both sides are points
  of `X`: this is precisely the node's `i(z) = x`, written with the fibre inclusions.
- Flatness and local finite presentation of the composite are
  `Flat (i ≫ f) ∧ LocallyOfFinitePresentation (i ≫ f)`.
- Exactly one point in the designated fibre is
  `(∀ z' : (i ≫ f).fiber s, z' = z)`; existence is already supplied by the witness `z`.
- The final clause `(i ≫ f).IsLocallyQuasiFinite` uses the dependency's Stacks
  definition, including its local finite-type condition.

Statement dependency declarations used:

| Node | Module | Declaration |
| --- | --- | --- |
| def-pc-scheme | Mathlib.AlgebraicGeometry.Scheme | AlgebraicGeometry.Scheme; Scheme.Hom |
| def-weil-flat-morphism | Mathlib.AlgebraicGeometry.Morphisms.Flat | AlgebraicGeometry.Flat |
| def-sbc-locally-finite-presentation | Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation | AlgebraicGeometry.LocallyOfFinitePresentation |
| def-weil-closed-points | Mathlib.Topology.JacobsonSpace | closedPoints |
| def-pc-scheme-fibre | Mathlib.AlgebraicGeometry.Fiber | Scheme.Hom.fiber; Scheme.Hom.fiberι |
| def-weil-pbc-noetherian-ring | Mathlib.RingTheory.Noetherian.Defs | IsNoetherianRing |
| def-weil-pbc-depth | Sheaf.RingTheory.Depth | IsLocalRing.depth |
| def-weil-pbc-krull-dimension-ring | Mathlib.RingTheory.KrullDimension.Basic | ringKrullDim |
| pqf-def-quasifinite | Sheaf.AlgebraicGeometry.QuasiFiniteMorphism | Scheme.Hom.IsLocallyQuasiFinite |

The closed-point dependency is a Mathlib leaf with no `lean` record; its `mathlib_match`
is `closedPoints`, whose definition at JacobsonSpace.lean:38 is exactly closed singletonhood.
The signatures and docstrings were read at Scheme.lean:35–79, Flat.lean:37–47 and 99–107,
FinitePresentation.lean:42–49, Fiber.lean:37–49, JacobsonSpace.lean:37–43,
Noetherian/Defs.lean:193–206, KrullDimension/Basic.lean:27–31, and the complete project
Depth and QuasiFiniteMorphism modules. No dependency interface repair is needed.

The module also imports the recorded, already stated proof prerequisites: the finite
Noetherian local dimension instance, affine pullback spectra, closed-point dimension,
zero-dimensional quasi-finiteness, open quasi-finite locus, isolation in fibres, open
restriction of local quasi-finiteness, fibre stalk quotient, closed immersions, regular
sequences and the depth/dimension quotient lemma. The only proof prerequisite with no
recorded declaration is `lem-trf-fibre-regular-element-flat-hypersurface`; its import is
omitted until stated. The theorem's docstring reproduces all six node proof steps and
names this pending prerequisite. There is no import cycle.

Edge cases checked before writing: empty `X` or an empty designated fibre has no `x`,
so no unwanted existence conclusion is required. A given fibre point has a nonzero local
ring, so the bottom dimension of the zero ring does not create a missing case. Dimension
zero (including a field stalk) is retained; there is no positivity hypothesis. A singleton
fibre may be nonreduced, and no reducedness or residue-field-isomorphism assumption is
added. The hypotheses require Noetherianity only for the one fibre stalk, not for the
base or whole source. No affine, separated, quasi-compact or immersion condition is
added to the statement. The scheme universe `u` is arbitrary and shared with the
scheme category; the slice exists in that same universe. All variables and universes
are explicit and `autoImplicit` is disabled.

Searches performed in this run (all remote services returned successfully):

- `msearch.py` LeanFinder: “A flat morphism locally of finite presentation has a flat
  locally quasi finite slice through a closed Cohen Macaulay fibre point with singleton
  fibre”. Eight hits, including `UniversallyOpen.of_flat`, `Flat.stalkMap`, and
  `Smooth.flat`; none constructs a Cohen-Macaulay singleton-fibre slice.
- `msearch.py` Loogle: `"Flat", "LocallyQuasiFinite"`. Zero hits.
- `msearch.py` Mathlib grep, AlgebraicGeometry:
  `slice.*(flat|quasi)|CohenMacaulay.*(quasi|flat)|quasi.*CohenMacaulay`. Zero hits.
- `msearch.py` LeanSearch: “Cohen Macaulay closed fibre point flat locally quasi finite
  slice with singleton fibre”. Eight hits, including `LocallyQuasiFinite.mk`,
  `QuasiFinite.iff_finite_comap_preimage_singleton`, and quasi-finiteness constructors;
  none gives this existence theorem.
- `rg` over `WeilConjectures/`, `lean/Sheaf/` and `dag/lean_names_upstream.json` for the
  item id, the proposed theorem name, and the above slicing/Cohen-Macaulay patterns:
  no exact theorem. Upstream `AlgebraicGeometry/Morphisms/Slicing.lean` was read: its
  slice theorem is for smooth morphisms with finite separable residue extension (057G),
  which does not cover a general flat Cohen-Macaulay fibre point. The related
  `CohenMacaulayFibreDimensionNeighbourhood` and `CohenMacaulayFlatQuasiFiniteChart`
  interfaces concern charts over smooth polynomial space, not the singleton-fibre
  slice over the original base, and are not equivalent statements.

Validation: `scompile.py Q55 lem-trf-cm-closed-point-flat-quasifinite-slice` compiled
both its sandbox view and the module at its library path cleanly (2.8 and 1.8 seconds).
No errors or warnings were printed. No statement dispute or correction is needed.

## Second reading by Q55

Independent maintainer second reading, 2026-10-18, of the immutable delivery
`a59d5394d30189cc6c8a283cd93619d1513e59ca`. This section records the actual
independent reading; it replaces the delivered placeholder, which said that no
second reading had occurred. The worker report above is preserved.

I read the packet, the snapshot item and all nine statement-dependency records,
the complete delivered module, the worker report, the exact dependency declarations
and their docstrings. I compared the statement with Stacks more-morphisms.tex
`lemma-slice-CM` (Tag 0570, lines 6357–6428), the surrounding slicing section,
`lemma-slice-given-element` (Tag 056Y, lines 6166 onward), and `definition-CM`
(lines 5816 onward). Local finite presentation implies locally Noetherian fibres,
so the convention preceding the source's Cohen–Macaulay definition adds no missing
hypothesis here. The source assumes flatness at the designated point; the node
explicitly specializes to globally flat f. The node explicitly forgets the regular
immersion conclusion, and the Lean correctly follows that node.

Clause-by-clause reading:

| Node clause | Exact Lean rendering | Verdict |
| --- | --- | --- |
| Schemes and morphism | `{X S : Scheme.{u}} (f : X ⟶ S)` | Exact |
| Global flatness | `[Flat f]` | Exact, via `Flat.iff_flat_stalkMap` |
| Local finite presentation | `[LocallyOfFinitePresentation f]` | Exact affine-local predicate |
| Base point and fibre point | `(s : S) (x : f.fiber s)` | Actual scheme-theoretic fibre |
| Closed fibre point | `hx : x ∈ closedPoints (f.fiber s)` | Closed singleton in the fibre |
| Noetherian fibre local ring | `[IsNoetherianRing ((f.fiber s).presheaf.stalk x)]` | Only that stalk is constrained |
| Depth equals dimension | `hdepth`, using `IsLocalRing.depth` of that stalk over itself, coerced to `WithBot ℕ∞`, equal to `ringKrullDim` of the same stalk | Exact |
| Slice scheme and map | `∃ (Z : Scheme.{u}) (i : Z ⟶ X)` | No extra condition on i |
| Designated slice-fibre point | `z : (i ≫ f).fiber s` | Correct composite and base point |
| Point maps to x | `i ((i ≫ f).fiberι s z) = f.fiberι s x` | Exact equation in X |
| Composite flat and locally finitely presented | `Flat (i ≫ f) ∧ LocallyOfFinitePresentation (i ≫ f)` | Both clauses retained |
| Singleton fibre | `∀ z' : (i ≫ f).fiber s, z' = z` | Existence supplied by z; uniqueness exact |
| Locally quasi-finite composite | `(i ≫ f).IsLocallyQuasiFinite` | Stacks predicate including finite type |

The exact declarations read were Mathlib `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
`Flat` and `Flat.iff_flat_stalkMap`, `LocallyOfFinitePresentation`,
`Scheme.Hom.fiber`, `fiberι`, `fiberHomeo`, `closedPoints`, `IsNoetherianRing`,
`isNoetherianRing_iff_ideal_fg`, and `ringKrullDim`; and the side-project
`Ideal.depth`, `IsLocalRing.depth`, `Scheme.Hom.IsQuasiFiniteAtPoint`,
`Scheme.Hom.IsLocallyQuasiFinite`, and `Algebra.IsQuasiFiniteAtPrime`.
Depth is the real regular-sequence supremum construction, not an arbitrary
predicate. Quasi-finiteness uses actual affine appLE maps and the canonical fibre
prime. No duplicate definition or private replacement occurs in this delivery.

I checked all six proof-plan paragraphs against the node: finite local dimension
and strong induction with depth at least dimension; affine zero-dimensional
quasi-finiteness; open quasi-finite locus and open singleton restriction; lifting
a fibre regular element and applying 056Y; the quotient/localization computation;
and depth/dimension descent followed by induction and composition. The existing
closed-point dimension, zero-fibre-dimension quasi-finiteness, open-locus,
isolation, open-restriction, fibre-stalk quotient, and depth-quotient modules were
also inspected. The report's omitted `lem-trf-fibre-regular-element-flat-hypersurface`
is an already existing statement-only proof dependency (its node was read in the
read-only group clone), not a missing object needed to type this statement.
No canonical map, definition, universe transport, or statement prerequisite is
missing. Its future proof implementation does not prevent this stage-2 statement.

Edge cases: empty source or empty designated fibre admits no x; an inhabited
scheme stalk is a nonzero local ring, so the zero ring's bottom Krull dimension
is irrelevant. Dimension zero and nonreduced Artinian fibre stalks remain allowed.
No smoothness, reducedness, perfectness, separability, residue-field equality,
positive dimension, affine base, separatedness, quasi-compactness, or global
Noetherianity was added. Characteristic is unrestricted. Universe u is arbitrary;
all schemes are in the same scheme category, with no extra universe equation.
All binders are bound, and `autoImplicit` is false.

Independent searches used different phrasing: LeanSearch, “A regular immersion
through a Cohen Macaulay closed point of a fibre produces a flat morphism with
singleton fibre”, returned flatness definitions/constructors, flat open restrictions,
and immersion results, but no slicing existence theorem. Loogle
`"Flat", "IsLocallyQuasiFinite"` returned zero declarations. Direct rg searches for
`0570`, `slice.CM`, Cohen–Macaulay slicing, and the theorem name over pinned Mathlib,
slopmaster2 WeilConjectures and the group's lean/Sheaf found no exact match.
I opened upstream `Smooth.exists_etale_comp_of_etale_residueFieldMap` (057G):
its smoothness and finite separable residue-extension hypotheses exclude it as a
match. I also opened `exists_flat_quasiFinite_chart_of_fibre_depth_eq_ringKrullDim`
and the constant-fibre-dimension neighbourhood theorem: they give charts over
smooth models or dimension neighbourhoods, not the required singleton-fibre
slice over S.

The module and theorem docstrings have the correct source and blueprint markers;
the theorem docstring includes every node proof step. The sole local theorem has
exactly `by sorry`, and the delivery introduces no definitions. There are no lines
over 100 characters. I compared `lean.statement` programmatically with the exact
source substring from `theorem` up to `:=`: they are verbatim equal. No statement
correction or dependency-record repair is needed.

The current `origin/newtargets-dag:coord/route-pivot-dropped.txt` was read and
intersected with all direct statement/proof dependencies: no intersection. There
is no repair note for this item at the prescribed repair-note path. This delivery
contains no dropped infinity/dg/model-category machinery or pro-etale substitute.

Compiler reproduction on 2026-10-18:

`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q55 lem-trf-cm-closed-point-flat-quasifinite-slice snapshot/lean/Sheaf/AlgebraicGeometry/Morphisms/CohenMacaulayClosedPointSlice.lean`

Exit 0. The currently installed wrapper uses the server's persistent side overlay;
it compiled the sandbox `Sheaf/Stage2/Sandbox0.lean` in 2.2 seconds and the exact
library module in 7.0 seconds, with no diagnostics. No direct SSH command, global
build, lake build, live Lean edit, delivery, or Git mutation was performed.

Finding and correction: H11, with the report-content requirement of H1, was the
placeholder second-reading section. This complete report supplies the independent
reading and compiler evidence. No Lean, node, or mathematical change was needed.
