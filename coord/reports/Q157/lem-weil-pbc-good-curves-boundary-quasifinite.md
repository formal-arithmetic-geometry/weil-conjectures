## Worker report

The module `Sheaf.AlgebraicGeometry.GoodCurvesBoundaryQuasiFinite` states
`AlgebraicGeometry.good_curves_boundary_quasiFinite`, with its entire proof `sorry`.
It also supplies the concrete canonical composite `AlgebraicGeometry.goodCurvesBoundaryMap`:
the inclusion of the subscheme cut out by the vanishing ideal of the closed complement,
followed by `Sigma.desc (fun i ↦ b i ≫ t i)`. This helper introduces neither an arbitrary map
nor an existence choice, and its data contains no postponed proof. It is listed in
`lean.declarations` under the owning item's blueprint tag. No new node, dependency repair,
or statement correction is needed.

Clause-by-clause correspondence:

- The base scheme is `(B : Scheme.{u})`. The exact Noetherian convention in the node is
  `[IsLocallyNoetherian B] [CompactSpace B]`, with compactness meaning quasi-compactness
  of the underlying space; no separatedness, affineness or dimension bound on B is assumed.
- A finite set is `{I : Type u} [Finite I]`. No nonemptiness or enumeration is required.
  All finite index sets can be represented in the scheme universe; all scheme and fibre
  universes and all variables are bound explicitly.
- `T C O : I → Scheme.{u}` bind precisely the three families of schemes.
  `t : ∀ i, T i ⟶ B`, `b : ∀ i, C i ⟶ T i`, and `u : ∀ i, O i ⟶ C i`
  are the three specified families of arrows.
- Finite etaleness of each `t i` is the pair `[∀ i, IsFinite (t i)]` and
  `[∀ i, Etale (t i)]`. The dependency's finite-etale category is the subcategory of
  the over-category cut out by these two properties; only its object condition is
  used here, so no new category or specialized copy is introduced.
- Smoothness and properness of each `b i` are `[∀ i, Smooth (b i)]` and
  `[∀ i, IsProper (b i)]`.
- The three ordinary-fibre hypotheses are exactly the three conjuncts of `hC`:
  `Nonempty ((b i).fiber s)`,
  `GeometricallyConnected ((b i).fiberToSpecResidueField s)`, and
  `topologicalKrullDim ((b i).fiber s) ≤ 1`. The connectedness is geometric over
  the actual residue field, not merely connectedness of the underlying fibre.
- The open immersions are `[∀ i, IsOpenImmersion (u i)]`. The open fibre hypothesis
  `hO` says `Nonempty ((u i ≫ b i).fiber s)` for every `i` and `s : T i`.
  It is a hypothesis on the fibre over T_i, not only over B.
- `C = ∐ C` is the existing scheme coproduct, with coprojections `Sigma.ι C i`.
  The image of the open coproduct `∐ O → ∐ C` is exactly the open union
  `⨆ i, (u i ≫ Sigma.ι C i).opensRange`. This expression uses the canonical
  components of that coproduct map, and does not replace the open by a dense subopen.
- The complement is the bundled closed set obtained by `.compl` of that open union.
  `Scheme.IdealSheafData.vanishingIdeal` and its `.subscheme` give precisely
  `(C \ O)_red`; `.subschemeι` is its closed inclusion. The recorded reduced-induced
  theorem identifies this construction with the unique reduced closed subscheme
  of that image. No reduction/base-change commutation is assumed.
- The induced map Z → B is exactly `goodCurvesBoundaryMap B T C O t b u`.
  `IsSeparated` is the first conclusion; the second conclusion uses the recorded
  `Scheme.Hom.IsQuasiFinite`, including finite type and isolated fibre points.
- The final three conjuncts are `LocallyOfFinitePresentation`, `QuasiCompact` and
  `QuasiSeparated` of this same map, exactly the Stacks 01TP finite-presentation
  convention of `def-weil-pbc-scheme-conventions`. There is no extra finiteness
  conclusion, although the proof plan first obtains properness.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`; the node's
  Noetherian condition is the two displayed instances rather than a new predicate.
- `def-weil-pbc-scheme-conventions` is explicitly a convention-only node and has no
  declaration or module; finite presentation is written as its specified conjunction.
- `Mathlib.CategoryTheory.MorphismProperty.Comma` and `.OverAdjunction`:
  `MorphismProperty.Over` and `Over.pullback` are the finite-etale-category match.
  They define the category generally; here the relevant object data uses the existing
  `IsFinite` and `Etale` of `Mathlib.AlgebraicGeometry.Morphisms.Finite` and `.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` and `.Separated`: `IsProper`, `IsSeparated`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberToSpecResidueField`.
- `Mathlib.AlgebraicGeometry.Geometrically.Connected`: `GeometricallyConnected`, the
  connected variant explicitly recorded by `def-pc-geometrically-irreducible`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion` and `Scheme.Hom.opensRange`.
- `Mathlib.AlgebraicGeometry.Limits`: `sigmaOpenCover`, coproducts, and their
  `Sigma.ι` / `Sigma.desc` maps from the recorded coproduct-family match.
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme`.
  Its current source was read using `scompile.py --source` because the older upstream
  source checkout lacks this file. The construction is the existing
  `Scheme.IdealSheafData.vanishingIdeal` (`Mathlib.AlgebraicGeometry.IdealSheaf.Basic`)
  and `subscheme` / `subschemeι` (`Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`).
- `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`: `Scheme.Hom.IsQuasiFinite`.
  Its full definition was read: it requires locally finite type, quasi-compactness,
  and every singleton open in its fibre; the weaker bare Mathlib local predicate
  is not used as a replacement.

The proof-only imports preserve the recorded plan: `SmoothFiber`,
`GeometricRegularitySmoothFieldCriterion`, the upstream topological `KrullDimension`,
`FiniteOfIsClosedOfClosedPoints`, and upstream `ProperQuasiFinite`. The other stated
proof dependencies are supplied by the public geometry imports. `rem-pc-regular-normal`
has no recorded declaration and is mentioned in the proof plan without inventing one;
it is not needed to type the statement. There is no import cycle.

Sources checked locally: Stacks `more-etale.tex`, Tag 0GKX, second localization
triangle and second boundary Zprime; `more-morphisms.tex`, Tag 0GK7 clauses (4)-(8).
These agree with the item's hypotheses. The source theorem's coefficient and
cohomological hypotheses belong to its parent, not to this independent geometric
boundary assertion. The declaration docstring gives all seven steps of the node's
proof, including the ordinary-fibre regularity argument over arbitrary residue fields.

Edge cases checked mathematically:

- Empty I: the coproduct and boundary are empty; all fibre hypotheses are vacuous.
- Empty B: any T_i and C_i mapping to it are empty; the conclusions still hold.
- Empty T_i: its component contributes nothing, with no impossible nonemptiness binder.
- O_i = C_i: its boundary is empty. Empty O_i over a nonempty T_i fails `hO`, as required.
- Dimension-zero fibres: a nonempty open of the irreducible smooth connected fibre is
  the entire fibre. The condition is `≤ 1`, never an equality or a dimension-one class.
- A proper smooth geometrically connected curve with finitely many points removed
  has a finite boundary in each fibre. Dropping `hO` would allow an entire curve
  as boundary, so `hO` is substantive. No algebraic closure or perfection is assumed.

Searches (the preserved sandbox `searches.jsonl` records the interrupted turn's calls):

- `msearch.py`, LeanFinder: `quasi-finite boundary complement open every fibre proper
  smooth geometrically connected curve`: eight results, principally
  `Scheme.Hom.coborderRange`, `LocallyQuasiFinite`, and finite/proper-map facts;
  none states this boundary assertion.
- `msearch.py`, Loogle: `AlgebraicGeometry.Scheme.Hom.IsQuasiFinite IsProper Smooth
  GeometricallyConnected`: no results, with the tool reporting the project-specific
  quasi-finite name unknown to its Mathlib index. The recorded project predicate
  was then opened directly, as required.
- `msearch.py`, grep: `isOpenImmersion_sigmaDesc|topologicalKrullDim.*fiber|IsQuasiFinite`
  in Mathlib/AlgebraicGeometry: no indexed hits for a matching statement.
- Direct `rg` of upstream `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for good-curves / boundary-quasi-finite patterns:
  only unrelated boundary statements and the existing good-curves diagram/consumer;
  no existing theorem stating this item and no declaration-name collision.
- Direct upstream grep of the exact blueprint id found no declaration.
  The existing `GoodCurvesGenericDiagram` was opened: it constructs the diagram,
  not the boundary conclusion, so is not an existing match for this node.

Validation: prescribed `scompile.py` compiled the sandbox and library-path module
cleanly, separately, in 2.6 and 2.8 seconds. No compiler errors or warnings occurred.
The source has no `#check`, no auto-bound implicits, no local instances or notation,
no theorem proof except `sorry`, and no lines exceeding 100 characters.
No STATEMENT-DISPUTED flag or node fault.

## Second reading by Q157

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
