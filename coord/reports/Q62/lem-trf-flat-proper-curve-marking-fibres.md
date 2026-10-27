## Worker report

The module `Sheaf.AlgebraicGeometry.FlatProperCurveMarkingFibres` states
`AlgebraicGeometry.flat_proper_curve_marking_fibres`. Its sole theorem has proof `by sorry`;
there are no new definitions, helper axioms, or dependency repairs.

Hypotheses, read against the node:

- Integral base and its generic point: `{T X Z : Scheme.{u}} [IsIntegral T]`,
  `(η : T) (hη : IsGenericPoint η (Set.univ : Set T))`.
- The morphism `f : X ⟶ T` is proper and flat by `[IsProper f] [Flat f]`.
  Its finite presentation is all three conditions explicitly:
  `[LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]`.
  This follows the node's convention, including quasi-separatedness.
- The marking is `(i : Z ⟶ X) [IsClosedImmersion i]`. Its structure map is exactly
  `i ≫ f`, never an independently chosen morphism. Its flatness and finite presentation
  are `[Flat (i ≫ f)]`, `[LocallyOfFinitePresentation (i ≫ f)]`,
  `[QuasiCompact (i ≫ f)]`, `[QuasiSeparated (i ≫ f)]`.
- Both generic fibres are dense through their canonical first projections:
  `hXdense : Dense (Set.range (f.fiberι η))` and
  `hZdense : Dense (Set.range ((i ≫ f).fiberι η)))` (the extra final parenthesis
  here closes the hypothesis binder in the file).
- The generic curve is nonempty and irreducible by `[IrreducibleSpace (f.fiber η)]`:
  Mathlib's irreducible-space class includes nonemptiness. Its Krull dimension is
  `hXdim : topologicalKrullDim (f.fiber η) = (1 : WithBot ℕ∞)`.
- The generic marking is finite etale through its canonical residue-field projection:
  `[IsFinite ((i ≫ f).fiberToSpecResidueField η)]` and
  `[Etale ((i ≫ f).fiberToSpecResidueField η)]`. There is no nonempty hypothesis
  for this fibre or for `Z`.

Conclusion clauses:

- Surjectivity is `Surjective f`.
- For every `t : T`, field `Ω : Type u`, algebra structure over `T.residueField t`,
  and `[IsAlgClosed Ω]`, the geometric fibre is the actual scheme pullback
  `pullback (C := Scheme.{u}) (f.fiberToSpecResidueField t)
  (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)))`.
  Its `Nonempty` and `.IsPureDimension 1` form the first universal conjunct.
  These are arbitrary algebraically closed extensions, not only algebraic closures.
- `IsFinite (i ≫ f) ∧ Flat (i ≫ f) ∧ LocallyOfFinitePresentation (i ≫ f) ∧
  QuasiCompact (i ≫ f) ∧ QuasiSeparated (i ≫ f)` is precisely the finite,
  flat, finitely presented conclusion for the marking.
- The analogous universal pullback for `(i ≫ f).fiberToSpecResidueField t` satisfies
  `Nonempty ... → ... .IsPureDimension 0`. Thus no nonemptiness of the marking
  or all its fibres is asserted.
- The final conjunct `(IsEmpty ((i ≫ f).fiber η) → IsEmpty Z)` is the empty
  generic marking implication, using underlying-point emptiness of the schemes.
- `Scheme.IsPureDimension` is the existing componentwise Krull-dimension definition,
  so the explanation of purity is represented without a private copy.

Dependency declarations and their modules (full signatures and docstrings read):

- `topologicalKrullDim`: `Mathlib.Topology.KrullDimension`.
- `AlgebraicGeometry.IsIntegral`: `Mathlib.AlgebraicGeometry.Properties`.
- `AlgebraicGeometry.Scheme.Hom.fiber`, `.fiberι`, `.fiberToSpecResidueField`:
  `Mathlib.AlgebraicGeometry.Fiber`.
- `AlgebraicGeometry.LocallyOfFinitePresentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`; its quasi-compact and
  quasi-separated comparison clauses use Mathlib's existing morphism classes.
- `IsGenericPoint`: `Mathlib.Topology.Sober`.
- `AlgebraicGeometry.IsClosedImmersion`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `AlgebraicGeometry.Etale`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `AlgebraicGeometry.IsFinite`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`.
- `AlgebraicGeometry.Flat`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`.
- `CategoryTheory.Limits.pullback`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`. The node's recorded
  geometric-fibre match is the equivalent iterated pullback of the ordinary fibre.
- `irreducibleComponents`: `Mathlib.Topology.Irreducible`, used by the imported
  definition of purity. This Mathlib-status dependency needs no new Lean record.
- `AlgebraicGeometry.IsProper`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- `AlgebraicGeometry.Scheme.residueField`:
  `Mathlib.AlgebraicGeometry.ResidueField`, with its existing Field instance.
- `AlgebraicGeometry.Scheme.IsPureDimension`: `Sheaf.AlgebraicGeometry.PureDimension`.
- `AlgebraicGeometry.Surjective`: `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`.

The two latter definition nodes already have landed records. Their ids
`def-weil-pure-dimension` and `def-weil-surjective-morphism` were added to `stmt_deps`
under brief-stage2 section 5's authorization to add existing landed notions. No new
node or definition was created. All original dependency records are used unchanged.

Stated proof dependencies are imported privately: the flat dense generic-fibre theorem,
locally quasi-finite dimension-zero criterion, equidimensional-open local-dimension theorem,
etale-fibre discrete/separable theorem, and Mathlib's proper-quasi-finite finiteness theorem.
The other proof dependencies are supplied by the already imported Mathlib modules.
No proof-dependency import is omitted for an import cycle.
The theorem docstring gives all seven accepted proof steps, naming their DAG dependencies.

Sources checked: Stacks `more-morphisms.tex`, 0GSJ/0GSK (in particular the second list,
with the structure sheaf), and 02LS (proper plus locally quasi-finite implies finite);
`morphisms.tex`, 02NK (base change of relative dimension) and 0397 (dimension zero
and locally quasi-finite). No Noetherian assumption is added.

Edge cases checked before writing:

- Empty marking and empty generic marking: finite/etale hypotheses allow them;
  the dimension-zero conclusion has an explicit nonempty premise; density yields
  the final empty implication. The existing purity definition is vacuous on empty schemes.
- Empty generic curve cannot occur, because irreducibility includes nonemptiness;
  the node explicitly excludes it. The integral base is itself nonempty.
- Base a field: the generic fibre is the family itself and the marking hypothesis
  already gives the finite marking.
- Non-Noetherian integral base: no Noetherian or finiteness condition on the base is added.
- A reducible or nonreduced special curve is allowed; purity does not assert smoothness,
  reducedness, or irreducibility of geometric fibres.
- A marking may ramify or become nonreduced in a special fibre: etaleness is required
  only at the generic fibre, and the conclusion does not assert global etaleness.
- Arbitrary characteristic and transcendental algebraically closed residue-field
  extensions are included. Schemes and test fields share the arbitrary universe `u`,
  as in the published dense-generic-fibre dependency; there is no separate smaller
  test universe and no restriction to algebraic closures.

Searches for an exact existing statement:

- `msearch.py ... leansearch`: query "A proper flat finitely presented curve over an
  integral scheme with dense irreducible dimension one generic fibre has pure dimension
  one geometric fibres and a flat closed marking with finite etale generic fibre is finite".
  Eight results: `IsFinite.recOn`, smooth-to-LFP, finite-to-proper, finite-to-locally-quasi-finite,
  finite-carrier fibres, proper-to-LFT, Flat.casesOn, finite-to-proper. None is this theorem.
- `msearch.py ... leanfinder`: query "A proper flat family over an integral scheme with
  dense irreducible one dimensional generic fibre has nonempty pure curve geometric fibres
  and a closed flat finitely presented marking with finite etale generic fibre is finite".
  Eight results: finite global sections of proper integral schemes, IsFinite, finite-carrier
  fibres, Flat, IsIntegralHom, finite-to-proper, flat-LFP-to-universally-open, and LFP.
  These supply notions or tools, not the combined statement.
- `msearch.py ... loogle 'AlgebraicGeometry.IsProper, AlgebraicGeometry.Flat'`: zero hits.
- `msearch.py ... grep 'pure.*dimension|equidimension|generic.*[Dd]im|[Dd]im.*generic'
  AlgebraicGeometry`: one hit, a discussion in `AlgebraicCycle/Basic.lean`, no theorem.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for purity, equidimension,
  geometric fibres, and proposed theorem names found the reusable
  `Scheme.IsPureDimension` and the dense-generic-fibre proof dependency, but no exact match.
  Searching the item id in `lean/WeilConjectures` returned no declaration.
  Proposed declaration name also has no match in `dag/lean_names_upstream.json`.

There is no statement correction and no STATEMENT-DISPUTED flag.

## Second reading by Q62

A separate reading pass reopened the unchanged DAG statement and the complete Lean module.
The dispatch explicitly prohibits starting another agent; this is a second pass by the
assigned worker, with the maintainer's independent review still required.

The base, generic point, properness, flatness, all three finite-presentation conditions,
closed immersion, and composite marking structure map match their corresponding binders.
Density is of the canonical fibre images in the correct schemes. The nonempty irreducible
one-dimensional generic curve and possibly empty finite etale generic marking match exactly.
The geometric fibre is base change through the residue field, and the quantifiers allow
arbitrary algebraically closed extensions. Every conclusion is present: surjectivity,
nonempty pure dimension-one curve fibres, finite/flat/finitely-presented marking,
pure dimension-zero nonempty marking fibres, and the empty-generic-marking implication.
The existing purity predicate was reopened to check that it means component dimension,
including its vacuous empty case. No mathematical mismatch was found.

The first compile exposed Lean inferring a pullback in the category of types from the
`Nonempty` expected type. All four pullbacks now explicitly specify `(C := Scheme.{u})`,
as the recorded proof dependency does. This changes no object or mathematical condition.
The signature recorded in JSON is extracted verbatim from the final module.
