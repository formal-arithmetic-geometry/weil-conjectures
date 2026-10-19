## Worker report

Q158 states `lem-coef-terminal-local-kan-corepresentability` in
`Sheaf.CategoryTheory.TerminalLocalKanCorepresentability`, declaration
`SSet.Enhanced.TerminalLocalKan.terminal_local_kan_corepresentability`.
The single postponed theorem has `sorry`; every definition has actual data.
All variables and universes are explicit, with `autoImplicit false`.
The source was read at https://cisinski.app.uni-regensburg.de/CatLR.pdf:
Definitions 7.2.2, 7.2.4, 7.2.6, Theorem 7.2.8, and Remark 7.2.10,
especially its four displayed formulas. The ordinary comma description is the
ordinary-nerve specialization of the slice/colimit description there.

Hypotheses, one by one:

- Small ordinary categories: `Datum.A`, `Datum.I`, `categoryA`, `categoryI`.
  Both small categories fit in the common small universe `u`; the simplicial
  localization lives in the independently enlarged universe `max u t`.
  `largeNerve` lifts every comma nerve degreewise to this ambient universe.
- A wide subcategory containing isomorphisms: `Datum.W` is the actual Mathlib
  `MorphismProperty A`; `multiplicative : W.IsMultiplicative` supplies identities
  and closure under composition, and `isomorphisms` includes every isomorphism.
- The given coherent localization: `Datum.L`, `q`, and
  `localization : HomotopicalAlgebra.FiniteReedy.IsLocalization W q`.
  The recorded interface includes the quasicategory property, inversion of W,
  and the equivalence of entire coherent functor categories under restriction,
  for every ambient quasicategory. Neither locality nor localization is derived
  or replaced by an ordinary categorical localization.
- The indexing functor and specified terminal object: `π`, `i₀`, and
  `terminal : CategoryTheory.Limits.IsTerminal i₀`.
  The object called x is written literally as `D.π.obj D.i₀` throughout.
- Every terminal denominator belongs to W: `denominators` is exactly
  `∀ i, W (π.map (terminal.from i))`.
- The comma categories: `CostructuredArrow D.π y`, using Mathlib's objects
  `(i, f : π i ⟶ y)` and morphism equation `π.map h ≫ f' = f`.
  `CostructuredArrow.map` is the actual postcomposition functor.
- Locality: `Datum.locality` quantifies over every `w : y ⟶ z` in W and says
  that the lifted nerve of precisely this postcomposition functor is an
  `SSet.Enhanced.IsWeakHomotopyEquivalence`.

Conclusions, one by one:

- `Comparisons D` consists of actual simplicial maps from each lifted comma
  nerve to the recorded right-pinched `mappingSpace D.L (q x) (q y)`.
  The first conjunct says every one is a weak homotopy equivalence. This
  expresses an equivalence of weak homotopy types without assuming the comma
  nerves themselves Kan.
- Entire target-variable coherence is `∃ a, TargetComparison D c a`.
  Its domain is the nerve of `Total D = Comma D.π (𝟭 D.A)`, retaining all
  target arrows and all their compositions, rather than the disjoint union
  of fixed-target comma categories. Its values are arrows in L with source
  constantly qx and target exactly the localized target projection.
  The fixed-target restriction is related to `c y` on EVERY simplex by
  `rightPinchPrism`; the two fixed-endpoint arrow-space diagrams are coherently
  naturally equivalent. Thus right-pinched maps and the full arrow family
  are related in their full spaces, not merely on components.
- `FractionFormula` asserts the actual compositional triangle
  `q(π(i → i₀))`, `c(i,f)`, `q(f)` via the recorded `Composes` predicate.
  Since the first edge is inverted, this says precisely the required component
  formula `q(f) q(π(i → i₀))⁻¹`, without supplying arbitrary chosen inverses.
- `IdentityFormula` explicitly equates the component of `(i₀, 𝟙 x)` with
  the component of the degeneracy identity vertex in the right-pinched space.
- `Postcomposition` gives a whole mapping-space map for each actual v,
  the coherent naturality square with the actual comma postcomposition functor,
  and its normalization as composition with the localized v on every vertex.
  `TargetComparison` supplies the simultaneous higher target coherences.
- A second datum is quantified in `DataNaturality`; `DatumMap` has precisely
  U, V, preservation of W, equality on the specified terminal object, and
  the equality `V ⋙ π' = π ⋙ U`. These are the hypotheses in the node.
  `mapTotal` is Mathlib's `Comma.map`, with the transports prescribed by that
  equality; it sends `(i,y,f)` to `(Vi,Uy,Uf)` with those transports.
- The localized functor Q is a conclusion, accompanied by a coherent natural
  equivalence `η : q Q ≃ N(U) q'`. A coherent natural equivalence ξ compares
  the two WHOLE arrow diagrams over `N Total D`; its two endpoint restrictions
  are required to be exactly η restricted to the constant source and actual
  moving target. This keeps the endpoint transport in the data naturality
  square, including the terminal-object equality.
  The second comparisons are assumed only to have their specified coherent
  arrow family and fraction/identity normalization, not a new locality premise.
- Higher canonicality and composition of maps of the data are retained by
  `CoherentChoices`. `transformations D F` is the full right-pinched mapping
  space of coherent transformations from the constant F(qx) to the actual
  target projection followed by F. `normalization D F` is the PUBLISHED
  evaluation map at `(i₀,x,1)`, mapped on right-pinched spaces, with explicit
  equalities transporting its endpoints. `normalizedChoices D F` is its
  homotopy fiber at the identity, retaining the normalizing path itself.
  For every quasicategory C and functor F : L → C, these spaces are Kan,
  contractible, and have every boundary filler. Degree zero gives existence;
  degree one compares two normalized choices; degree two fills compositional
  triangles; higher n retain all further compatibilities. Taking C to be the
  last localization in any chain of data maps and F its composite includes
  transported comparisons and all their higher choices in one common space.
  This is the contractible-choice formulation in proof step 8 of the node,
  rather than an assertion about an unrelated arbitrary space.

The helpers are interfaces for this node's own data, comma comparison,
normalization and naturality. No independent missing mathematical notion was
introduced. No dependency module or statement correction was needed.
The main theorem docstring gives all eight DAG proof steps, with their cited
nodes, and explains the total-comma evaluation normalization and its fibers.

Dependency declarations used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `mappingSpace`,
  `mappingSpaceMap`, `diagramVertex`, `evaluation`, `AreNaturallyEquivalent`,
  `IsEquivalenceEdge`, `IsWeakHomotopyEquivalence`, `IsContractible`,
  `homotopyFiber`. These are the recorded definitions of the stipulated
  quasicategorical and space-valued conventions.
- `Sheaf.CategoryTheory.InfinityCategoryOfSpaces`:
  `CategoryTheory.Spaces.infinityCategory` and its coherent corepresentable
  convention. The full declaration and its source docstring were read.
  The comparison is expressed in unstraightened arrow families rather than
  defining a second category of spaces or a second corepresentable functor.
- `Sheaf.CategoryTheory.FiniteReedyLocalization`: `largeNerve`,
  `IsLocalization`, `object`, `Composes`, as recorded separately by the landed
  `def-coef-coherent-localization-interface`. That definition node is added
  to stmt_deps; no finite-Reedy theorem dependency is added.
- `Sheaf.CategoryTheory.RightPinchComparison`: `arrowMappingSpace`,
  `arrowMappingSpaceInclusion`, `rightPinchPrism`; the already landed
  `lem-coef-infinity-pinch-comparison` is added to stmt_deps as this interface
  occurs in the statement and was already a proof dependency.
- Mathlib: `CostructuredArrow`, `CostructuredArrow.map`, `Comma`, `Comma.map`,
  `Comma.snd`, `MorphismProperty.IsMultiplicative`, `Limits.IsTerminal`,
  the ordinary nerve, the degreewise universe lift, π₀ and simplex boundaries.
- All recorded proof-dependency modules are imported plainly; the statement's
  dependency modules are public imports. The downstream citer
  `TrivialFibrationFractionModel` was read for its consumer interface but is
  deliberately not imported, so no dependency cycle is introduced.

Edge cases checked:

- I cannot be empty because i₀ is specified; likewise A contains π(i₀).
  No gratuitous `Nonempty` hypothesis is added.
- A fixed-target comma category may be empty. The actual empty nerve is used,
  and the conclusion requires the corresponding mapping space to have empty
  weak homotopy type. No nonempty-fiber hypothesis or selected comma object
  appears at an arbitrary target.
- The identity target always has `(i₀,1)` and its identity formula is explicit.
- For terminal singleton A and I, the comparison is the contractible point
  case, including degenerate source and target arrows.
- W may be just the isomorphisms or all arrows. Both cases use exactly the
  same locality hypothesis; no Ore condition or calculus hypothesis is added.
- `V(i₀)=i₀'` and the functor equality need not be definitional: `Comma.map`
  uses `eqToHom m.comm`, and data naturality retains endpoint transport.
- Degree zero boundary fillers are included (existence), while the mapping
  and homotopy-fiber constructions retain every higher degree.
- The ambient t can strictly exceed u. No equality of the localization and
  category universes is imposed. The structure's universe linter is disabled
  because its result sort depends on `max u t`; this does not constrain t.

Searches for existing declarations:

- msearch leanfinder, `local comma criterion putative right calculus fractions
  corepresentability`: ordinary localization/fraction and reflection
  corepresentability hits, no coherent comma-nerve criterion.
- msearch loogle, `CategoryTheory.CostructuredArrow, CategoryTheory.Comma`:
  the existing comma constructors and functors; these are reused directly.
- msearch grep, `corepresent.*[Ll]ocal|[Ll]ocal.*corepresent|terminal.*[Kk]an`,
  Mathlib `CategoryTheory`: ordinary Kan-extension and reflection material,
  not this theorem.
- msearch leansearch, `local comma category nerves compute mapping spaces in
  coherent localization with terminal diagram`: eight hits, chiefly
  `WithTerminal.mkCommaObject`, inverse comma constructors and comma
  equivalences; none is the claimed localization theorem.
- rg in upstream `WeilConjectures` for local/comma/corepresentability terms
  and the exact node id: no exact theorem.
- rg in `lean/Sheaf` for these terms: the downstream
  `TrivialFibrationFractionModel` uses this criterion in its proof docstring,
  and the existing right-pinch/localization helpers give the needed interfaces;
  no declaration already states this node.
- `tools/blueprint_refs.py search 'terminal local Kan'`: zero matching units.
  The present node is infrastructure below the cited blueprint proof.
- Full declaration-name collision search was done in the allowed upstream,
  Mathlib and project trees; the `TerminalLocalKan` namespace is new.

No STATEMENT-DISPUTED flag or node fault remains. No hypotheses or conclusions
of the node were changed. The two additional stmt_deps name already landed
interfaces used by the statement, as permitted by the standing brief.

Validation: scompile.py compiled the sole delivered file both as an isolated
sandbox file and at its actual library module path, with no errors or warnings.
The required dry run and delivery are recorded below after their execution.

## Second reading by Q158

Performed a fresh clause-by-clause rereading of the unchanged node and final
module in this worker session; the dispatcher explicitly prohibits starting
another agent, and the maintainer performs the independent delivery review.
The rereading checked the direction of comma arrows and composition, all
localization hypotheses, the lifted universes, the identity point, both data
naturality endpoints, the full target diagram, and the higher coherence clause.
It replaced any separate ordinary comma description with Mathlib's actual
comma construction, made the evaluation endpoint transports explicit, and
ensured the normalized choice spaces are also quantified AFTER functors out
of L, so composable data maps are covered in their common target. The final
file compiles cleanly after these changes. No mathematical statement correction
was required.

Delivery validation: `deliver2.py Q158 lem-coef-terminal-local-kan-corepresentability
--no-push` returned `OK (dry run): commit 3fc70c2950 passes the preflight and
compiles; nothing pushed`. The delivery wrapper repeats these checks when pushing.
