## Worker report

The delivery states lem-trf-projective-determinant-chart-descent without changing its
informal statement or dependencies. The module is
Sheaf.LinearAlgebra.ProjectiveDeterminantChartDescent. Its two postponed theorems are
Module.determinant_chart_descent and Module.determinant_chart_tensor_descent. Every other
declaration is an explicit definition belonging to this node's chart/descent interface;
none contains sorry. Both theorem docstrings give the corresponding steps of the nine-step
DAG proof. No independent mathematical notion, new definition node, or dependency repair
is needed.

Source read: literature/stacks-project/more-algebra.tex, lines 36225--36335, section
Determinants (0FJ9), remark-determinant-as-socle (0FJA), lemma-det-ses (0FJB), including
both proofs; literature/stacks-project/algebra.tex, lines 4306--4366,
lemma-cover-module (00EK). The statement is the explicit module descent elaboration of
those constructions, including the intrinsic socle model already fixed by the dependency.

Hypothesis and clause correspondence:

- A commutative ring is `{R : Type u} [CommRing R]`. Arbitrary module universes v, w, z
  are independent of u. Finite projectivity is `[Module.Finite R E] [Module.Projective R E]`,
  and likewise for each of E₁, E₂, E₃. Over a ring this is exactly direct summand of finite
  free. The modules' AddCommGroup and Module structures are explicit binders.
- The finite free cover is `{r : ℕ} (f : Fin r → R)` with
  `Ideal.span (Set.range f) = ⊤`, local ranks `n : Fin r → ℕ`, and the displayed basis of
  `LocalizedModule.Away (f a) E` over `Localization.Away (f a)` indexed by `Fin (n a)`.
  There is no nonempty-cover, positive-rank or nonzero-ring assumption.
- `determinantChartLine E (f a) (n a)` is an abbreviation for the EXISTING Mathlib
  exterior power, not a new exterior construction. `determinantModule` is imported from
  the recorded definition node, with its original annihilator data.
- `DeterminantCharts.map` sends the intrinsic socle to each top exterior chart;
  `inclusion` says its exterior-algebra value is EXACTLY `ExteriorAlgebra.scalarExtensionMap`
  of the original element under the module localization map. This specifies the canonical
  chart, including its basis independence. `localizes` makes this a localization, hence
  `iso` is Mathlib's canonical `IsLocalizedModule.iso`. Although this equivalence is
  displayed as R-linear, it is automatically linear over R_f: R-linearity commutes with
  the invertible action of f and therefore with its inverse. The theorem also displays
  the rank-one chart equivalences as R_f-linear equivalences.
- `restricts` states the same localization property for each further principal open h
  divisible by f a. It is a CONCLUSION of existence of charts, not an assumption on E.
  `restrictedIso` is the existing Mathlib iso for that composite localization map.
  Localizing the chart at h or the complementary factor gives the same restriction,
  because f a is already invertible on the chart. This handles the notation (L_a)_{f_b}
  on overlaps using h=f_a*f_b without choosing separate ring presentations.
- `transition` is inverse restricted chart a followed by restricted chart b, both through
  the same localization of the intrinsic socle. The transition formula in the theorem
  explicitly takes the image of x in chart a to its image in chart b. Combined with
  `inclusion` and localization, it is the exterior map induced by the identity on the
  original module, on every element, not an arbitrary isomorphism.
- Nonzero-overlap rank equality is the explicit implication
  `Nontrivial (Localization.Away (f a * f b)) → n a = n b`.
  Zero overlaps need no rank equality: all restricted modules are zero, so `transition`
  is the unique linear equivalence. Identity transitions and the three-chart cocycle are
  explicit conjuncts, allowing any common principal restriction h. The transition
  definition also permits two different covers, not just two indices of one cover.
- Descent takes D to be the actual intrinsic socle, so its canonical identification with
  D_R(E) is identity. Finite and projective are explicit conjuncts, and each localization
  is isomorphic over R_f to R_f. The P/p conjunct states universal descent: every other
  module with localizing chart maps agreeing under these transitions has a UNIQUE
  equivalence to D, commuting with every chart. Thus no clause is weakened to mere
  existence of an arbitrary finite projective line.
- Unique charts are expressed by `∃! C : DeterminantCharts E f n, True`: True here is
  only the terminal predicate of unique existence of an object carrying its specified
  equations, not an added tautological mathematical hypothesis. Together with the
  comparison for arbitrary P and transitions between two covers, this gives cover and
  refinement independence. A basis itself never enters a chart's inclusion formula.
- Every multiplicative subset is quantified by `S : Submonoid R`, without excluding zero.
  The unique q maps into `determinantModule (Localization S) (LocalizedModule S E)`, has
  the canonical exterior inclusion formula, and satisfies `IsLocalizedModule S q`.
  Successive localizations have the same maps because exterior scalar-extension maps
  compose on vectors and scalars and inclusion is injective; uniqueness here supplies the
  compatibility, not a choice of arbitrary localized isomorphisms.
- For E=0 the final conjunct is formulated for every subsingleton module, not only a
  particular encoding of 0. Its unique equivalence to R has inverse taking a to
  `algebraMap R (ExteriorAlgebra R E) a`. In particular empty wedge/1 maps to 1.
- In the second theorem the three simultaneous rank functions and three local bases are
  bound. C₁, C₂, C₃ are the uniquely specified chart systems whose existence the first
  theorem supplies; they do not add an assumption to the informal statement.
- `lam` has exactly the R_f-linear equivalence type L₁,a tensor L₂,a ≃ L₃,a over R_f.
  `determinantLocalizedTensorMap` is TensorProduct.map followed by the recorded
  IsLocalization.moduleTensorEquiv in the appropriate direction. It is the canonical
  change-of-coefficient tensor map, not an independently assumed comparison.
- `pairingSection` transports each lambda to a section of (D_R(E₃))_f using C₃.iso.symm.
  `PairingsCompatible` is the equality of these sections on every pairwise overlap,
  evaluated on every p of the global tensor product. This is equivalent to agreement
  on the entire localized tensor product: fractions of global tensors generate it, and
  multiplication by their denominators is invertible on the target. It therefore does
  not replace the overlap hypothesis by agreement only on chosen basis vectors.
- The conclusion supplies an R-linear equivalence e, `IsPairingDescent` for all charts,
  and equality with e for EVERY other equivalence having that property. The predicate
  identifies the whole local map using its restriction to the original tensor module;
  localization uniqueness extends the equality to every fraction.
- The next conjunct explicitly identifies the images of `e.symm x` with
  `(lam a).symm (C₃.map a x)` under the canonical tensor comparison. This says the inverse
  descends precisely the supplied inverse family.
- The g/m/C'/mu conjunct allows ANY second finite cover whose pairings agree with the
  original on their pairwise product refinement. It concludes `IsPairingDescent` for
  the SAME e. This includes every finite principal refinement and also identifies two
  covers with a common refinement. No surjectivity of a refinement-index function is
  assumed.
- The final S/q conjunct gives a unique equivalence eS over Localization S, commutes on
  every global tensor p, identifies its inverse on every q₃ x, and records the localized
  chart lambda formula. The q maps are required to have their canonical exterior inclusion
  formula AND be localization maps; they exist uniquely by the first theorem. This
  specifies localization of the supplied family, not just an abstract isomorphism of
  the localized determinant modules. The final chart equation holds on all pure tensors
  from the original modules; tensor generation and the localization universal property
  determine the entire localized chart map. Uniqueness of eS is explicit.

Dependency declarations read and used:

- def-trf-projective-determinant-module: Sheaf.LinearAlgebra.ProjectiveDeterminantModule,
  Module.determinantModule and ExteriorAlgebra.scalarExtensionMap; full module read.
- def-weil-pbc-projective-module: Mathlib.Algebra.Module.Projective, Module.Projective;
  declaration and direct-summand docstring read at lines 65--75. Finiteness is Module.Finite.
- def-weil-pbc-exterior-algebra: Mathlib.LinearAlgebra.ExteriorAlgebra.Basic,
  ExteriorAlgebra, ExteriorAlgebra.ι, exteriorPower and ExteriorAlgebra.ιMulti;
  Mathlib.LinearAlgebra.ExteriorPower.Basic, exteriorPower.ιMulti, zeroEquiv, oneEquiv.
- def-weil-pbc-module-tensor-product: TensorProduct and TensorProduct.map, with its
  existing coefficient comparison from Mathlib.RingTheory.Localization.BaseChange.
- def-weil-pbc-module-localization[-away]: Mathlib.Algebra.Module.LocalizedModule.Basic,
  LocalizedModule, LocalizedModule.Away, mkLinearMap, IsLocalizedModule (fields read),
  IsLocalizedModule.lift, iso, and map. No localization copy is introduced.
- def-weil-pbc-free-module: Mathlib.LinearAlgebra.FreeModule.Basic, Module.Free and
  Module.Basis (the node's explicitly supplied finite bases are used).
- Proof imports: WeilConjectures.LinearAlgebra.GenericExteriorPowerLocalization,
  exteriorPower.isLocalizedModule_of_pure_wedge (full signature and docstring read);
  Mathlib.LinearAlgebra.ExteriorPower.Basis, Module.Basis.exteriorPower and coe_basis;
  Mathlib.LinearAlgebra.InvariantBasisNumber, invariantBasisNumber_of_nontrivial_of_commRing;
  Sheaf.RingTheory.FiniteProjectiveOfStandardCover,
  Module.finite_projective_of_localizationAway_free (full module read);
  WeilConjectures.RingTheory.CoverModuleExact, RingTheory.coverModuleExact and its
  localizationAway_map_units_of_dvd (full module read). The last helper is used to build
  the existing canonical overlap lift, so that module is a public import.
- lem-weil-pbc-localization-tensor-product is a Mathlib leaf with no lean record:
  Mathlib.RingTheory.Localization.BaseChange supplies its TensorProduct.map localization
  instance and IsLocalization.moduleTensorEquiv (full relevant section read).

Searches performed (through the prescribed msearch wrapper, group Q41 and this item):

- leansearch: "finite projective determinant exterior algebra socle localization chart
  descent compatible tensor isomorphisms": 8 hits, including moduleTensorEquiv and exterior
  map properties; no determinant chart or compatible-family descent statement.
- leanfinder: "determinant module annihilator exterior algebra localization descent tensor
  product compatible local isomorphisms": 8 hits on cotangent/Kaehler localization,
  finite-presentation local maps and exactness; none states this node.
- loogle: "IsLocalizedModule, LinearEquiv": 12 hits on the existing localization iso and
  linearEquiv interfaces. These are used for charts, not redefined.
- grep wrapper: "determinantModule|[Dd]eterminant.*[Ss]ocle|[Dd]eterminant.*[Dd]escent"
  in LinearAlgebra: zero Mathlib hits. Wrapper search for the proposed helper names
  determinantChartLine|DeterminantCharts|determinantLocalizedTensorMap: zero hits.
- rg on lean/WeilConjectures and lean/Sheaf for projectiveDeterminant, determinantModule,
  chart/determinant combinations and the item id: the determinant socle module and
  ProjectiveDeterminantExactSequence are present. The latter's full source was opened:
  it supplies topExterior, finite_projective, localization and zero partial statements,
  but not universal chart descent, transition equations or arbitrary compatible tensor
  pairings. Importing it would introduce the downstream exact-sequence theorem as a
  dependency of its own proof input. We use its underlying recorded socle definition,
  with the new node's stronger chart-specific statement, instead of creating duplicate
  socle/topExterior/localization definitions.
- rg of all proposed full-name components in lean/WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json returned no name collisions.

Edge cases checked mathematically before and during drafting: r=0 forces R=0 by the
unit-ideal hypothesis and all modules vanish; no forbidden Nonempty index assumption.
Rank zero uses the degree-zero exterior power and the scalar normalization. R=0 permits
local bases of any length, so rank equality is conditioned only on nonzero overlaps.
The example R=Z/6 with different local ranks on its two components has zero cross-overlaps:
our transitions exist there without equating those ranks. Characteristic two changes no
socle coefficient argument, which uses only signs. S containing zero is explicitly
permitted; localized rings and modules are zero and all comparison maps are unique.
Three module universes and the competing descent module universe are independently bound.
All definitions have real data; only the two named theorem proofs are sorry.
No STATEMENT-DISPUTED and no statement correction.

## Second reading by Q41

I performed a separate rereading of the node and final file after drafting; no second agent
was started, as the dispatcher brief explicitly forbids it. The maintainer's independent
review remains required. This rereading found two missing explicit assertions in the first
draft: uniqueness of comparison with an arbitrary descended module P, and the formula for
the transition on localized socle images. Both were added to determinant_chart_descent.
A final line-width warning in the explicit IsLocalizedModule.map application was repaired.

The rereading matched the finite-projective and free-cover hypotheses with their binders,
confirmed that the map fields include the actual exterior localization formula, and
checked that the transition construction works without equal ranks on zero overlaps.
The universal P/p comparison now states the canonical descent claim explicitly; the
rank-one, cocycle, arbitrary S, and zero-module conjuncts are all present. For the second
paragraph, I checked the precise lambda type, overlap equality on the entire localized
module through the localization universal property, uniqueness of e, its inverse formula,
the arbitrary second-cover comparison and uniqueness/inverse/chart equations after S.
No false nonzero-ring or positive-rank hypothesis is hidden in those clauses. The two
proof docstrings account for all nine original proof steps, with the generic tool imports
retained. Every helper belongs to this same node's chart/descent notation and is listed
in lean.declarations. No dependency node or source definition is privately replaced.
