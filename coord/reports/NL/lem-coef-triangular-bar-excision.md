## Worker report

The delivery states `CategoryTheory.TriangularBar.triangular_bar_excision` in
`Sheaf.CategoryTheory.TriangularBarExcision`. All theorem proofs are `sorry`.
Definitions have explicit data; each proof needed by a definition is a separate named
helper theorem, recorded in `lean.declarations`. The node changes only in `lean`.
There are no new nodes, dependency repairs, or statement corrections.

The source is the node's agent-formulated auxiliary two-block calculation supporting
paragraph 2 of `prop-coef-integral-exceptional-adjoint.proof.md` in blueprint
main-20261015. I opened that blueprint proof: its paragraph 2 is the coherent middle
adjunction, not a published two-block excision theorem. The module preserves the node's
qualification that HTT A.3.2--A.3.3 is background only. Its main docstring records all
seven proof steps and the comparisons between simplicial and topological representatives.

Hypothesis and clause correspondence:

- A small simplicial category in the fixed universe is `T : CoherentNerve.SCat.{u}`.
  Its object type and mapping simplicial sets have universe `u`, exactly as in the
  dependency. Modules are the dependency's `DerivedSpaceModule.Left T` and `Right T`.
- The disjoint partition is `c : T → Bool`: the fibers over `false` and `true` are
  respectively O₀ and O₁. Every object belongs to exactly one fiber. Conversely every
  partition in the node gives such a function; no nonemptiness or finiteness is assumed.
- The empty reverse mapping sets are `NoBackwards c`, requiring `IsEmpty` in every
  simplicial degree of `CoherentNerve.hom T a b` whenever `c a = true` and `c b = false`.
  No local Kan, fibrancy, or projective-cofibrancy assumption appears.
- `pure c i X Y` is the actual subcomplex of the dependency's `bar X Y` consisting of
  words whose every vertex has color `i`. Thus its degree-n summands are exactly the
  restricted bar for the full subcategory Tᵢ and restrictions Xᵢ,Yᵢ. Its mapping factors,
  endpoint modules, and operators are inherited, with no new definition of modules,
  enriched categories, weak equivalences, or general derived coends.
- `MixedWord c X Y n` is a word with a first and a second block of n+1 vertices.
  Its one crossing factor is exactly T(aₙ,b₀), namely the stated N. Composites in the
  stored `ComposableArrows` functor are determined by adjacent arrows; they add no
  independent factors. `mixedMap` uses ordinal concatenation in the outer direction
  and the same internal operator. Hence `mixed c X Y` is precisely the diagonal of
  the two-outer-direction, one-internal-direction mixed bar in proof step 2. The
  bar/Fubini interface of the dependency identifies it with either parenthesization
  of X₀ ⊗ᴸ N ⊗ᴸ Y₁. This is a concrete representative of that homotopy type.
- `action c false X Y` retains the first chain and uses the inherited contravariant
  endpoint action to absorb N and the entire second chain into Y₀. `action c true X Y`
  retains the second chain and uses the covariant endpoint action to absorb the first
  chain and N into X₁. They are the specified two arrows of the span, not supplied maps.
- `pushoutModel` is the simplicial double mapping cylinder: the pushout of
  W ⨿ W → W × Δ[1] along the coproduct of these action maps into U ⨿ V.
  This is a standard model for the homotopy pushout of the displayed span. In simplicial
  sets all objects are cofibrant, the cylinder boundary is a monomorphism, and Δ[1] is
  contractible. Equivalently, take the two individual mapping cylinders of the span
  maps: each retracts weakly onto its target, its W inclusion is a cofibration, and
  their pushout is the double mapping cylinder, up to subdividing the interval.
- `comparison` is `pushout.desc` with the specified mixed-word homotopy and `outside`.
  `outside` is the coproduct of the ACTUAL subcomplex inclusions of the pure bars.
  Its connecting homotopy is also fixed on every simplex: a binary monotone word
  selects aⱼ or bⱼ from the concatenated chain, and discarded endpoint arrows act on
  X and Y. Its endpoint equations identify precisely the two action maps.
- The first conjunct of `triangular_bar_excision` states
  `SSet.Enhanced.IsWeakHomotopyEquivalence (comparison c X Y)`. Since its source is
  that homotopy-pushout model and its target is the dependency's derived-bar model,
  this is exactly the displayed natural equivalence of homotopy types, including
  its specified cocone, rather than an unrelated equivalence between objects.
- Block-preserving enriched functors and module maps are `Change`. It contains an
  actual enriched functor F with `c' (F.obj a) = c a`, and endpoint simplicial maps
  commuting with the enriched actions in EVERY internal degree. Functors may identify
  objects in a block. The arbitrary `K : SSet.{u}` encodes a common enriched parameter;
  K = Δ[0] includes ordinary module maps.
- The second conjunct asserts `Natural d` for every such change. The induced pushout
  map is fixed on the whole mixed cylinder and both pure bars, and its square with
  `comparison` commutes with the actual `changeTotal` word map. These generator
  equations determine the pushout map uniquely. Thus it is canonical, not an
  unconstrained arrow or an existence choice used to define data.
- Taking K to each mapping simplicial set of an extra enriched module variable gives
  compatibility with all of that variable's action simplices. All maps are fixed by
  their word formulas, so its identities and compositions agree as well. This handles
  the clause retaining extra enriched variables, beyond ordinary objectwise naturality.
- The third conjunct asserts `Augmentations`. For every dependency `Pairing X Y Z`,
  the two mixed-to-Z composition augmentations agree, and the entire connecting
  homotopy becomes constant after the augmentation. Its pure-bar restrictions are
  the existing `DerivedSpaceModule.augmentation` composed with the actual inclusions.
  The pushout property therefore gives precisely compatibility of the comparison
  with composition augmentations. The dependency's retained-variable/Fubini clauses
  identify these balanced pairings with the stated derived augmentations.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.CoherentNerveComparison`:
  `CategoryTheory.coherent_nerve_comparison` and the imported
  `CoherentNerve.SCat`, `CoherentNerve.hom`, `CoherentNerve.underlying`.
  I read the full recorded statement and its source/proof docstring. No model-structure
  choice or locally Kan replacement is imposed on T.
- `Sheaf.CategoryTheory.DerivedSpaceModuleCoyoneda`:
  `DerivedSpaceModule.derived_space_module_coyoneda`, `Left`, `Right`, `Word`,
  `operator`, `operator_laws`, `bar`, `actLeft`, `actRight`, `Pairing`, `augmentation`;
  I read its bar, projective comparison, `LeftExtension`, `RightExtension`,
  `FubiniComparison`, `FubiniNaturality`, and `AugmentationCompatibility` signatures
  and docstrings. The bar representative is its explicit diagonal, not a private copy.
- `CategoryTheory.SimplicialHammockDegree` and
  `simplicialHammockDegreeFunctor` from the dependency's public
  `Sheaf.CategoryTheory.SimplicialHammockPair` evaluate enriched functors on chains.
- Mathlib `AugmentedSimplexCategory.tensorObjOf`, `tensorHomOf`, `inl'`, `inr'`
  supply ordinal concatenation. Mathlib supplies simplicial cylinders, coproducts,
  pushouts and the componentwise Cartesian tensor structure.

Proof-dependency imports: all recorded modules for
`lem-cbc-realization-singular-unit-weak`,
`lem-coef-bisimplicial-diagonal-space-colimit`,
`lem-coef-derived-space-module-coyoneda`,
`lem-coef-kspace-exponential-law`,
`lem-coef-realization-finite-limits`, and
`lem-coef-simplicial-simplex-colimit-product` are imported. The Mathlib proof leaves
are imported from `Analysis.Convex.StdSimplex`, `Topology.Compactness.Compact`, and
`Topology.Separation.Hausdorff`; I read the recorded compactness and quotient signatures.
`lem-coef-double-mapping-cylinder-space-pushout` has no recorded declaration/module,
so it is cited by the proof docstring but has no import. It is a proof prerequisite;
no missing declaration is needed to type this statement or its explicit constructions.

Edge cases checked before writing:

- O₀ empty: the false pure bar and mixed bar have no words. The double cylinder is
  empty; the pushout and total bar reduce to the true pure bar, with its actual inclusion.
- O₁ empty: the symmetric case. Both blocks empty: all four simplicial sets are empty;
  weak homotopy equivalence uses the component bijection and has no basepoints to test.
- N empty with both blocks nonempty: the mixed bar is empty and the result is the
  disjoint union of pure bars. There is no accidental extra connecting interval.
- One object in each block, only identities within blocks: the formula is the usual
  double cylinder of X₀ × N × Y₁ with the indicated module actions; with terminal
  modules and N a point it is the interval joining the two objects.
- Degree zero of the mixed bar is the single crossing arrow with its endpoint labels;
  the two maps are exactly its right and left module actions. Higher simplicial
  operators insert identities or compose arrows. Non-Kan mapping sets are unrestricted.
- Empty values of X or Y remove the corresponding summands, without assumptions that
  components, spaces, modules, or blocks are inhabited. All binders and universe u are
  explicit; there are no auto-bound implicits.

Searches for existing declarations:

1. `msearch.py ... leanfinder "two block enriched bar derived coend homotopy pushout excision"`:
   eight hits, including `HomotopicalAlgebra.Cylinder.trans_I`, `trans_π`, and cell
   attachment lemmas. These are generic cylinder/cell constructions, not this bar
   excision statement with its actions and enriched naturality.
2. `msearch.py ... loogle '"coend"'`: twelve hits for ordinary categorical coends in
   `Mathlib.CategoryTheory.Limits.Shapes.End`, not the derived enriched two-block theorem.
   Read its coend construction and coprojections to check that distinction.
3. `msearch.py ... grep 'twoSidedBar|triangular.*bar|homotopyPushout' CategoryTheory`:
   zero hits.
4. `msearch.py ... leansearch "Two sided enriched bar over category partitioned into two full blocks homotopy pushout"`:
   eight generic pushout/attachment hits, with no matching statement.
5. `rg` of `triangular|TwoBlock|two.block|excision` in the upstream project and
   `lean/Sheaf/CategoryTheory`: upstream hits are unrelated triangular linear algebra
   and sheaf excision; side hits include mapping-space excision and operadic bars.
   Opened `TwoSidedCoherentBarConstruction`: it constructs a coherent operadic bar
   without colimit assumptions, not this simplicial-enriched two-block homotopy pushout.
6. `rg` for the exact item ID in upstream `WeilConjectures`: no hits.
   `rg` for `TriangularBar|triangular_bar_excision|selectVertex` in upstream,
   `lean/Sheaf`, and `dag/lean_names_upstream.json`: no conflicting declaration.
   Other `MixedWord` hits are in a different namespace for operadic word substitution.

Validation: the full module compiled cleanly through the required `scompile.py` in
both its sandbox form and its eventual module path, at approximately four seconds per
file. Initial elaboration failures (explicit product-category indices, the subcomplex
map argument, and implicit coproduct injection arguments) were repaired. One unused
variable name was repaired. No warning remains. Every theorem is deliberately unproved.

There is no STATEMENT-DISPUTED flag or identified node fault.

## Second reading by NL

No second worker was started, as explicitly required by the dispatcher brief. The
maintainer's independent review reads this delivery. This section does not claim an
independent review by the author.
