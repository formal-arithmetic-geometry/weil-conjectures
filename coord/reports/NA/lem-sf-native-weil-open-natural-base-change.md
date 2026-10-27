## Worker report

The module `lean/Sheaf/WeilSheaf/NativeOpenNaturalBaseChange.lean` states
`AlgebraicGeometry.nativeWeilOpenNaturalBaseChange`. It uses the native all-sheaf
Weil category `ProEtaleWeilSheaf` and its actual termwise derived operations. The
conclusion is a `Nonempty` natural isomorphism of functors on the full unbounded
ordinary derived categories.

The Lean binders render the statement as follows. `k₀ : Type u` with `[Field k₀]`
and `[Finite k₀]` is the finite base field; `l : ℕ` with `[Fact l.Prime]` and
`[Fact (ringChar k₀ ≠ l)]` renders the prime and unequal-characteristic hypotheses.
The four schemes `U'`, `U`, `T'`, and `T` carry the four `Over (Spec
(CommRingCat.of k₀))` instances, and the four `LocallyOfFiniteType` instances
render locally finite type over `k₀`. The arrows `v`, `j'`, `j`, and `u`, with
`*.IsOver` instances, render the four `k₀`-morphisms. `[IsOpenImmersion j']`,
`[IsOpenImmersion j]`, and `[QuasiCompact j]` render the open-square arrows and the
specified quasi-compact open immersion; `sq : ChosenCartesianSquare v j' j u`
renders the chosen Cartesian square and its selected pullback identification.
The displayed `Nonempty` value has source
`(ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory ⋙
(ProEtaleWeilSheaf.upperStar k₀ l u).mapDerivedCategory`, namely `u^* J_j`, and
target `(ProEtaleWeilSheaf.upperStar k₀ l v).mapDerivedCategory ⋙
(ProEtaleWeilSheaf.extensionByZero k₀ l j').mapDerivedCategory`, namely
`J_{j'} v^*`. `Iso` supplies both the natural comparison and its inverse in the
native equivariant derived categories. The use of ambient `ProEtaleWeilSheaf`
means no constructibility, boundedness, or separatedness hypothesis is added.

The dependency declarations used are:

- `WeilConjectures.WeilSheaf.LowerShriek`,
  `AlgebraicGeometry.ProEtaleWeilSheaf.extensionByZero` and
  `AlgebraicGeometry.ProEtaleWeilSheaf.upperStar`; the framework node
  `def-sf-native-weil-derived-framework` records the native coefficient sheaves,
  fixed-pair categories, and ordinary derived categories.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`,
  `AlgebraicGeometry.ChosenCartesianSquare`, for the chosen Cartesian square
  (`def-weil-pbc-cartesian-square`).
- Mathlib `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.IsOpenImmersion`; `def-weil-finite-type-morphism` and
  `def-weil-open-immersion` record those exact matches.

Edge cases checked against the source statement and the operations are the empty
open (extension by zero is still defined), `j = 𝟙`, `u = 𝟙`, `v = 𝟙`, and a base
change whose image misses the open (both sides are zero on the complement). The
statement has no constructibility or absolute-separatedness assumptions and allows
arbitrary `u`.

Searches made:

- `msearch.py ... leanfinder "native derived Weil open extension by zero pullback cartesian square base change"` returned only generic pullback/restriction declarations; no native derived Weil base-change isomorphism.
- `msearch.py ... loogle "ProEtaleWeilSheaf.extensionByZero, ProEtaleWeilSheaf.upperStar, mapDerivedCategory"` returned no match (the names are project declarations, not Mathlib declarations).
- `msearch.py ... grep "extensionByZero|extension_by_zero|shriek.*base.*change" Mathlib/` returned no match.
- `rg` over `WeilConjectures/` and `Sheaf/` found no declaration with this node id or
  with the complete native open base-change statement. `tools/blueprint_refs.py search
  lem-sf-native-weil-open-natural-base-change` found no pre-existing blueprint node.
  The only DAG citer is `lem-sf-native-weil-compact-base-change`, which names this
  item only in `proof_deps`; its use remains valid because the present conclusion is
  precisely the native open factor it invokes.

No `STATEMENT-DISPUTED` issue or node fault was found.

## Second reading by NA

I reread the item, all four `stmt_deps`, their recorded declarations and source
docstrings, and the module. The finite-field, prime, characteristic, four locally
finite-type schemes, four over-morphisms, chosen Cartesian square, quasi-compact open
immersion, arbitrary base map, and exact orientation of the natural isomorphism all
match clause by clause. The inverse is included by `Iso`; all functors are the
published native operations. No dependency module or new definition node was needed.
