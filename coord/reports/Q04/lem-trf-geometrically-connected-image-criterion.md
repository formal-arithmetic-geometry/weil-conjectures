## Worker report

This repair supplies the missing stage-2 Lean statement for the Tag 056R criterion. The
module is `Sheaf.AlgebraicGeometry.GeometricallyConnectedImageCriterion` and states
`AlgebraicGeometry.GeometricallyConnected.of_connectedSpace_of_geometricallyConnected`
with a `sorry` proof. The node's statement is unchanged; only its `lean` record is added.

The field is `(k : Type u) [Field k]`. The schemes are `(T X : Scheme.{u})` with
`[T.Over (Spec (.of k))]` and `[X.Over (Spec (.of k))]`; these are the two schemes over
`k` in the node. The given morphism is `(f : T ⟶ X)` with `[f.IsOver (Spec (.of k))]`,
which renders a morphism of schemes over `k`. The hypothesis that `T` is geometrically
connected is `[GeometricallyConnected (T ↘ Spec (.of k))]`. The hypothesis that `X` is
connected is `[ConnectedSpace X]`, whose underlying topological space is nonempty and
has no nontrivial clopen separation. The conclusion is
`GeometricallyConnected (X ↘ Spec (.of k))`, exactly the node's geometric-connectedness
conclusion over `k`.

The module uses Mathlib's `AlgebraicGeometry.GeometricallyConnected` and the standard
`Scheme.Over`/`IsOver` structures; it introduces no replacement definitions or extra
finiteness, separatedness, surjectivity, reducedness, or characteristic assumptions. The
statement's docstring records the node proof plan: finite-separable reduction through a
finite Galois extension, connectedness and surjective projections after base change,
Galois-invariant clopen intersection and descent, connectedness descent, and the
finite-separable geometric-connectedness test. The only postponed proof is the theorem's
`sorry`.

Dependency declarations read and used: `Mathlib.AlgebraicGeometry.Over` (`Scheme.Over`,
`Scheme.Hom.IsOver`), `Mathlib.AlgebraicGeometry.Geometrically.Connected`
(`AlgebraicGeometry.GeometricallyConnected`), and
`Mathlib.AlgebraicGeometry.Geometrically.Integral` (which imports the recorded Mathlib
geometric-irreducibility class). The project dependency nodes
`def-weil-scheme-over-base`, `def-weil-connected-scheme`, and
`def-pc-geometrically-irreducible` were read; the first two are conventions/definitions
rendered by these standard structures and the third is the Mathlib geometric-property
notion.

Edge cases checked: `T` and `X` have the same universe as the base field, matching the
scheme-over-field convention; no nonempty source hypothesis is added because
`GeometricallyConnected` entails connectedness and hence nonemptiness; the connected
hypothesis on `X` likewise excludes the empty target; the morphism need not be
surjective; arbitrary characteristic, nonreduced schemes, and non-quasi-compact schemes
remain allowed.

Searches for an exact existing declaration found no match. `msearch.py` LeanFinder for
“a geometrically connected scheme mapping to a connected scheme over a field implies
geometric connectedness of the target” returned only unrelated universal-injectivity,
properness, and dominance declarations. `msearch.py` Loogle for
`GeometricallyConnected.of_connectedSpace, GeometricallyConnected, IsOver` returned zero
hits. `msearch.py` grep for
`GeometricallyConnected.*ConnectedSpace|connectedSpace.*GeometricallyConnected` in
Mathlib algebraic geometry returned zero exact criterion hits. `rg` over the project and
upstream source found only the already existing rational-section/open-immersion criteria,
not Tag 056R. The exact Mathlib geometric-connectedness definition was read and reused.

## Second reading by Q04

I reread the item node, its three statement dependencies, the complete module, and the
Tag 056R source. Every node clause has a direct Lean rendering listed above: field,
over-field structures, over-base morphism, geometric connectedness of `T`, connectedness
of `X`, and geometric connectedness of `X`. The theorem has no extra hypothesis and no
weakened conclusion. The imports are standard Mathlib declarations and the proof is
`sorry` only. Compilation through `scompile.py` succeeds without errors or warnings after
adding the public section marker required for an exported declaration. No statement
correction, dependency module, or new definition node is needed.
