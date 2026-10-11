## Worker report

The module `Sheaf.AlgebraicGeometry.AmpleSquareZeroThickening` states that for schemes `X` and `Z` of the same universe, a closed immersion `j : Z ⟶ X`, locally Noetherian and quasi-compact hypotheses on both schemes, an invertible module `L` on `X`, and square-zero ideal sheaf `j.ker ^ 2 = ⊥`, ampleness of the tensor pullback implies ampleness of `L`. The `letI` installs the invertibility of the tensor pullback from the dependency module.

The binders render the node clause by clause: `j` is the scheme morphism; `[IsClosedImmersion j]` is the closed immersion; `[IsLocallyNoetherian X]`, `[CompactSpace X]`, `[IsLocallyNoetherian Z]`, and `[CompactSpace Z]` are the Noetherian hypotheses; `L : X.Modules` with `[L.IsInvertible]` is the invertible module; `hI : j.ker ^ 2 = ⊥` is square-zero; `tensorPullback j` is the recorded module pullback; and the implication from `IsAmple Z ...` to `IsAmple X L` is the conclusion.

Dependencies used: Mathlib `AlgebraicGeometry.IsClosedImmersion`, `AlgebraicGeometry.IsLocallyNoetherian`, and `CompactSpace`; project declarations `AlgebraicGeometry.Scheme.Modules.tensorPullback`, `IsInvertible`, and `IsAmple` from `Sheaf.AlgebraicGeometry.TensorPullback`, `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, and `Sheaf.AlgebraicGeometry.Ample`.

Edge cases checked: the square-zero condition permits the zero ideal (`j.ker = ⊥`); the statement allows empty schemes through the existing typeclass hypotheses; `n = 0` is excluded internally by the definition of `IsAmple`; no characteristic or nonempty assumption is added.

Searches: `msearch.py leanfinder` for square-zero thickening and ample invertible modules found only subscheme/basic-open declarations and no ampleness theorem; `msearch.py loogle` for `Ample` found no relevant declaration; grep of Mathlib AlgebraicGeometry for `ample`, `thickening`, and `square-zero` found no line-bundle ampleness notion; `rg` over `WeilConjectures` and `lean/Sheaf` found only the existing `IsAmple` definition and no theorem with this statement.


## Earlier second reading (a previous round; superseded)

Read the node and both modules independently. The main theorem includes every hypothesis and conclusion clause from the node, with no added geometric assumptions. The `j.ker ^ 2 = ⊥` expression uses the closed immersion ideal sheaf and its powers. The helper theorem `tensorPullback_isInvertible` supplies the let-bound invertibility instance required by `IsAmple`; it does not alter the mathematical implication. The dependency module states the dependency node's pullback-invertibility notion using tensorPullback, explaining why the recorded older pullback declaration was unusable.

## Second reading by J1

The node introduces a closed immersion `j : Z ⟶ X`, locally Noetherian and quasi-compact
schemes `X` and `Z`, a square-zero ideal condition `j.ker ^ 2 = ⊥`, an invertible module
`L : X.Modules`, its pullback, and the implication from pullback ampleness to ampleness.
The theorem renders these as `[IsClosedImmersion j]`, `[IsLocallyNoetherian X]`,
`[CompactSpace X]`, `[IsLocallyNoetherian Z]`, `[CompactSpace Z]`, `hI`, `L` with
`[L.IsInvertible]`, `Scheme.Modules.tensorPullback j`, and the exact `IsAmple` implication.
No hypothesis or conclusion clause is added or omitted. Empty schemes and the zero ideal are
allowed; `IsAmple` itself requires positive tensor powers, and no characteristic restriction is
introduced.

The recorded dependency theorem `AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback`
uses the distinct `Scheme.Modules.pullback` construction, so it was unusable for this node's
standard tensor pullback. I added dependency module
`Sheaf.AlgebraicGeometry.TensorPullbackInvertible`, stating the dependency notion for
`tensorPullback`, and updated that dependency node's `lean` record with the reason. The item
module now imports this dependency module and contains only the item theorem. Searches in
Mathlib, WeilConjectures, and Sheaf found no existing square-zero ampleness theorem; the
existing `IsAmple` and `tensorPullback` definitions are used directly.
