## Worker report

The module `Sheaf.Paper.GeometricFiberQbar` states
`AlgebraicGeometry.Scheme.geometricFiber_qbar_properBaseChange`. It introduces
`Qbar` as an algebraic closure of `ℚ_[l]`, a proper morphism `f`, a geometric
point `ybar : Spec (.of Ω) ⟶ Y`, and the chosen pullback square
`geometricFiberSquare f ybar`. The conclusion is an existential
`PbcQbarExchangePresentation` whose descended exchange is an isomorphism at
 every `K : pbcQbarCategory l Qbar X`, whose finite-stage exchange components
are isomorphisms, and whose component equals the canonical `atStage` formula
for every finite overfield `M` containing the stage of `K`.

The Lean binders render the statement hypotheses as follows. `l` is prime via
`[Fact l.Prime]`; `Qbar` has `[Field Qbar]`, `[Algebra ℚ_[l] Qbar]`, and
`[IsAlgClosure ℚ_[l] Qbar]`. The schemes and maps are `{X Y : Scheme.{u}}`,
`f : X ⟶ Y`, `Ω : Type u` with `[Field Ω] [IsAlgClosed Ω]`, and
`ybar : Spec (.of Ω) ⟶ Y`. The four noetherian assumptions are the four
`[IsNoetherian ...]` binders. Finite dimensionality is represented by the four
`Fact (∃ n, topologicalKrullDim _ ≤ (n : WithBot ℕ∞))` binders `dX`, `dY`,
`dFiber`, and `dPoint`. Invertibility of `l` on all four schemes is rendered
stalkwise by the four `Fact (∀ t, IsUnit (l : stalk t))` binders `iX`, `iY`,
`iFiber`, and `iPoint`. Properness of `f` and of the geometric-fiber map is
`[IsProper f]` and `[IsProper (pullback.snd f ybar)]`. The uniform geometric
fiber bound is the explicit `(e : ℕ)` and `_hFibres` binder over all algebraically
closed geometric points. The conclusion's first conjunct is
`∀ K, IsIso ((P.exchange).app K)`, the second is
`∀ M K, IsIso ((P.Ex.τ M).app K)`, and the third is the displayed equality with
`PbcQbarExchangePresentation.atStage`, which is the finite-stage geometric-fiber
exchange on the scalar-extended representative.

Dependencies used are `Sheaf.Paper.PbcQbarCategory`
(`AlgebraicGeometry.Scheme.pbcQbarCategory`),
`Sheaf.Paper.GeometricFiberFiniteExtension`
(`AlgebraicGeometry.Scheme.geometricFiberSquare` and
`geometricFiber_finiteExtension_properBaseChange`),
`Sheaf.AlgebraicGeometry.ChosenCartesianSquare`
(`AlgebraicGeometry.ChosenCartesianSquare`),
`Sheaf.AlgebraicGeometry.Dimension`
(`AlgebraicGeometry.Scheme.dim`),
`Sheaf.Paper.PbcDescentFunctors`
(`AlgebraicGeometry.Scheme.pbcDescentFunctors`), and
`Sheaf.Paper.PbcScalarExtension`
(`AlgebraicGeometry.Scheme.pbcCoherentScalarExtension`). The proof dependency
`Sheaf.Paper.QbarProperBaseChange` supplies
`PbcQbarExchangePresentation`, `PbcQbarExchangePresentation.atStage`, and
`qbar_properBaseChange`; the proof specializes the latter and projects its
three required conjuncts. No definition data is postponed.

Edge cases checked: `e = 0`; identity `f`; `M` equal to `K.stage`; zero
objects; and empty geometric fibers. The stalkwise invertibility hypotheses
exclude residue characteristic `l`, as required by the source. Universes keep
`Qbar : Type w` independent of the scheme and geometric-point universe
`Type u`, while every geometric fiber and its point remain in `Scheme.{u}`.

Searches made: `msearch.py ... leanfinder "Qbar l-adic proper base change geometric fiber exchange"`
returned only generic proper-base-change and pullback declarations, with no
matching derived Qbar exchange; `msearch.py ... loogle
"PbcQbarExchangePresentation, qbar_properBaseChange, IsIso"` returned no hits;
`msearch.py ... grep "geometricFiber.*qbar|qbar.*properBaseChange" WeilConjectures`
returned no source hits. Direct `rg` over the project found the canonical
`QbarProperBaseChange.lean` presentation and no duplicate geometric-fiber-Qbar
corollary. Mathlib grep for Qbar geometric-fiber proper-base-change declarations
also found no match. Therefore the new declaration is required.

## Second reading by Q77

I reread the node and the module signature independently. The prime, algebraic
closure, proper morphism, geometric point, four noetherian schemes, four finite
 dimension witnesses, four invertibility witnesses, proper fiber map, and
uniform fiber bound each have a corresponding Lean binder. The chosen square is
exactly `(f, pullback.snd f ybar, ybar, pullback.fst f ybar, id)` through
`geometricFiberSquare f ybar`. The three conclusion clauses respectively render
invertibility of the descended exchange, invertibility of every finite-stage
exchange, and its finite-overfield representative formula. No hypothesis or
conclusion clause was omitted; the proof only obtains the existing canonical
Qbar presentation and projects those clauses. The file compiled cleanly with
`scompile.py`.
