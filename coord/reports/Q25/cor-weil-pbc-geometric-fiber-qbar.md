## Worker report

The module `Sheaf.Paper.GeometricFiberQbar` states
`AlgebraicGeometry.Scheme.geometricFiber_qbar_properBaseChange`.  It specializes
the descended Qbar proper-base-change presentation to
`geometricFiberSquare f ybar`.  The existential `P` is the descended direct-image
and pullback data from `PbcQbarExchangePresentation`; its first conjunct says that
the Qbar exchange is an isomorphism for every `K`, its second says that every
finite-stage component is an isomorphism, its third is the specified
finite-overfield representative formula, and its fourth is independence under an
isomorphism of pair representatives.

The Lean rendering of each hypothesis is as follows.  The prime is
`(l : ℕ) [Fact l.Prime]`; the algebraic closure is
`(Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]`; the schemes and maps
are `{X Y : Scheme.{u}}`, `f : X ⟶ Y`, and
`ybar : Spec (.of Ω) ⟶ Y`.  Noetherianity is stated for all four schemes with
the four `IsNoetherian` instances.  Finite-dimensionality is stated by the four
`Fact (∃ n, topologicalKrullDim _ ≤ (n : WithBot ℕ∞))` instances.  Invertibility
of `l` on all four schemes is stated by the four `Fact (∀ t, IsUnit ...)`
instances on their presheaf stalks.  Properness is stated by `[IsProper f]` and
`[IsProper (pullback.snd f ybar)]`, so the base-changed geometric-fibre map is
included.  The uniform geometric-fibre bound is the explicit `e : ℕ` and
`_hFibres : ∀ Ω' [Field Ω'] [IsAlgClosed Ω'] (y : Spec (.of Ω') ⟶ Y), ...`.

The conclusion uses the chosen square
`geometricFiberSquare f ybar`, whose projections are exactly
`pullback.fst f ybar` and `pullback.snd f ybar`.  Its four clauses render,
respectively, the Qbar isomorphism, finite-stage isomorphism, the equality with
`PbcQbarExchangePresentation.atStage` for every `M` containing the stage of `K`,
and naturality/representative independence for every isomorphism `h : K ≅ L`.
The `atStage` definition is the finite-stage exchange conjugated by the scalar
comparisons, hence is the node's exchange on `T_{M/E} K_E`.

Dependency declarations used:

* `Sheaf.Paper.QbarProperBaseChange`:
  `AlgebraicGeometry.Scheme.PbcQbarExchangePresentation`,
  `.exchange`, `.atStage`, and
  `AlgebraicGeometry.Scheme.qbar_properBaseChange`.
* `Sheaf.Paper.GeometricFiberFiniteExtension`:
  `AlgebraicGeometry.Scheme.geometricFiberSquare` and
  `AlgebraicGeometry.Scheme.geometricFiber_finiteExtension_properBaseChange`.
* `Sheaf.Paper.PbcQbarCategory`:
  `AlgebraicGeometry.Scheme.pbcQbarCategory` and
  `CategoryTheory.StageSystem.pbcStageCategory`.
* `Sheaf.Paper.PbcDescentFunctors`:
  `AlgebraicGeometry.Scheme.pbcDescentFunctors` and the canonical descent
  presentation types used by `PbcQbarExchangePresentation`.
* `Sheaf.Paper.PbcScalarExtension`:
  `CategoryTheory.StageSystem.pbcScalarSystem` and its stage transitions,
  which are used by `atStage`.
* `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.Scheme.ChosenCartesianSquare`.
  Properness and the pullback are Mathlib's `AlgebraicGeometry.IsProper` and
  `CategoryTheory.Limits.pullback`.

Edge cases checked: `M = K.stage` is allowed by the non-strict inequality;
the finite-stage formula therefore includes `M = E`; the zero object is covered
by the universal `∀ K`; identity `f` and an empty geometric fibre use the same
chosen pullback square; and the characteristic-`l` case is excluded on every
corner by the four stalk invertibility hypotheses.  No nonempty-fibre or
positive-dimension assumption was added.

Searches for an existing declaration were made with:

* `msearch.py ... leanfinder "proper base change geometric fiber formula constructible Qbar derived category"`:
  only Mathlib stability and pullback declarations, no matching Qbar exchange.
* `msearch.py ... loogle "CategoryTheory.IsIso, CategoryTheory.NatTrans"`:
  no hits.
* `msearch.py ... grep "proper.*base.?change|geometric.*fiber.*cohomology"`:
  only ordinary scheme base-change and site declarations.
* `rg -n 'geometricFiber|Qbar|properBaseChange' lean/Sheaf`:
  found the finite-extension and general Qbar declarations, but no geometric
  Qbar specialization.
* `rg -n 'geometricFiber|Qbar|properBaseChange' WeilConjectures` and the same
  Mathlib search:
  no declaration with this statement.

No `STATEMENT-DISPUTED` issue or node fault was found.

## Second reading by Q25

I reread the target node and the complete module.  The prime, coefficient field,
four schemes, four Noetherian hypotheses, four dimension clauses, four
invertibility clauses, both properness hypotheses, and the uniform fibre bound
all occur in the Lean binder list.  The chosen square has exactly the node's
orientation `(f, a_ybar, ybar, i_ybar, id)`, with the pullback projections in the
corresponding positions.  The four conclusion clauses match the descended
exchange, its finite-stage geometric-fibre exchange, the overfield formula, and
representative independence.  The finite-stage inequality is non-strict, so the
identity-stage case remains included.  No hypothesis or conclusion clause was
added, dropped, or weakened.
