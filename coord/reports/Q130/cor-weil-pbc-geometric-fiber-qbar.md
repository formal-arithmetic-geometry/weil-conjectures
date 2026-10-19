## Worker report

The module `Sheaf.Paper.GeometricFiberQbar` states
`AlgebraicGeometry.Scheme.geometricFiber_qbar_properBaseChange`, with proof `sorry`.
It specializes the existing canonical exchange presentation to the scheme-theoretic
geometric fiber. No definitions, assumptions of constructible preservation, auxiliary
nodes, dependency repairs, or statement corrections are introduced.

Source read: `literature/blueprint/main-20261015/blueprint/sec-proper-base-change/`
`sk-thm-properbasechange/cor-weil-pbc-geometric-fiber-qbar.md`, its displayed exchange
and final representative sentence, together with the full DAG statement and proof.
There is no repair note for this item.

Hypothesis and clause correspondence:

- A prime ell is `(l : ℕ) [Fact l.Prime]`.
- Its chosen algebraic closure is `(Qbar : Type w) [Field Qbar]`
  `[Algebra ℚ_[l] Qbar] [IsAlgClosure ℚ_[l] Qbar]`. Its universe `w` is
  independent of the scheme universe `u`.
- The proper morphism is `{X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]`.
- The geometric point is `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]`
  `(ybar : Spec (.of Ω) ⟶ Y)`. Here Ω is the geometric-point field, and Qbar
  is the coefficient field; they are not identified.
- `P = Spec Ω` and `X_ybar = pullback f ybar` use Mathlib's chosen scheme
  fiber product. Their two projections are those in `geometricFiberSquare f ybar`:
  `pullback.fst f ybar` is i_ybar and `pullback.snd f ybar` is a_ybar.
- Noetherianity of each of X, Y, X_ybar and P is a separate `IsNoetherian` binder.
- Finite dimension of each is a separate `Fact (∃ n : ℕ, topologicalKrullDim ... ≤ n)`
  binder, exactly as required by the existing Qbar-category interface.
  The recorded `Scheme.dim_eq_topologicalKrullDim` identifies these with finite
  dimension using the recorded local-ring dimension. It is a proved theorem in the
  imported dimension module, including for the empty scheme.
- Invertibility of ell on each of the four schemes is a separate `Fact` binder
  asserting `∀ t, IsUnit (l : ...presheaf.stalk t)`. This is the stalkwise
  formulation used by the Qbar categories and the scalar system; it says exactly
  that ell is invertible on that scheme. It is equivalent to the global-section
  formulation used by the finite-extension corollary (units are local).
- Properness of a_ybar is retained as `[IsProper (pullback.snd f ybar)]`.
- The bound e ≥ 0 is `(e : ℕ)`, and `_hFibres` bounds the recorded
  `(pullback f y : Scheme.{u}).dim` by e for every algebraically closed
  geometric-point field Ω' and every y. No nonemptiness of a fiber is required.
- The square `(f,a_ybar,ybar,i_ybar,id)` is literally
  `geometricFiberSquare f ybar`, whose definition uses `Iso.refl` on this
  chosen scheme pullback. No arbitrary square or arbitrary identification is substituted.
- The functors and exchange are supplied in the conclusion by
  `∃ P : PbcQbarExchangePresentation l Qbar (geometricFiberSquare f ybar)`.
  This existing structure supplies constructible-preservation witnesses, four exact
  coherent stage families, their equality to the actual rational direct images and
  completed pullbacks, all four canonical beta specifications, and `exchange_eq`
  fixing the actual localized completed exchange. These are conclusions, never
  additional hypotheses. The letter P in this existential is a presentation, not
  the geometric-point scheme, which is always written `Spec (.of Ω)` in Lean.
- For every `K : pbcQbarCategory l Qbar X`, the first conjunct
  `IsIso (P.exchange.app K)` is the displayed descended geometric-fiber formula.
  The source is the composite Rf then Lybar, and the target is Li_ybar then Ra,
  as specified by the types of `P.exchange` and `geometricFiberSquare`.
- For the object's actual representative `(K.stage, K.obj)`, the next existential
  supplies a finite coefficient field M and `h : K.stage ≤ M`, so M contains E.
  The scalar extension is `((pbcScalarSystem ...).T h).obj K.obj`, the existing
  rationalized integral scalar-extension functor with literal identity at equal fields.
- `IsIso ((P.Ex.τ M).app (...))` states that the representing finite-stage
  geometric-fiber exchange is an isomorphism. This is the actual finite-extension
  exchange: `P.exchange_eq` fixes it on every raw rational object by its integral
  representative, using the canonical small model of M and its coefficient-ring
  normalization. The same localized completed mate occurs in
  `finiteExtensionRationalExchangeComponent` in the finite-extension corollary.
- The final equality identifies the descended component with
  `PbcQbarExchangePresentation.atStage ... P K M h`. That definition is explicitly
  `PairCategory.mkHom` of the M-component on the scalar extension, conjugated by
  the two canonical composite beta comparisons. Thus it identifies the specified
  morphism with the finite-stage representative, rather than asserting only an
  unrelated isomorphism of its source and target. The node requests some finite
  overfield, so this corollary uses an existential M rather than the stronger
  every-overfield/representative-independence clauses of the general theorem.

Dependency declarations inspected and used:

- `Sheaf.Paper.PbcQbarCategory`: `AlgebraicGeometry.Scheme.pbcQbarCategory`;
  the unchanged raw finite-stage pair category, with no Karoubi envelope.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the geometric-point
  representation is the recorded inline one. Also read the signature and docstring
  of `Scheme.SpecToEquivOfField` in `Mathlib.AlgebraicGeometry.ResidueField`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, and the universal-property declarations.
- `Sheaf.Paper.GeometricFiberFiniteExtension`: `geometricFiberSquare` and
  `geometricFiber_finiteExtension_properBaseChange`, including its full signature,
  raw coefficient category, preservation witnesses and exchange component.
- `Sheaf.AlgebraicGeometry.Dimension`: `Scheme.dim` and its proved comparison
  `Scheme.dim_eq_topologicalKrullDim`.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `ChosenCartesianSquare`,
  including the two projection equations for its chosen pullback identification.
- `Sheaf.Paper.PbcDescentFunctors`: `pbcDescentFunctors`,
  `pbcDescentDirectImage`, `pbcDescentPullback`, `PbcDirectImageBetaSpec`,
  `PbcPullbackBetaSpec`, and `pbcDescentOperations`. The presentation reuses these
  actual operations and their canonical comparisons.
- `Sheaf.Paper.PbcScalarExtension`: `pbcCoherentScalarExtension` and the
  rational tensor/identity normalization interfaces. The pair-category interface
  `pbcScalarSystem` from `Sheaf.Paper.FiniteStagePairCategory` exposes their
  canonically normalized raw rational scalar extensions at small field models.
- The stated proof dependency `Sheaf.Paper.QbarProperBaseChange` supplies
  `PbcQbarExchangePresentation`, its `exchange` and `atStage`, and
  `qbar_properBaseChange`. The first three are the existing interface for the
  descended exchange in the statement; the latter is the theorem to specialize
  in stage 3. Its module must be public because the statement uses that interface.

All these are available through the two proper-base-change imports and the direct
public import of the recorded dimension module. No imported proof dependency is
left out, and no existing notion is privately reconstructed.

Edge cases checked before writing:

- K = 0 and empty X or empty geometric fiber remain allowed; the formula is on
  the same categories, and dimension of an empty scheme is bottom, so its bound holds.
- e = 0 is allowed; there is no positivity or nonempty-fiber hypothesis.
- M = E is allowed by `≤`; the existing scalar system uses its literal identity
  normalization, and atStage retains the associated unit comparisons.
- f = identity and arbitrary geometric points are allowed.
- Characteristic ell is excluded precisely by the stipulated invertibility hypothesis.
- No constraint equates the coefficient closure's universe w with the scheme universe u.

Searches for an existing exact statement (run through the prescribed msearch wrapper):

- LeanSearch, `proper base change geometric fiber constructible Qbar l coefficients`:
  eight hits concerning scheme-morphism stability under base change and tensor-product
  universal properties; no Qbar constructible geometric-fiber exchange statement.
- LeanFinder, `proper base change geometric fiber formula for constructible Q_l
  algebraic closure sheaves`: eight hits on scheme pullback/residue-field constructions
  and ordinary module pullback composition; no match.
- Loogle, `CategoryTheory.IsIso, CategoryTheory.NatTrans`: zero hits.
- Mathlib grep, `geometric.*[Ff]ib[er]+.*[Qq]bar|[Qq]bar.*geometric.*[Ff]ib[er]+`:
  zero hits.
- rg in the upstream `WeilConjectures` and side `lean/Sheaf` sources for
  `geometricFiber.*[Qq]bar|[Qq]bar.*geometricFiber|geometric.fiber.qbar|qbar_properBaseChange`:
  no upstream match; side hits include the general `qbar_properBaseChange` and
  unrelated Weil-category geometric-fiber constructions, not this corollary.
- The prescribed upstream grep for the literal node id found no match.
- The upstream declaration-name index contains no matching corollary declaration.

The general Qbar theorem is more general and has different binders and conclusion
clauses; it is used as the proof dependency and the canonical interface, not recorded
as an exact existing match for this specialized corollary. No statement dispute or
node fault was found. Every theorem proof in the new module is exactly `sorry`.

## Second reading by Q130

No independent worker reading is claimed. This dispatcher worker delivers directly;
the maintainer performs the independent review. In a separate author rereading with
both node and final module open, the four noetherian, four finite-dimension and four
invertibility hypotheses, both properness hypotheses, geometric-field algebraic
closure, nonnegative uniform fiber bound, identity chosen fiber square, descended
isomorphism, finite-overfield containment, scalar-extended object, finite-stage
isomorphism and representative equality all have the counterparts listed above.
The geometric-point field and coefficient closure stay separate. The first compile
found that an unannotated `pullback` in a point-type binder was inferred in the category
of types; adding the explicit `Scheme.{u}` annotation repaired elaboration. The fiber
bound uses the recorded local-ring dimension, with its proved topological comparison.
No mathematical mismatch or statement change was needed.
