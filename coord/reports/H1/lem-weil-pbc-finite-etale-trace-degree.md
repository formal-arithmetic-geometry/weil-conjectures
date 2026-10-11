## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteEtaleTraceDegree` states
`AlgebraicGeometry.Etale.exists_finiteEtaleTrace_degree`.

The hypothesis `[ConnectedSpace X]` renders that `X` is connected (the dependency
`def-weil-connected-scheme`, represented by Mathlib's `ConnectedSpace`), while
`f : Y ⟶ X` with `[IsFinite f] [Etale f]` renders a finite étale morphism.  The
existential `d : ℕ` is the common degree.  The witness
`f.IsFiniteLocallyFreeOfDegree d` is exactly clause (a), using the recorded
source declaration `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFreeOfDegree`.

For every geometric point `x : Spec (.of Ω) ⟶ X`, with `[Field Ω]
[IsAlgClosed Ω]`, the conjunct `Finite ↥(pullback f x : Scheme.{u})` states that the
geometric fibre has finitely many points, and
`Nat.card ↥(pullback f x : Scheme.{u}) = d` states clause (b), exactly `d` points.
The parenthetical assertion that the fibre is a coproduct is rendered by
`Nonempty (Over.mk (pullback.snd f x) ≅
Over.mk (Sigma.desc fun _ : Fin d ↦ 𝟙 (Spec (.of Ω))))`: the isomorphism is
in the category of schemes over `Spec Ω`, not only of underlying schemes.
The final universal quantifier over
`F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}` is every abelian sheaf on
`X_\Et`; the equation
`finiteEtaleRestriction f F ≫ finiteEtaleTrace f F = d • 𝟙 F` is clause (c),
restriction followed by trace being multiplication by `d`.

The restriction and trace declarations used are
`AlgebraicGeometry.Etale.finiteEtaleRestriction` and
`AlgebraicGeometry.Etale.finiteEtaleTrace` from
`Sheaf.AlgebraicGeometry.FiniteEtaleTrace` (dependency
`def-weil-pbc-finite-etale-trace`).  The degree class is
`AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFreeOfDegree` from
`WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree` (dependency
`def-pc-finite-locally-free`).  The geometric point convention is rendered by
`Spec (.of Ω) ⟶ X` with `Field Ω` and `IsAlgClosed Ω`, matching the recorded
Mathlib match `Scheme.SpecToEquivOfField` and `IsAlgClosed` for
`def-weil-geometric-point`.  `ConnectedSpace` is the recorded Mathlib match for
`def-weil-connected-scheme`; scheme/morphism conventions and the abelian étale
sheaf are supplied by their dependency records.

Edge cases checked: `d` is a natural number and therefore permits `d = 0`; the
empty geometric fibre is represented by `Finite` with `Nat.card = 0`; no
nonemptiness of `X` beyond `ConnectedSpace` is added; arbitrary algebraically
closed fields in the same universe are allowed; and the scalar multiple equation
also covers the zero sheaf and arbitrary coefficient torsion.

Searches made:

* LeanFinder (`msearch.py ... leanfinder "finite etale morphism connected scheme constant degree trace restriction multiplication"`): finite étale algebra product results and étale API only; no theorem for this scheme trace-degree statement.
* Loogle (`... loogle "Nat.card, IsFiniteLocallyFreeOfDegree, finiteEtaleTrace, finiteEtaleRestriction"`): unavailable identifier `IsFiniteLocallyFreeOfDegree`; no match.
* Mathlib grep (`... grep "finiteEtaleTrace|IsFiniteLocallyFreeOfDegree|Nat.card.*pullback" Mathlib`): no hits.
* `rg` over `WeilConjectures/` for `lem-weil-pbc-finite-etale-trace-degree`, `finiteEtale.*degree`, and trace/restriction names: no declaration of this theorem.
* `rg` over project `lean/Sheaf/` found only the preceding trace definition and unrelated fibre-cardinality statements; no duplicate declaration.

No statement correction, new node, dependency module, or `STATEMENT-DISPUTED` flag was needed.

## Earlier second reading (a previous round; superseded)

Independent second reading is reserved for the second worker. The following is the
statement writer's final self-check. I reread the node and the module side by side. The connected-scheme and finite-étale
hypotheses are exactly `[ConnectedSpace X]`, `f : Y ⟶ X`, `[IsFinite f]`, and `[Etale f]`.
The existential natural number and the `IsFiniteLocallyFreeOfDegree` witness render the
constant finite locally free degree clause. The geometric-point binders keep the same
universe and add only the field/algebraic-closure structure required by the node; the
`Finite` and `Nat.card` conjuncts render finiteness and exactly `d` points of the pullback
geometric fibre. The last binder ranges over precisely the abelian étale sheaves used by
the trace definition, and its composition equation is unchanged. The module remains a
statement-only theorem with `sorry`; no hypotheses or clauses were changed.

Final clause check added the explicit isomorphism over `Spec Ω` to the coproduct
indexed by `Fin d`, retaining the point count. The docstring now records all eight
proof steps, with their cited nodes. No independent second reading is claimed here.

Additional search: LeanSearch (`msearch.py ... leansearch "finite etale cover over
connected scheme has constant degree and trace restriction composite multiplication
by degree"`) returned HTTP 500 / service unavailable, recorded as unavailable.

Source checked at [Stacks 03SH](https://stacks.math.columbia.edu/tag/03SH),
paragraphs following Definition 03SE, and [04HN](https://stacks.math.columbia.edu/tag/04HN).
The local source text is not present on this machine; the official pages give the
trace characterisation and étale local splitting used in the node's proof.

## Second reading by H1

I read the node statement and the module signature item by item. The node introduces a
connected scheme (X), a finite étale morphism (f:Y\to X), and a natural number (d\geq0).
These are rendered by `{X Y : Scheme.{u}} [ConnectedSpace X]`, `f : Y ⟶ X`,
`[IsFinite f] [Etale f]`, and `d : ℕ`, respectively. `ConnectedSpace` includes the
nonempty condition required by `def-weil-connected-scheme`; no extra scheme hypothesis is
present.

Clause (a), finite locally free of degree (d), is exactly the existential witness
`f.IsFiniteLocallyFreeOfDegree d`, using the recorded declaration from
`WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`. Clause (b) quantifies over every
geometric point: the module uses `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]` and
`x : Spec (.of Ω) ⟶ X`, matching the recorded geometric-point convention. Its three
conjuncts render finiteness of the fibre point set, cardinality `Nat.card = d`, and the
coproduct assertion as a nonempty isomorphism over `Spec Ω` from the pullback to the
`Fin d`-indexed coproduct of copies of `Spec Ω`. This includes `d = 0` and empty fibres.
Clause (c) quantifies over precisely
`F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})` and states
`finiteEtaleRestriction f F ≫ finiteEtaleTrace f F = d • 𝟙 F`; the two declarations are the
restriction and trace of the dependency node, so the composition and scalar multiplication
are exactly the node's restriction-then-trace equation.

The universe is shared with the scheme, as in the project's geometric-point convention and
its other statements; the module has no unbound variables. The empty-index case `Fin 0`,
the zero sheaf, and arbitrary characteristic/torsion are all admitted. Since
`ConnectedSpace` supplies a point, the source's connectedness convention is respected.

I searched LeanFinder and Loogle for finite étale degree and trace-composition statements,
Mathlib for `finiteEtaleTrace`, `IsFiniteLocallyFreeOfDegree`, and fibre-cardinality APIs,
`WeilConjectures/` for the theorem, and `lean/Sheaf/` for duplicate declarations. Only the
recorded degree, restriction, and trace declarations were found; no existing theorem matches
this node. The worker module already compiles cleanly with `scompile.py`. I found no
statement mismatch, no dependency mismatch, and made no source changes.
