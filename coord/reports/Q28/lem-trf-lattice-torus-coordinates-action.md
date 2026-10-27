## Worker report

The module `Sheaf.AlgebraicGeometry.LatticeTorusCoordinatesAction` states all clauses of
`lem-trf-lattice-torus-coordinates-action` in six theorems. Every proof is `sorry`.
It introduces no definition, changes no statement, and repairs no dependency record.

Source read: ILO, Travaux de Gabber, Exposé VIII, printed pp.103–104, Proposition
3.2.2 (realization by affine monoid-algebra gluing and localization compatibility),
3.2.4 (the generic split torus and its extended action), Remark 3.2.5 (including
non-normal toric schemes), and Lemma 3.2.12(i). The source permits nonsaturated and
nonseparated objects; neither restriction is imposed here.

Hypothesis and clause correspondence:

* The field is `(k : Type u) [Field k]`. An abelian lattice is `(L : Type u)
  [CommGroup L]`, written multiplicatively exactly as in the recorded monoscheme
  interface. Thus `single l 1` is the node's `e^l`, and lattice multiplication is
  the node's addition. `(r : ℕ)` allows zero. The specified integral basis is its
  coordinate equivalence `b : L ≃* Multiplicative (Fin r → ℤ)`; its inverse on the
  standard vector is the chosen basis vector. This is precisely the data of a
  finite integral basis, not a new freeness assumption.
* `latticeTorus_coordinates` supplies the k-algebra equivalence `e` to the monoid
  algebra of integer exponent vectors. That algebra consists of finite sums of
  Laurent monomials. The forward and inverse `single` equations specify both
  directions on every monomial, hence exactly the displayed basis-coordinate map.
  The following three equations preserve comultiplication, counit and antipode.
  These are Mathlib's canonical group-algebra Hopf operations, with formulas
  `e^l ↦ e^l ⊗ e^l`, `e^l ↦ 1` and `e^l ↦ e^(−l)`. The last existential is an
  isomorphism in `Grp (Over (Spec k))`; its underlying map is required to be
  `Spec.map e.symm`, so it is the very coordinate identification. On the target,
  the same canonical Hopf structure gives coordinate multiplication, ones, and
  inversion on tuples of units. No arbitrary group structure is quantified over.
* For the conditional action clause, `Monoscheme.Fine` includes the finite affine
  cover by its definition. `[ConnectedSpace M.space]` supplies nonemptiness and
  connectedness, and `hM : Fine.IsTorsionFree M` is the stipulated stalk condition.
  `C : ToricComponent M` selects its unique connected component and
  `j : C.lattice ≃* L` records the identified generic lattice. The canonical
  completion used by the dependency is equivalent to the generic stalk group.
  `latticeTorus_action` asserts `IsIso (componentι k C)`, identifying the component
  realization with the whole k[M]. Its `IsCanonicalTorusAction` conjunct is exactly
  the dependency's equation on EVERY component chart using its `coaction`, not
  an unrelated action. This expresses the gluing of the prescribed coactions.
  The `ModObj` carries associativity and unit for the canonical Hopf group object,
  and `action.smul.left = torusAction k C` ties those identities to that glued map.
  Writing the torus as its defining spectrum makes its canonical base structure
  available to instance resolution; it does not replace the dependency's scheme.
* `latticeTorus_baseChange` chooses the R-algebra comparison for every bundled
  k-algebra R, including the zero ring. Its tensor-monomial equation is literally
  `c ⊗ e^l ↦ c t^(b l)`. Its second conjunct is naturality for every k-algebra
  homomorphism, so it includes restriction along arbitrary affine open inclusions,
  not just principal opens. Because each comparison is an algebra equivalence,
  constants and all finite sums have the prescribed images as well.
* `latticeTorus_presentation` uses `MvPolynomial (Fin r ⊕ Fin r) R`, with left
  indices for t_i and right indices for u_i. The quotient ideal is exactly the
  span of `X (inl i) * X (inr i) - 1`. The equivalence `q` is an R-algebra
  equivalence, and both generator equations specify the positive and negative
  standard Laurent monomials. These formulas also determine the comparison
  uniquely and thus make it compatible with coefficient restriction.
* `latticeTorus_affineCharts` quantifies over every k-scheme `Y : Over (Spec k)`
  and every affine open presentation `j : Spec R ⟶ Y` over k, with
  `[IsOpenImmersion j.left]`. Every affine open of Y has such a presentation;
  no principal-open or finiteness condition is imposed. The domain of `c` is
  the pullback of the second projection along j, i.e. the stated inverse image.
  Its target is `Spec (R ⊗[k] k[L])`. The two equations identify its projections
  to Spec R and T with the canonical scalar inclusions. Therefore this is the
  canonical affine fiber-product comparison. The universal property determines
  it uniquely; it consequently commutes with restrictions of affine opens.
  Combining it with the preceding two algebra equivalences gives precisely
  the three displayed spectrum presentations, with their specified monomials.
* `latticeTorus_finiteType` quantifies over EVERY k-scheme Y. Its first conjunct
  states `LocallyOfFinitePresentation` for the second projection. The implication
  assumes exactly `LocallyOfFiniteType Y.hom` and `QuasiCompact Y.hom` and gives
  both properties for the product's structure map. The final two conjuncts state
  those same finite-type properties for T itself. No reducedness, separatedness,
  nonemptiness or positive rank assumption occurs in these clauses.

Dependency declarations used (definitions are imported publicly):

* `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`, `Spec.map`.
* `def-sc-group-scheme`: `Mathlib.CategoryTheory.Monoidal.Grp`,
  `CategoryTheory.GrpObj`, `Grp`, with the canonical spectrum instances from
  `Mathlib.AlgebraicGeometry.Group.Affine`. Group-algebra Hopf structures come
  from `Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra`.
* `def-trf-monoscheme-toric-realization`:
  `Sheaf.AlgebraicGeometry.MonoschemeToricRealization`, `Monoscheme.Fine`,
  `Fine.IsTorsionFree`, `ToricComponent`, `ToricComponent.lattice`,
  `componentι`, `componentToBase`, `torusAction`, `IsCanonicalTorusAction`.
  Their full definitions and source docstrings were read. In particular the
  canonical-action predicate fixes the coaction on each chart via
  `chartProductMap` and `pullbackSpecIso`.
* `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
* `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
* `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`,
  `AlgebraicGeometry.LocallyOfFiniteType` and `QuasiCompact`, used together as
  specified in this dependency's lean.note.

Proof-only imports include the stated fine-fan interface, Mathlib scheme gluing
and pullbacks. The proof dependencies lacking a recorded Lean declaration are not
invented or imported under guessed names. The entire natural-language proof is
carried by the theorem docstrings, divided according to the node's ten steps.

Searches actually run:

* LeanFinder via msearch: “A lattice basis identifies its group algebra spectrum
  with a split torus, with Hopf operations and glued monomial actions and Laurent
  base change”. Eight hits, including `MonoidAlgebra.instHopfAlgebra` and
  `.instHopfAlgebraStruct` and number-field lattice results; no combined statement.
* Loogle via msearch: `MonoidAlgebra.domCongr`. Twelve hits, including the
  coordinate algebra equivalence, its single-monomial and coefficient formulas,
  and `MonoidAlgebra.counit_domCongr`. These supply ingredients but no scheme
  comparison, glued action and arbitrary-base presentations together.
* LeanSearch via msearch: “A finite free abelian group algebra is a Laurent
  polynomial ring and its spectrum is a split torus”. Eight hits, including
  `LaurentPolynomial`, its localization, and
  `AddMonoidAlgebra.finiteType_iff_group_fg`; no match for this node.
* Mathlib grep via msearch: `comul_single|antipode_single` in
  `RingTheory/HopfAlgebra`. Three hits in the monoid-algebra file, giving the
  antipode formula, not the complete statement. Direct rg also inspected
  `domCongr`, `mapAlgHom`, `mapRingHom`, Hopf spectrum instances and Spec maps.
* Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for lattice-torus,
  Laurent-base-change and canonical torus action patterns found the recorded
  monoscheme interface and the downstream `ToricRealizationFiniteType` module.
  The latter states a different theorem over ℚ, including smoothness and
  reducedness, and is a consumer of this node: importing it would be circular.
  No occurrence of the item id was found in `lean/WeilConjectures`.
* Exact proposed declaration names were searched in Mathlib, WeilConjectures,
  Sheaf and `dag/lean_names_upstream.json`; none exists.

Edge cases checked before and after writing: r=0 gives the zero exponent group,
constant Laurent algebra and the quotient of a polynomial ring with no variables
by the zero ideal. Negative exponents are retained as integer vectors. Empty Y is
allowed in every projection statement. The zero coefficient ring is allowed by
`CommAlgCat` with no nontriviality binder. Arbitrary characteristic is allowed.
The action requires nonempty connected M exactly where the node does; no
saturation, normality or separatedness is imposed (e.g. the cusp monoid ⟨2,3⟩
is not excluded). Charts need not have affine pairwise intersections: the proof
uses shared basic monoidal neighbourhoods and scheme gluing on a cover.

Compilation: scompile.py compiled the final module twice, as the sandbox and as
its actual library module, with no errors or warnings, 2.5 seconds each. The only
elaboration repair was exposing the definitionally identical spectrum in the
ModObj type to obtain its canonical Over/GrpObj instances. No build was run locally.

No STATEMENT-DISPUTED issue or source correction was found.

## Second reading by Q28

I reread the DAG statement and the final module side by side after compilation.
The six declarations cover coordinates and the inverse, all three Hopf operations,
the specified group-scheme isomorphism, the conditional glued action with its two
identities, arbitrary affine inverse-image charts, both Laurent comparisons,
coefficient/restriction naturality, local finite presentation and both finite-type
claims. The quotient has exactly r relations and 2r variables, allowing zero of
both. The chart comparison is constrained by BOTH projections, and the action is
constrained by the recorded chart predicate and the smul equality. The only
source-to-Lean change of notation is multiplicative notation for the lattice.
No added reducedness, separatedness, saturation or nonzero-ring premise was found.
This is a second pass by the dispatched worker, not a claimed independent agent
review; the dispatch instructions prohibit starting other agents. The maintainer
provides the independent review of the delivery.
