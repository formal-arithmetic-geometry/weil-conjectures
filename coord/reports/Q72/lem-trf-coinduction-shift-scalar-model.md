## Worker report

The module `Sheaf.Algebra.Homology.CoinductionShiftScalarModel` states
`ModuleCat.coinduction_shift_scalar_model` with one `sorry`. The auxiliary structure
`CochainComplex.ModuleHomShiftComparison` packages precisely the simultaneous-shift
isomorphisms, their signed component formula, naturality and chain-map normalization.
It introduces no second Hom complex, shift, K-injectivity or coinduction construction.
Its data are structure fields; existence is part of the item's theorem, not an axiom
or a definition with postponed data. All new declarations belong to this item.

Sources read: Stacks `dualizing.tex`, `lemma-right-adjoint` (0A70),
`lemma-RHom-ext` (0A71), and `lemma-relative-dualizing-algebraic` (0BZW), especially
proof (1)(c), where the equal shifts cancel in the P-linear double Hom. Also read
the current blueprint's `lem-trf-local-term-locality` statement and proof under
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/`.
The present node is the extracted algebraic signed calculation, not that unit's
own statement. No statement correction, disputed statement, new DAG node or dependency
repair is needed.

Hypotheses and clauses, in the order of the node:

- The commutative rings and their homomorphism are `{P A : Type u}`,
  `[CommRing P] [CommRing A]`, and `(φ : P →+* A)`. The independent derived
  morphism universes `wP` and `wA` are explicit `HasDerivedCategory` parameters,
  so choosing derived categories is size data, not a mathematical restriction.
- Unbounded complexes are `CochainComplex (ModuleCat.{u} R) ℤ`, for either ring.
  Restriction U is exactly `(restrictScalars φ).mapHomologicalComplex (.up ℤ)`.
- Coinduction J is the recorded `coinductionComplexFunctor φ`, whose actual
  definition is termwise `coextendScalars`, with `CoextendScalars.equiv` identifying
  degree i with Hom_P(A,K^i). Its action is (ah)(b)=h(ba). Its identification
  with the product Hom from A[0] is already a clause of the recorded
  `coinduction_total_hom_model`; the theorem does not replace V by an unrelated complex.
- Product Hom is the recorded `CochainComplex.moduleHomComplex`, in every occurrence.
  Its cochains are the existing `HomComplex.Cochain` and its differential is `δ`.
- The shifts are the existing `L⟦n⟧`, with degree i term L^(i+n) and differential
  `n.negOnePow` times d. All n and all Hom degrees r range over ℤ.
- `σP` and `σA` are simultaneous-shift comparisons over the respective rings,
  for arbitrary L and M. `ModuleHomShiftComparison.iso` has exactly the displayed
  source and target of sigma. `component` states the factor `(n*r).negOnePow`.
  The indices satisfy p=p'+n and q=q'+n, so the source component is f^(p-n).
  `shiftFunctorObjXIso` explicitly supplies the ordinary index identifications.
- `naturality` is the equation for both precomposition by a and postcomposition by b,
  using `Cochain.ofHom` and cochain composition, with their shifted chain maps on
  the left. `ofHom` states sigma(ofHom(f[n]))=ofHom(f); thus degree zero is the
  usual inverse shift, with no sign. Since shift is an equivalence, this also
  specifies its action on every map between the shifted complexes.
- The two K-injectivity conjuncts say `K.IsKInjective → (K⟦n⟧).IsKInjective`
  over P and A, including arbitrary unbounded K.
- `j K n` is J(K[n]) ≅ J(K)[n]. Its degreewise hom is `𝟙 _`, recording the
  literal term identification with the same differential and A-action.
  The next conjunct states naturality for every K→K'. This expresses the
  node's equality as the identity-component chain identification.
- `T` is an isomorphism with exactly the dependency's total-Hom source and target;
  its formula conjunct states evaluation of every homogeneous cochain at one,
  using `CoextendScalars.equiv`. This determines every component of T uniquely
  and hence identifies it with the evaluation transposition of the dependency,
  rather than assuming an arbitrary natural isomorphism.
- `t E K n` expresses `T_(E[n],K[n])` after the identity component identifications
  J(K[n])=J(K)[n] and U(E[n])=(UE)[n]. Its own component formula is evaluation
  at one in `K.X (q+n)`. Thus it is uniquely the transported shifted T. The
  following conjunct is the commuting simultaneous-shift/transposition square
  in every Hom degree r; it is equality of the evaluations of the actual maps,
  and therefore specifies the chain-map equality degree by degree.
- A K-injective complex representing P[0] is `(I : CochainComplex ... ℤ)` with
  `[I.IsKInjective]` and `_e : Q.obj I ≅ Q.obj (singleFunctor ... 0).obj (of P P)`.
  The explicit isomorphism `_e` expresses “representing P[0]”; its particular value
  is irrelevant to the canonical comparison, not a hollow hypothesis.
- The derived comparison conjunct equates two paths from C(Q(I[n])) to
  C(QI)[n]. The first is C applied to Q's shift comparison, followed by
  `Functor.commShiftIso` with the precise instance
  `(derivedCoinductionAdjunction φ).rightAdjointCommShift ℤ`, and the shifted
  `derivedCoinductionModel φ I`. The second is the shifted K-injective model,
  Q applied to j, and Q's shift comparison. This is the canonical adjunction-mate
  comparison represented by the identity component coinduction identification.
  Together with `_e`, it is exactly C(P[n]) ≅ C(P[0])[n]. Shifted K-injectivity
  is also supplied by the existing Mathlib instance, so no extra assumption is added.
- In the final conjunct, V is `(coinductionComplexFunctor φ).obj I` and `m n`
  is an actual chain map from A[0] over P to U(Hom_A(V[n],V[n])). Its formula
  is multiplication `a • h`. The `singleObjXSelf` inverse explicitly places
  `a : A` in degree zero of A[0]. All other source degrees are zero.
- `δI` is an actual chain map A[0]→Hom_P(UV,I), with component formula
  `CoextendScalars.equiv φ (I.X p) h a`, namely h(a). Again the source is the
  recorded single complex, not an untyped degree-zero element.
- The last conjunct is the equality of actual chain maps
  `m n ≫ (t V I n).hom ≫ (σP.iso (UV) I n).hom = δI`. Categorical composition
  has the reverse written order from the node's function-composition notation.
- There are no bounds, perfectness, flatness, Noetherian or nonzero-ring assumptions.
  The rings and their module categories use a common ambient universe, as do the
  recorded dependency interfaces; any two ring sizes are accommodated by an ambient
  maximum. There is no independently smaller test-object universe.

Dependencies read and used:

1. `def-sc-module-total-hom-complex`: module
   `WeilConjectures.Algebra.Homology.ModuleHomComplex`, declaration
   `CochainComplex.moduleHomComplex`, with its complete terms/differential read.
2. `def-pur-kinjective-complex`: the Mathlib match
   `CochainComplex.IsKInjective` in
   `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`, including its acyclic-source
   null-homotopy definition and the shift-preservation instance. Ordinary modules
   give the one-object identity-cover site specialization used by this node.
3. `def-weil-abstract-derived-category`: the recorded module
   `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
   `HasDerivedCategory`, `DerivedCategory.Q`, and Q's `CommShift` structure.
4. `def-trf-derived-coinduction`: module
   `Sheaf.Algebra.Homology.DerivedCoinductionAdjunction`, declarations
   `ModuleCat.derivedCoinduction`, `coinductionComplexFunctor`,
   `derivedCoinductionModel`, and `derivedCoinductionAdjunction`.
   Read their full definitions and docstrings: the derived functor uses the existing
   K-injective construction, the model is its canonical comparison, and the adjunction
   is the derived ordinary restriction/coextension adjunction.
5. `lem-trf-coinduction-total-hom-model`: module
   `Sheaf.Algebra.Homology.CoinductionTotalHomModel`, theorem
   `ModuleCat.coinduction_total_hom_model`. Read its signature and proof docstring:
   product Hom identification, T and inverse formulas in every degree, differential
   and naturality, homotopies, K-injectivity preservation, and underlying derived Hom.
   Its T formula is reproduced as a characterization of the witness of this item;
   no new construction of T or definition node is introduced.

Additional Mathlib APIs used directly are `Cochain.shift` and its component/differential
formulas from `HomComplexShift`, and `Adjunction.rightAdjointCommShift` from
`Mathlib.CategoryTheory.Shift.Adjunction`. They are not redefined. The comparison
structure is only a named conjunction of the witnesses and properties already requested
by this node, with no postponed proofs inside a definition.

Edge cases checked mathematically: n=0 gives the identity reindexing and sign;
n=1 and n=-1, r=1 and r=-1 give the expected odd sign; r=0 always gives +1.
In characteristic two both signs become one, and all equations still hold.
Zero complexes and the zero ring produce the zero scalar maps. A field with
I=P[0] reduces the last equality to (a·h)(1)=h(a). Arbitrarily unbounded
complexes have all product factors, with no finite-support requirement.

Searches actually run with `msearch.py Q72 lem-trf-coinduction-shift-scalar-model`:

- LeanFinder: “Simultaneous shift total Hom complex sign (-1)^(nr), coinduction
  evaluation at one and scalar normalization”. Eight hits, including
  `Cochain.leftShift_v`, `leftUnshift_v`, `leftUnshift`, and total-complex shift
  isomorphisms. None states the full coinduction/scalar identity.
- Loogle: `CochainComplex.HomComplex.Cochain.shift, CochainComplex.isKInjective_shift_iff`.
  Successful query, zero hits.
- Grep: `shift.*[Hh]om|[Hh]om.*shift|coinduc` in `Algebra/Homology`.
  Twenty-five hits, concerning general Hom/total-complex shifts. Read
  `HomComplexShift.lean`, `KInjective.lean`, and the termwise shift comparison
  in `HomotopyCategory/Shift.lean`; no full-node match.
- LeanSearch: “Signed simultaneous shift isomorphism of module total Hom complexes
  compatible with coinduction evaluation and scalar multiplication”. Eight hits,
  including `Cochain.shift`, `leftUnshift_v`, `leftShiftLinearEquiv`, and bicomplex
  total-shift isomorphisms; no full-node match.
- Direct `rg` over `lean/WeilConjectures` and `lean/Sheaf` for simultaneous shifts,
  coinduction shifts, and the two chosen declaration names found the already recorded
  coinduction/shriek modules but no theorem stating this full node. The downstream
  `coinductionHomShift` was read; this module constructs the canonical mate directly
  from the dependency adjunction and does not import the downstream consumer.
- Direct node-id search in `lean/WeilConjectures` and `dag/lean_names_upstream.json`
  returned no matching declaration. The chosen structure/theorem names also do not
  occur in Mathlib or the project.

Server validation: the prescribed `scompile.py` compiled this file independently
in sandbox and library module modes (3.0 s and 2.9 s), with no errors or unexpected
warnings. `set_option autoImplicit false` checks all variables are explicitly bound.
The file has no proof except the single theorem's `sorry`, and all lines fit 100 columns.
The theorem's seven-step docstring carries the full node proof and its dependencies.

## Second reading by Q72

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
