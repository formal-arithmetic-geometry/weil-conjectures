## Worker report

Item: `lem-trf-split-unit-group-ideal-tensor`. Module:
`Sheaf.RingTheory.SplitUnitGroupIdealTensor`; main declaration:
`MonoidAlgebra.SplitUnitGroupIdealTensor.split_unit_group_ideal_tensor`.
The theorem is stated with `sorry`; no theorem is proved. The five construction helpers
and `Comparison` have actual data, with no `sorry` in any definition.
Only the item's `lean` field changes. There are no new nodes, dependency repairs,
statement corrections, or disputed statements.

### Hypotheses and objects

- The source's additive commutative monoid Q is `[CommMonoid Q]`, written
  multiplicatively, and its additive abelian group G is `[CommGroup G]`.
  This changes notation only: source `q+r` is `q*r`, source `0` is `1`.
  These types have independent universes `u`, `v`.
- The commutative coefficient ring is `{A : Type w} [CommRing A]`;
  `c : Q →* A` and `v : G →* Aˣ` are exactly the chosen characters.
  No nontriviality, domain, flatness, or cancellation hypothesis is imposed.
- The monoid ideal, including the empty set, is `K : Set Q` with
  `hK : ∀ q ∈ K, ∀ r : Q, q * r ∈ K`.
- Integer monoid rings are Mathlib's `MonoidAlgebra ℤ Q` and
  `MonoidAlgebra ℤ (Q × G)`. The direct sum of two monoids here is the product;
  the subset L is literally `K ×ˢ Set.univ`.
- `I` and `J` name the ideals Z[K] and Z[L]. Their binders `hI` and `hJ` fix
  them to `Ideal.span (MonoidAlgebra.of ℤ Q '' K)` and
  `Ideal.span (MonoidAlgebra.of ℤ (Q × G) '' (K ×ˢ Set.univ))` respectively.
  These equalities only name the uniquely specified ideals, imposing no restriction
  on K or the characters. Closure `hK` ensures the ring ideal span is the integer
  additive span intended by the source. No duplicate monomial-ideal definition is made.
- `evaluation c` is `(MonoidAlgebra.lift ℤ A Q c).toRingHom`.
  `splitEvaluation c v` uses `c.coprod ((Units.coeHom A).comp v)`, so its
  value on z^(q,g) is c(q)v(g). Their `RingHom.toAlgebra` structures give
  exactly the specified actions on A, including A_c.

### Clauses of the conclusion

1. Ideal extension: the first conjunct is
   `I.map (MonoidAlgebra.mapDomainRingHom ℤ (MonoidHom.inl Q G)) = J`.
   The ring hom sends z^q to z^(q,1), source z^(q,0).
2. The A-linear comparison: the existential `σ : Comparison c v I J` supplies
   `σ.equiv : tensor (splitEvaluation c v) J ≃ₗ[A] tensor (evaluation c) I`.
   `tensor e I` is precisely the ordinary Mathlib tensor `A ⊗[R] I` with
   `e.toAlgebra`, bundled in `ModuleCat A` to keep the selected scalar action
   explicit. Tensor symmetry identifies this with the source's `I ⊗[R] A`.
   The helper `pure e I x a` means `a ⊗ₜ[R] x`, so its arguments retain the
   source order (ideal element, coefficient). This is an implementation of the
   given tensor, not a new independent notion or a replacement tensor relation.
3. The displayed formula is `σ.monomial`, quantified over every q, g, a and
   ideal elements x,y equal to z^q and z^(q,g). It states
   `σ.equiv (pure ... y a) = pure ... x ((v g : A) * a)`.
   All required monomials lie in the spans by hI/hJ. Their subtype witnesses
   are quantified rather than constructed with a new postponed membership theorem.
4. The inverse formula and its canonical ideal-tensor interpretation are both
   `σ.inverse`. For every x in I, y in J equal to the actual inclusion image of
   x, and a in A, it states `σ.equiv.symm (pure ... x a) = pure ... y a`.
   Specializing x to z^q gives exactly insertion of the identity group coordinate.
   Quantifying over all x also states the induced inclusion/identity map on all
   pure tensors, not just an unspecified inverse.
5. `multiplication e I` is constructed by `LinearMap.liftBaseChange A` from
   `(Algebra.linearMap R A).comp I.subtype`. Hence it sends `pure e I x a`
   to `a * e x = e x * a`, giving the displayed μ_K and μ_L monomial formulas.
   `σ.multiplication` is the equality of A-linear maps μ_K ∘ σ = μ_L.
6. Coefficient naturality: after choosing σ, the conclusion quantifies over every
   independent `{A' : Type w'}` with `[CommRing A']`, ring hom φ, chosen characters
   c',v', and their pointwise compatibilities `_hc`, `_hv`.
   It supplies `σ' : Comparison c' v' I J` and additive coefficient maps βK,βL.
   The first two conjuncts specify β on every pure tensor as identity on I or J
   and φ on the coefficient, uniquely determining the canonical coefficient maps.
   The third and fourth conjuncts state the σ and inverse σ squares, respectively.
   The fifth and sixth state the μ_K and μ_L squares with φ. Thus “these maps”
   includes the comparison, inverse, and both multiplications.
   Additive maps suffice for coefficient change across different coefficient rings;
   their pure-tensor characterizations also force φ-semilinearity.
   There is no arbitrary-map assumption: all maps are existential conclusions
   completely determined on generating pure tensors.

`Comparison` is only a data package for clauses 2--5 of this very node, not a
hypothesis. It makes no assertion of existence; the theorem supplies that package.
Its structure fields carry precisely the isomorphism and its characterizing equations.
All helpers and the package are recorded in `lean.declarations`.

### Dependency declarations and source reading

The sole statement/proof dependency `def-weil-pbc-module-tensor-product` has
status `mathlib`, with `mathlib_match.declaration = TensorProduct`; it needs no
`lean` record or dependency repair. Read its entire node and the following
recorded Mathlib signatures/docstrings:

- `TensorProduct` and `TensorProduct.tmul` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, lines 81 and 107.
- `TensorProduct.lift`, `lift.tmul`, `ext'` in
  `Mathlib.LinearAlgebra.TensorProduct.Basic`, lines 123, 127, 134.
- `LinearMap.rTensor`, its pure-tensor formula and its definition as
  `TensorProduct.map f LinearMap.id` in
  `Mathlib.LinearAlgebra.TensorProduct.Map`, lines 331--345.

The public import `Mathlib.RingTheory.TensorProduct.Basic` exposes these tensor
constructions and `LinearMap.liftBaseChange`. Other public imports supply the
bundle `ModuleCat`, monoid rings/evaluation, and ideal extension. No extra proof
imports are required: the only proof dependency is already imported publicly.

Read Stacks `algebra.tex`, `lemma-tensor-product`, lines 1716 onward, including
its universal property and generation by pure tensors. Read the actual ILO PDF:
PDF page 81 (printed 75), VI 3.7(a), for the split sharp chart; PDF page 116
(printed 110), VIII 3.4.1--3.4.3, for monoidal ideals and the ideal-tensor context.
The node's elementary calculation is agent-written, rather than a verbatim ILO
lemma. Also read the current blueprint `latest` ancestor
`lem-trf-local-term-locality.md` and its proof: its current proof uses contracting
correspondences, whereas this node retains an older log-chart ancestry.
This inherited route metadata was not changed: it does not affect the valid
standalone algebra statement assigned here.

### Edge cases

- K empty: I and J are zero, both tensors are zero, and every monomial equation
  is vacuous while the all-pure inverse and naturality equations still apply.
- K = Q: both full monoid rings are allowed and the comparison is evaluation
  of the group factor. No proper-ideal hypothesis is present.
- The trivial group G: v(1)=1, and forward/inverse reduce to the identity chart.
- The zero coefficient ring: all coefficient modules and maps are zero;
  neither `[Nontrivial A]` nor `[Nontrivial A']` is used.
- Noncancellative Q and characters c with zeros: balancing only uses the character
  identities; there is no localization, cancellation, or injectivity assertion.
- Trivial Q and a nontrivial group G: either monoid ideal is empty or all of Q,
  and the character evaluation still describes the comparison.
- Independent universes for Q, G, A, A': `tensor` lives in `max u w` as needed;
  no equality of these universes or smallness assumption is imposed.

### Searches actually run

The prescribed `msearch.py Q19 lem-trf-split-unit-group-ideal-tensor` calls
are logged in the sandbox's `searches.jsonl`:

- LeanFinder query: “Eliminating the group factor from a monomial ideal tensor
  over additive monoid algebras using a character into units”. Eight hits,
  including `MvPolynomial.rTensor_apply_monomial_tmul`,
  `AddMonoidAlgebra.scalarTensorEquiv`, `MonoidAlgebra.scalarTensorEquiv_tmul`.
  These concern whole algebras/polynomials, not this arbitrary monomial ideal
  with its inverse, multiplication equations, and coefficient naturality.
- Loogle query: `AddMonoidAlgebra, TensorProduct`. Twelve hits, including
  `AddMonoidAlgebra.scalarTensorEquiv`, `tensorEquiv`, `lTensorAlgEquiv`,
  `rTensorEquivAlgEquiv`; no exact statement.
- Mathlib grep query:
  `AddMonoidAlgebra.*(ideal|tensor)|(ideal|tensor).*AddMonoidAlgebra`.
  Nineteen hits, including `Algebra/MonoidAlgebra/Ideal.lean`, which was read:
  `AddMonoidAlgebra.mem_ideal_span_of'_image` describes ideal membership,
  not the assigned tensor comparison. Other hits are tensor algebra infrastructure.
- LeanSearch query: “A monomial ideal in the integer monoid ring of Q times an
  abelian group tensor a character algebra cancels the group factor”. Eight hits
  on cancellation in monoid algebras and `CancelMonoid`; no matching theorem.
- Direct project `rg` for `split.unit|monomialIdeal|monomial.ideal|groupIdealTensor|
  idealTensor`, and a literal item-id grep in `lean/WeilConjectures`: no exact
  theorem. Read `Sheaf.TraceFormula.LogChartFaceTorComparison` (its ideal/tensor
  helpers are in the downstream parent),
  `Sheaf.AlgebraicGeometry.LogRegularMonomialTensor`, and
  `Sheaf.RingTheory.AffineToricEquivariantIdeals`.
  The first is the downstream chart comparison, the second a geometric
  injectivity theorem, and the third a field-coefficient toric ideal definition;
  none gives the assigned group-factor theorem. This delivery uses `Ideal.span`
  directly rather than copying those monomial-ideal definitions or importing
  the downstream parent.
- Direct name search for `SplitUnitGroupIdealTensor|split_unit_group_ideal_tensor`
  in `dag/lean_names_upstream.json`, Mathlib, `lean/WeilConjectures`, and
  `lean/Sheaf`: no existing declaration.

### Validation

The prescribed server `scompile.py` compiled both sandbox and module successfully
(6.7 s and 9.1 s), with no errors or warnings. An initial compile found the
incorrect API spelling `Units.valHom`; reading Mathlib located `Units.coeHom`,
which was substituted before the clean compile. No `#check` commands remain.
All universes and variables are explicitly bound; `autoImplicit` is false.
The node JSON is serialized with indent 1, Unicode retained, and a final newline.

## Second reading by Q19

Final clause-by-clause reread by this dispatched worker; the maintainer supplies
the independent review after delivery, as specified in the dispatch brief.
Opened the completed module and the original node again and checked:
Q/G notation is uniformly multiplicative, `inl` inserts the correct identity,
I/J are exactly the indicated ideal spans, hK permits the empty ideal, both
scalar actions are built from the stated characters, `Comparison.equiv` is
A-linear, `monomial` has the exact v(g) multiplier, `inverse` is specified on
all inclusion-image pure tensors, and multiplication is the constructed
canonical evaluation map. Checked that coefficient naturality quantifies over
all compatible φ and chosen new characters, gives a comparison with the same
properties over A', and includes forward, inverse, and both multiplication
squares. The use of swapped tensor factors is exposed by `pure` and preserves
every formula through tensor symmetry. No hypothesis or conclusion mismatch
was found; no statement correction was needed. The only compile repair was
the API spelling recorded above.
