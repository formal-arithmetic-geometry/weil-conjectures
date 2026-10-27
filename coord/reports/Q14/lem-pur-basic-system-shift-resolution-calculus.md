## Worker report

Stated `WeilConjectures.IntegralSystemRealization.basicSystemShiftResolutionCalculus`
in `Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus`. The conclusion is the
Prop-valued record `BasicSystemShiftResolutionCalculus`; all its fields concern
already prescribed functors, shifts, resolution units and tensor-model maps.
The only postponed proof is this named theorem, with the six-step DAG proof in
its docstring. The local helper definitions contain actual constructions or
explicit predicates, with no postponed data. The item node changes only in `lean`.
There are no new nodes, dependency repairs or statement corrections.

Sources read: the item and all four statement dependency nodes, their recorded
source modules and declaration docstrings/signatures; the current blueprint
`literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-compatibility/`
`fix-prop-coherence.proof.md` (maps-used sentence); the exact-functor shift,
K-injective shift and adjunction-shift APIs. The older snapshot in the item's
source field was not used as the current blueprint.

### Hypotheses and objects

* `D : FiniteFieldDatum` retains the prime p, positive exponent, finite field of
  cardinality q and its specified algebraic closure k. `_hl : l ≠ D.p` is the
  required characteristic inequality; `[Fact l.Prime]` makes l prime.
* `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]` and
  `[FiniteDimensional ℚ_[l] E]` express a finite extension of Q_l. All occurrences
  use the dependency's valuation ring, chosen uniformizer and quotient rings;
  these are not newly parameterized or defined. Existing tower indices n : ℕ
  mean the positive quotient R/t^(n+1), including R/t as index zero.
* `W : Over (Spec (.of D.k))`, `[LocallyOfFiniteType W.hom]` and
  `[QuasiCompact W.hom]` mean a finite-type k-scheme. The same conditions are
  imposed on both endpoints of the scheme arrows. These are k-arrows in `Over`.
* In `pull_models`, `[IsSeparated v.left]`, `[LocallyOfFiniteType v.left]` and
  `[QuasiCompact v.left]` give exactly separated finite type. `push_models` and
  `push_mate` use `[IsProper p.left]`. `open_models` uses
  `[IsOpenImmersion j.left]` and `[QuasiCompact j.left]`.
* `o : Operations l E` is the existing simultaneous system operation data, supplied
  by the statement dependency realization theorem. It retains the universal
  right-derived image and its actual adjunction, and the exact ordinary open
  extension. No extra shift/coherence hypothesis is assumed on o. The theorem
  works for any presentation of these prescribed operations.
* `System l E W` is the ordinary unbounded derived category of modules on the
  whole ringed sequence site. Its ordinary modules are
  `coefficientSequenceModules`, with quotient-semilinear transitions encoded as
  the horizontal restrictions of one sheaf. This is not a diagram in derived
  categories. `Integral l E W`, `calculus`, and the prescribed tensor models and
  shift maps are reused without restriction to normalized or bounded inputs.
  The coefficient universe u+1 retains the small site's object universe u+1 and
  morphism universe u; no equality between those universes is imposed.

### Every conclusion clause

* Naturality and invertibility: the prescribed `systemPullShift`,
  `systemPushShift`, `systemOpenShift` are `Functor.CommShift ℤ` structures,
  whose comparisons are natural isomorphisms. The two tensor slots in
  `tensorShifts` are natural isomorphisms on the entire product category.
  `basicSystemTensorShift` is their actual right-then-left composite. Its
  definition inserts the canonical shift-addition isomorphism, not an endpoint
  isomorphism chosen by existence.
* Zero/addition coherence: already part of the three unary `CommShift` records.
  `system_tensor_laws` identifies each prescribed tensor-slot comparison with
  an actual `CommShift` structure on the appropriate partial functor.
  `integral_tensor_laws` does the same for completed tensor. Both identities are
  equalities of isomorphisms for every M, N and integer r.
* Exact inverse image and open extension: `pull_models` and `open_models` use
  `BasicExactShiftModels`. Its first clause is literal identity in each reindexed
  cochain degree. Its second clause identifies the prescribed derived shift
  through `mapDerivedCategoryFactors`, input/output `Q.commShiftIso`, and the
  ordinary cochain shift. Signed differentials are those of Mathlib's cochain
  shift, C[r]^i = C^(i+r), with r.negOnePow multiplying d.
* Proper image on every K-injective resolution: `push_models` uses
  `BasicSystemImageShiftModels`. For every simultaneous quasi-isomorphism
  a : M → I into a K-injective I it asserts shifted K-injectivity, the shifted
  quasi-isomorphism, and the full derived computation square. The computation
  `basicSystemImageResolutionIso` is S_p(Qa) followed by the inverse of the
  actual universal derived-unit component at I, using its existing `computes`
  certificate. The ordinary map in the square is precisely the termwise
  direct-image cochain shift; its every degree is identity by
  `mapHomologicalComplex_commShiftIso_hom_app_f`.
* Actual adjunction mate: `push_mate` is `BasicSystemImageMate`, namely
  `(o.direct p).adj.CommShift ℤ` with precisely `systemPullShift` and
  `systemPushShift`. This covers both the unit and counit of the recorded
  adjunction, not a separately selected adjunction.
* Independence of representatives: the proper square quantifies over every
  quasi-isomorphism a and K-injective I, and uses the canonical derived unit.
  The tensor square `tensor_models` quantifies over every K-flat P,Q (in
  particular every flat-term K-flat pair) and relates the fixed derived tensor
  map to the actual recorded `systemTensorModel.iso` on both sides.
  The completed properties likewise quantify over every good pair. Thus these
  are fixed derived natural maps with specified computations on all models.
* Two-slot sign: `BasicSystemTensorFormula` applies to every total generator on
  every object U of `(ℕ × W.ProEt)ᵒᵖ`. It sends shifted bidegree (i,j) to the
  generator of degrees (i+a,j+b), with scalar `(b*i).negOnePow`, after the
  explicit output reindexing. `BasicSystemTensorModels` requires an actual
  chain isomorphism α with this formula and the full derived-model square.
  Therefore both total-differential compatibility and every quotient-transition
  compatibility are included as morphism conditions of α, not just levelwise
  formulas. No argument assumes derived evaluation detects arrow equality.
* First slot coefficient 1 and second slot coefficient (-1)^(ri): `system_left`
  and `system_right` are exactly the existing normalized predicates applied to
  `(tensorShifts l E).systemLeft` and `.systemRight`, respectively. They include
  the chain generator formulas and their comparison with the fixed derived map.
* Actual associator: `tensor_associativity` spells the three-input square with
  `(calculus l E W).systemClosed.monoidal.associator`. The sum of shifts is
  transported by the displayed `add_assoc` equality. No new associator is used.
* Koszul symmetry: `tensor_symmetry` retains a natural symmetry isomorphism,
  characterized by `BasicSystemTensorSymmetryModel` on every K-flat pair using
  the actual tensor-model comparisons and sign `(i*j).negOnePow`. This pins the
  canonical Koszul symmetry by its representative formula. Its second clause
  is the simultaneous-shift symmetry square with scalar `(a*b).negOnePow` and
  the canonical identification of a+b with b+a.
* Completed integral tensor: `integral_left` uses exactly
  `integralTensorLeftProperty` for the prescribed completed left comparison.
  `integral_right` uses exactly `integralCompletedTensorRightShiftProperty`
  from the required right-shift node. These predicates include every finite
  quotient generator formula, a natural tower isomorphism, the product shift
  identification, the two cone-summand equations (coefficients 1 and
  r.negOnePow), the final [-1] and commuting-shift isomorphism, and their
  equality to the derived comparison through `integralCompletedTensorComparison`.

### Dependency declarations used

* `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `WeilConjectures.coefficientDerivedSystemEvaluationCalculus`,
  `CoefficientDerivedSystemCalculus`, and the system tensor-model comparison.
  The chosen `calculus` in the operation dependency is that theorem's calculus.
* `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`:
  `WeilConjectures.IntegralSystemRealization.integralCompactificationSystemRealization`,
  `Operations`, `Direct.model`, `Direct.adj`, `Open.ordinary`, `System`, `Integral`,
  `pull` and `calculus` from its public imports. Its theorem supplies the
  operations and realization setting; no realization bounds are added to the
  ambient shift assertion.
* `Sheaf.SixFunctors.IntegralOperationShiftData`:
  `TensorShifts`, `tensorShifts`, `systemPullShift`, `systemPushShift`,
  `systemOpenShift`, `systemTotalTensor`, `systemKFlat`,
  `systemTensorLeftProperty`, `systemTensorRightProperty`,
  `integralTensorLeftProperty`, and `tensorShiftFirst`, all in
  `WeilConjectures.IntegralSystemRealization`.
* `Sheaf.SixFunctors.CompletedTensorShiftRight`:
  `WeilConjectures.completedTensorShiftSecond`,
  `integralCompletedTensorRightShiftProperty`,
  `completedTensorShiftConeFormula`, `completedTensorShiftRoosIso`, and
  `integralCompletedTensorShiftRight` (the last is the existence statement used
  by the proof plan; the conclusion directly names its normalization predicate).
* All fourteen stated proof dependencies are imported, with plain imports for
  proof-only modules. The Mathlib leaves use ExactFunctor, KInjective and
  Localization.Predicate. The proof docstring names the six DAG steps and the
  precise role of each dependency. No proof import closes a cycle in the
  compiler's successful module import graph.

### Edge cases checked

The shifts range over all ℤ, including negative integers and zero, and the
cochain complexes are unbounded. At a=b=0 the generator scalar is 1. If b=0
it is always 1; if a=0 it is (-1)^(bi), with odd i and b giving -1. Taking
a=b=1 in the symmetry square gives the required extra -1; associativity
compares bi+c(i+j) with cj+(b+c)i. The cone map is identity at r=0; its second
summand coefficients multiply to (-1)^(r+s), including negative shifts.
The zero complex and zero tensor factors are allowed throughout, as are empty
schemes, the empty open immersion and identity maps. No nonempty, bounded,
constructible, normalized, flat-quotient or evaluated-K-injective hypothesis
has been inserted. l=2 is permitted when the characteristic is different; the
signs use the integral scalar action, so they also specialize correctly when
-1=1 in a finite coefficient ring. Positive quotient indexing starts at R/t;
there is no spurious A_0 restriction or flatness claim on the quotient maps.

### Searches actually run

* `msearch.py ... leanfinder` with query
  `Exact inverse image proper direct image open extension and derived tensor shifts normalized on simultaneous coefficient system resolutions`:
  eight hits (Tor, Tor', exact-functor Ext and resolution facts), no statement
  of the combined prescribed system/complete tensor normalization.
* `msearch.py ... loogle` with query
  `CategoryTheory.Functor.CommShift, CochainComplex.mapBifunctorShift₂Iso`:
  zero hits for that combined query. The relevant individual declarations were
  nevertheless read directly in Mathlib's source.
* `msearch.py ... grep` with query
  `mapCochainComplexShiftIso|KInjective.*shift|shift.*KInjective`:
  seven hits in Mathlib's homotopy/derived KInjective and Shift modules; these
  provide the reusable infrastructure, not the item's combined statement.
* `msearch.py ... leansearch` with query
  `Derived inverse image direct image extension by zero and tensor commute with signed integer shifts on strict coefficient systems`:
  eight hits, including exact-derived `CommShift`, its factorization compatibility,
  and ordinary cochain `commShiftMapCochainComplex`; no combined system theorem.
* `rg` in `lean/WeilConjectures`, `lean/Sheaf`, Mathlib and
  `dag/lean_names_upstream.json` for the proposed full/short declaration names:
  no existing declarations. Broader searches for `resolution.*[Ss]hift`,
  `basic.system.shift`, `systemPullShift|systemPushShift|systemOpenShift`
  located the prescribed data and related operation/coefficient comparison
  lemmas, which do not state this whole result. The item-id grep in upstream
  `lean/WeilConjectures` found no module.

### Validation

Compiled through the required `scompile.py`, in module mode, including all
proof imports. Initial elaboration fixes were the explicit arity of `asIso`,
the `Functor` namespace for whiskering, and the project's finite-type encoding
`LocallyOfFiniteType` plus `QuasiCompact`; no mathematical statement changed.
The next compile succeeded and identified seven long lines, which were wrapped.
No auto-bound implicits or theorem proofs other than the expected `sorry` remain.
Final standalone compilation passed cleanly in both sandbox and library module
paths (11.7 s and 13.2 s). The prescribed delivery dry run returned OK:
commit 14f296e7573 passed server preflight and per-file compilation. Final
delivery uses the same Lean module and node record.

## Second reading by Q14

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
