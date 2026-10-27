## Worker report

The module `Sheaf.RingTheory.CompletedMonomialIdealTensor` states
`AddMonoidAlgebra.completed_monomial_ideal_tensor`, with its proof `sorry`.
The item statement and all dependency lists are unchanged. There is no statement
correction or disputed assertion. The two real-data helpers provide the specified monomial element and the
base-changed subtype inclusion followed by scalar cancellation. They use
Mathlib `Ideal.span` directly and are recorded in `lean.declarations`.
No new independent notion, new DAG node, or dependency repair is required.

Hypotheses and objects, clause by clause:

- The Noetherian commutative coefficient ring is `(L : Type v) [CommRing L]
  [IsNoetherianRing L]`. In particular no field, domain, local, nontriviality,
  characteristic, or flatness-over-integers assumption is imposed.
- The finitely generated additive commutative monoid is `(P : Type u)
  [AddCommMonoid P] [AddMonoid.FG P]`. There is no cancellation, saturation,
  torsion-freeness, sharpness, or integrality assumption.
- The number of variables is `(n : ℕ)` and the variables are indexed by `Fin n`.
  This includes zero variables; the zero-based indexing simply renames t₁,...,tₙ.
- For any coefficient ring D, D[P] is Mathlib `AddMonoidAlgebra D P`, whose
  finite-support coefficients and convolution multiplication are precisely the
  direct-sum construction in the node. R is `AddMonoidAlgebra ℤ P`.
- S is `MvPolynomial (Fin n) (AddMonoidAlgebra L P)`. The unrestricted ideal
  is `(a : Ideal S)`; B is the actual `AdicCompletion a S`, never an abstract
  ring with an unspecified map, nor a completion at a special monomial ideal.
- The structure R → L[P] is the existing Mathlib coefficient extension, enabled
  by `open scoped AlgebraMonoidAlgebra`. The standard polynomial and completion
  algebra instances compose it with L[P] → S → B. Thus z^q maps to the same
  monomial in B. A separate server probe checks equality of these actual
  integer and L-coefficient monomial images, without extra hypotheses.
- The monoid ideal is `(I : Set P)` with
  `hI : ∀ q ∈ I, ∀ r : P, q + r ∈ I`. It need not be nonempty or proper.
- `Ideal.span (AddMonoidAlgebra.of' D P '' I)` is used directly throughout.
  This is exactly D[I], not a different ideal: Mathlib's
  `AddMonoidAlgebra.mem_ideal_span_of'_image` says each supported exponent is
  r+q with q ∈ I. Under hI and commutativity this is equivalent to support in I;
  conversely any q ∈ I has q=0+q. This argument works in the zero ring too.
  `monomialSpanGenerator D I q` is the actual subtype element z^q, with its
  membership supplied directly by `Ideal.subset_span`.

Conclusions, clause by clause:

- The first conjunct gives `∃ e : B ⊗[R] (Ideal.span (AddMonoidAlgebra.of' ℤ P '' I)) ≃ₗ[B]
  B ⊗[L[P]] (Ideal.span (AddMonoidAlgebra.of' L P '' I))`. Tensor symmetry is used uniformly to put B
  first. These are the node's two module tensors with their factors swapped,
  not algebra tensor products. The canonical swaps identify their standard
  B-module structures with the source's action on the last factor. Equivalently,
  transport the displayed e across the swaps to recover precisely
  Z[I] ⊗_R B ≃ₗ[B] L[I] ⊗_{L[P]} B.
- The `∀ (q : I) (b : B)` clause specifies
  `e (b ⊗ₜ monomialSpanGenerator ℤ I q) =
  b ⊗ₜ monomialSpanGenerator L I q`. Under those same swaps it is the exact
  formula z^q ⊗ b ↦ z^q ⊗ b. The `LinearEquiv` provides B-linearity and
  invertibility, not merely an equivalence of underlying sets or an
  uncharacterized isomorphism.
- `monomialTensorMul D I B` is the constructed B-linear composite of
  `(Ideal.span (AddMonoidAlgebra.of' D P '' I)).subtype.baseChange B` with
  `TensorProduct.AlgebraTensorModule.rid (AddMonoidAlgebra D P) B B`.
  It sends b ⊗ x to b * image(x), by the actual definitions. A separate server
  probe checks this formula. In particular on basis elements it is the node's
  multiplication z^q ⊗ b ↦ z^q b (commutativity switches the written factors).
- Compatibility with multiplication is the equality of B-linear maps
  `(monomialTensorMul L I _).comp e.toLinearMap = monomialTensorMul ℤ I _`.
  It is an equality of the actual composites on all tensors.
- Injectivity is `Function.Injective (monomialTensorMul ℤ I B)`.
- The final equality identifies `Set.range (monomialTensorMul ℤ I B)` with
  the underlying set of `Ideal.span ((fun q ↦ algebraMap L[P] B (of' L P q)) '' I)`.
  Thus the image is exactly the specified ideal IB, not merely contained in it.

Dependency declarations read and used:

- The reused monomial ideal construction is Mathlib `Ideal.span`, module
  `Mathlib.RingTheory.Ideal.Span`, publicly imported by
  `Mathlib.Algebra.MonoidAlgebra.Ideal`. No specialized ideal wrapper is declared.

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`, module
  `Mathlib.RingTheory.Noetherian.Defs` (all ideals finitely generated).
- `def-weil-pbc-adic-completion`: `AdicCompletion`, module
  `Mathlib.RingTheory.AdicCompletion.Basic`, with its actual commutative-ring
  and induced algebra instances in `Mathlib.RingTheory.AdicCompletion.Algebra`.
  The latter publicly imports the recorded Basic module.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` and `TensorProduct.mk`,
  module `Mathlib.LinearAlgebra.TensorProduct.Defs`, exposed through
  `Mathlib.LinearAlgebra.TensorProduct.Tower`, which also supplies
  `LinearMap.baseChange` and `TensorProduct.AlgebraTensorModule.rid`.
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial`, module
  `Mathlib.Algebra.MvPolynomial.Basic`.
- Proof-only imports are `Mathlib.RingTheory.FiniteType`
  (`Algebra.FiniteType.isNoetherianRing`),
  `Mathlib.RingTheory.AdicCompletion.AsTensorProduct`
  (`AdicCompletion.flat_of_isNoetherian`), and
  `Mathlib.RingTheory.Flat.Basic`
  (`Module.Flat.lTensor_preserves_injective_linearMap`).
  `lem-trf-scalar-tensor-cancel-base-change` is
  `TensorProduct.AlgebraTensorModule.cancelBaseChange`, already exposed by
  the statement import `Mathlib.LinearAlgebra.TensorProduct.Tower`.
  These four proof leaves have `mathlib_match` records, which were read;
  their lack of a `lean` field is not a missing declaration.

The declaration docstring carries all six DAG proof steps: the ideals T_d;
the explicit coefficient inverse and balancing; finite type, Noetherianity and
flat completion; flat preservation of the inclusion with scalar cancellation;
the coefficient comparison with its inverse and multiplication square; and the
two image inclusions, including the empty ideal. Source read locally: ILO PDF
pages 76 and 116 (printed pages 70 and 110), specifically VI 1.6(i)--(ii) and
VIII 3.4.3, as well as the recorded Mathlib definitions and full signatures.
The node is explicitly an agent-extracted algebra lemma, rather than a claim
that ILO states this generality verbatim.

Edge cases checked before writing and on rereading:

- I=∅ gives zero monomial ideals, zero tensor sources and the zero image ideal.
- I=P contains the identity monomial, so both ideals are the entire rings and
  the multiplication map is the usual scalar-cancellation isomorphism.
- n=0 keeps all constructions and uses the ordinary no-variable polynomial ring.
- P={0} gives only the empty and whole monoid ideals.
- Noncancellative P={0,e}, e+e=e, is allowed. The monomial ideal with exponent e
  remains the coefficient summand on e; the balancing computation needs no
  cancellation. It is not silently replaced by a cancellative or fs monoid.
- L=ℤ/4 is allowed: the proof uses coefficient bases and flat completion over S,
  not flatness over ℤ. L the zero ring is also allowed.
- a=⊥ gives the original polynomial ring; a=⊤ gives the zero completion.
  Both are covered, with no Jacobson-radical, properness, or injectivity-of-S→B
  hypothesis. In the zero completion the asserted injection has zero source.
- Independent universes u and v for P and L remain independent; the completion
  and tensor products naturally live in their maxima. No size case is discarded.

Searches for an existing statement (all wrapper outputs are retained in
`sandbox/searches.jsonl`):

- `msearch.py ... leanfinder "The multiplication map from a monoid ideal tensor
  a completed monoid polynomial algebra is injective, with image the monomial
  ideal"`: 8 hits, including completion tensor-injectivity and the algebra-epi
  multiplication lemma. None states the coefficient comparison and injection
  over ℤ[P] with the prescribed image.
- `msearch.py ... loogle "AddMonoidAlgebra, TensorProduct"`: 12 hits, notably
  `AddMonoidAlgebra.scalarTensorEquiv`, `tensorEquiv`, and their pure-tensor
  formulas. These concern whole monoid algebras and do not state this ideal
  tensor theorem.
- `msearch.py ... grep "monomialIdeal|monoidIdeal|supported"
  Algebra/MonoidAlgebra`: 11 hits. `AddMonoidAlgebra.supported` is a coefficient
  submodule; it does not give this completed tensor comparison. The separate
  read of `Mathlib.Algebra.MonoidAlgebra.Ideal` supplies the existing ideal-span
  support characterization used above.
- `msearch.py ... leansearch "Injectivity of monomial ideal tensor product into
  an ideal adic completion of a monoid algebra"`: 8 hits, mostly adic exactness
  and tensor-completion comparisons; again no exact statement.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and the Mathlib source for
  `monomialIdeal|monoidIdeal|MonomialIdeal|monoid ideal|monomial ideal`, and
  `rg` for this item's ID upstream: no exact existing theorem. Nearby
  `MonoidAlgebra.toricIdeal` assumes a field and uses multiplicative monoids;
  `ToricMonoid.completedMonomialIdeal` requires local coefficient rings and a
  specified toric completion. Neither is used as an unrelated replacement for
  this arbitrary completion and arbitrary Noetherian coefficient ring.
  `LogChartFaceTor.ideal` is integer-only and multiplicative; it does not give
  the coefficient-family notion here. The monomial ideal is directly Mathlib's
  `Ideal.span` with `of'` generators and introduces no wrapper, algebra or tensor.
- The original name search missed the concurrently indexed
  `AddMonoidAlgebra.monomialSpan` declaration reported by the maintainer.
  The repair removes that declaration altogether and uses `Ideal.span` directly.

Validation: the delivered file passed `scompile.py` in both sandbox mode and
library module mode, within the default 60-second limit, with no errors or
unexpected warnings. Every universe is declared and `autoImplicit` is false.
The only postponed proof is the item's named theorem. The additional formula
probe is outside the delivered modules and will not be shipped.

## Second reading by NH

The delivering worker separately reread the unchanged node against the complete
module after the first clean compile. The maintainer performs the independent
review required by the assignment; no second agent was started or claimed here.
The two potentially nonliteral presentations were checked explicitly: the
monomial span equals the supported direct sum under hI by Mathlib's support
criterion, and the coefficient-first tensors are the canonical symmetric
presentations of the displayed tensors with the same B-action. The rereading
also checked that the comparison has its monomial formula, that multiplication
is a constructed map, that its square is equality of maps, and that its range
is equality with the generated ideal. All four hypotheses (L, P, n, a) and the
monoid-ideal stability hypothesis match; no additional hypothesis or omitted
conclusion was found. No statement correction was made.

## Returned delivery repair

The return on immutable head `b0ead7735cce` identified the duplicate
`AddMonoidAlgebra.monomialSpan` in
`Sheaf.RingTheory.MonomialQuotientResidueSurjection`. The current local checkout
and the current server source contain neither that module nor a Lean binding
for `lem-trf-monomial-quotient-residue-surjection`; the prescribed
`scompile.py --source Sheaf.RingTheory.MonomialQuotientResidueSurjection`
returns `Module source unavailable`. Reading the corresponding server node
confirms its `lean` is null. Therefore importing that module would not reuse
a published declaration.

The repair deletes our `monomialSpan` definition, without renaming or replacing
it with another wrapper. Every use now directly reuses the existing Mathlib
`Ideal.span` declaration already imported from the public ideal API, on exactly
the same `AddMonoidAlgebra.of' D P '' I` generators. The generator and
multiplication helpers, and every tensor in the theorem, use this single
Mathlib notion. Its type is definitionally the former wrapper's expansion,
so no hypothesis, conclusion, coefficient map, universe or edge case changes.
The removed name is also removed from `lean.declarations`, and the literal
theorem signature is updated in `lean.statement`. This repairs the source-index
collision even if the other module later lands, without duplicating or
renaming its specialized declaration.

Self-check: reread the repaired theorem against the unchanged DAG statement
and the return entry. Both real-data helpers still use the actual monomial
ideal and subtype map, with precisely the original formulas. No other node
is changed. The authorized delivery wrapper rebases this packet on current main.
