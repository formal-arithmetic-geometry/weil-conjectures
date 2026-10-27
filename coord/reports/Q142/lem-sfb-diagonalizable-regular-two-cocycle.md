## Worker report

The module `Sheaf.AlgebraicGeometry.DiagonalizableRegularTwoCocycle` states
`AlgebraicGeometry.diagonalizable_regular_two_cocycle`, with `sorry` as its sole proof.
It renders the regular cochain formulas directly as tensor expressions; there are no
new definitions, new nodes, dependency repairs, or statement changes.

Hypotheses and clauses, in the order of the node:

- Any commutative ring: `(R : Type u) [CommRing R]`; no nontriviality hypothesis.
- Finitely generated additive abelian character group: `(M : Type v)
  [AddCommGroup M] [AddGroup.FG M]`. The ring and character universes are independent.
- `D_R(M)` and its coordinate algebra: `R[M]` uses Mathlib's existing scoped
  `AddMonoidAlgebra` notation, with the canonical Hopf structure imported by the
  recorded dependency. The scheme is not an additional variable in the mathematical
  statement: it is the spectrum of this exact Hopf algebra, so no unused scheme
  parameter is introduced. Its universal points appear through the coordinate maps.
- The coproduct and counit are `Coalgebra.comul (R := R) (A := R[M])` and
  `Coalgebra.counit (R := R) (A := R[M])`. Their values on basis elements are exactly
  `e_m ⊗ e_m` and `1`, by the canonical group-algebra instances.
- Arbitrary coefficient module: `(E : Type w) [AddCommGroup E] [Module R E]`, with
  a third independent universe. No flatness, finite generation, or projectivity.
- Linear coaction: `τ : E →ₗ[R] E ⊗[R] R[M]`.
- Coassociativity: `hcoassoc` is `assoc ∘ (τ ⊗ 1) ∘ τ = (1 ⊗ Δ) ∘ τ`.
- Counitality: `hcounit` is `rid ∘ (1 ⊗ ε) ∘ τ = LinearMap.id`.
- Regular cochains: degree one is literally `E ⊗[R] R[M]`, degree two is
  `E ⊗[R] R[M] ⊗[R] R[M]`, and degree three is the same with one further factor.
  All products associate left. The general degree notation in the node explains
  the formulas and requires no independent cochain-complex construction.
- Evaluation at an algebra map and multiplication in the test algebra are expressed
  intrinsically by these coordinate tensors. On `x ⊗ a ⊗ f`, evaluating at `(h,k)`
  means `x ⊗ h(a) * k(f)`. Applying the coaction evaluates its new coordinate at `h`;
  the algebra multiplication of points pulls back along `Δ`; omission of a point
  inserts the coordinate `1`. Thus using the universal pair/triple here is an exact
  rendering of the node's stipulated equality in the coordinate tensor modules.
- The cocycle `c` is the binder `c : E ⊗[R] R[M] ⊗[R] R[M]`.
- First term of `hc`: `((τ.rTensor R[M]).rTensor R[M]) c` sends
  `x ⊗ a ⊗ f` to `τ(x) ⊗ a ⊗ f`, hence `h • c(k,l)`.
- Second term of `hc`: tensor the map `assoc.symm ∘ (1_E ⊗ Δ)` with the last
  factor. This gives `x ⊗ Δ(a) ⊗ f`, hence `c(hk,l)`.
- Third term of `hc`: apply `Δ.lTensor (E ⊗[R] R[M])` and flatten with the inverse
  associator. This gives `x ⊗ a ⊗ Δ(f)`, hence `c(h,kl)`.
- Fourth term of `hc`: `(TensorProduct.mk R C² R[M]).flip 1 c` appends `1`, hence
  `c(h,k)`. The signs are first minus second plus third minus fourth, equal to zero.
- The conclusion is `∃ b : E ⊗[R] R[M], c = ...`. Its three terms are respectively
  `τ.rTensor R[M] b`, `assoc.symm (Δ.lTensor E b)`, and
  `(TensorProduct.mk R C¹ R[M]).flip 1 b`, with signs plus, minus, plus. On pure
  tensors these are precisely `h • b(k)`, `b(hk)`, and `b(h)`.
- Torsion is allowed: there is no torsion-free, characteristic, or invertibility
  assumption on `M` or `R`.

Dependencies read and used:

- `def-sfb-ring-diagonalizable-group`: read the full signature and docstring of
  `AlgebraicGeometry.ringDiagonalizableGroup` and `ringDiagonalizableGroupMap` in
  `Sheaf.AlgebraicGeometry.RingDiagonalizableGroup`. The former is the Hopf spectrum
  of `CommHopfAlgCat.of R (AddMonoidAlgebra R M)`. We import that module publicly
  and use its coordinate algebra and canonical Mathlib Hopf operations directly;
  there is no second group-scheme definition.
- `def-weil-pbc-module-tensor-product`: its `mathlib_match` supplies `TensorProduct`
  (Defs.lean), `TensorProduct.lift`, `lift.tmul`, `ext'` (Basic.lean), and
  `LinearMap.rTensor`, `rTensor_tmul`, `rTensorHom` (Map.lean). Read those signatures
  and docstrings. The statement uses that exact tensor product, its `rTensor`,
  `lTensor`, `mk`, `assoc`, and `rid`, supplied by the first public import.
- `Mathlib.GroupTheory.Finiteness` supplies the precise `AddGroup.FG` hypothesis.
  The proof dependencies are exactly the two statement dependencies; their imports
  already suffice for the planned proof. The docstring carries all four DAG steps.

Edge cases checked before writing: `E = 0` makes every equation trivial, allowing
`b = 0`. The zero ring is allowed and forces the module to be zero. For `M = 0`,
all coaction and coordinate unit identifications reduce the cocycle differential
in degree two to zero and the degree-one coboundary to the identity, so `b = c`.
For a trivial coefficient action, the constant cocycle `c = x ⊗ 1 ⊗ 1` has
`b = x ⊗ 1`, confirming signs. For `M = Z/pZ` over characteristic `p`, extracting
the coefficient of `e_0` still satisfies `(1 ⊗ λ)Δ = 1 λ`, with no division by `p`.
The general module need not be flat: the proof only uses linear maps and pure-tensor
generation. No small test-algebra universe is quantified over in the theorem,
so no vacuous functor-of-points condition is possible.

Searches actually run with `msearch.py Q142 lem-sfb-diagonalizable-regular-two-cocycle`:

- leanfinder: `Every regular two cocycle of a split diagonalizable group scheme over
  a commutative ring acting on a module is a regular coboundary`. Eight hits,
  including `groupCohomology.isCoboundary₂_of_mem_coboundaries₂`, `H2π_eq_zero_iff`,
  and Hilbert 90. Their printed types concern abstract group cochains or assume
  membership in coboundaries; none gives a regular cobounding cochain here.
- loogle: `"AddMonoidAlgebra", "cocycle"`. Zero hits.
- leansearch: `Regular Hochschild cohomology of diagonalizable group schemes vanishes
  in degree two`. Eight hits on abstract group cohomology and Lie cochains; no match.
- grep: `([Dd]iagonali[sz]able|[Mm]ultiplicative[Tt]ype).*(cohomolog|cocycle)|[Hh]ochschild`.
  One hit, a TODO for the Hochschild-Serre spectral sequence, not this statement.
- `rg` of the project `WeilConjectures` and `Sheaf` trees for diagonalizable,
  coaction, regular cochain, Hochschild, and the item id: related geometric and
  descent coactions, but no regular two-cocycle vanishing statement. The upstream
  name index has no declaration for this item. No duplicate is introduced.
- Read Mathlib's Coalgebra.Basic, Coalgebra.MonoidAlgebra,
  Bialgebra.MonoidAlgebra, HopfAlgebra.MonoidAlgebra, tensor associator and
  tensor-map sources to verify the exact canonical operations and their types.

Source read online: https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf,
printed pp.283--285, especially the tensor description and differential on p.284
and Remark B.2.4 on p.285. They agree with the node and the displayed tensor maps.
No statement dispute or node fault was found. No source was copied into the project.

## Second reading by Q142

A separate pass over the complete node and final file checked the match explicitly:
`CommRing`, `AddCommGroup` and `AddGroup.FG` retain precisely the ring/character
hypotheses. `E` has only its additive module structure. `hcoassoc` has the associator
in the forward direction, while all cochain terms use inverse associators; this is
necessary because the cochain tensor products associate left. `hcounit` ends in
`LinearMap.id` on `E`. For `hc` the four outputs all lie in the ordered four-factor
module `E ⊗ B ⊗ B ⊗ B`, with signs `+ - + -`; the conclusion has three outputs in
`E ⊗ B ⊗ B`, with signs `+ - +`. The final `mk.flip 1` appends the unit, rather than
inserting it among the earlier coordinates. These checks found no mathematical
mismatch. The theorem name was changed to Mathlib's snake-case convention before
final validation. All universes and binders are explicit and autoImplicit is false.
This is the worker's additional reading; the maintainer performs the independent
review as specified by the dispatch brief. No other agent was started.

Validation: the prescribed scompile wrapper's local attempt reported disk full;
its automatic fallback compiled against current server sources successfully in
2.5 seconds. Final renamed declaration is also validated by the delivery dry run.
