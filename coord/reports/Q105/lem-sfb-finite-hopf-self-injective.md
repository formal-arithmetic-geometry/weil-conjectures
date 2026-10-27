## Worker report

The module `Sheaf.RingTheory.HopfAlgebra.FiniteSelfInjective` states
`HopfAlgebra.finiteDimensional_exists_extension`, with one `sorry` and no definitions.
It states the extension property directly, including arbitrary modules in independent
universes; it does not restrict to finite modules or to the universe of the algebra.

Source read: [Bichon, arXiv:2301.05480v2](https://arxiv.org/html/2301.05480v2),
section 3, first paragraph. This explicitly asserts self-injectivity of finite-dimensional
Hopf algebras. The node specializes to commutative algebras and spells out its usual
injective-module extension meaning. No source correction is needed. The named local PDF
is not required for this delivery: the cited online version was opened and read.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The field `k` is `(k : Type u) [Field k]`.
- The unital commutative algebra `H` is `(H : Type v) [CommRing H] [HopfAlgebra k H]`.
  `HopfAlgebra` extends `HopfAlgebraStruct`, hence `Bialgebra`, hence `Algebra k H`.
- Comultiplication and counit as algebra maps are `Bialgebra.comulAlgHom k H`
  and `Bialgebra.counitAlgHom k H`. Their definitions use the coalgebra maps and the
  bialgebra unit/multiplicativity axioms. Tensor multiplication is Mathlib's existing
  `Algebra.TensorProduct` multiplication, not another construction.
- The node's coassociativity and two counit identities are precisely
  `Coalgebra.coassoc`, `Coalgebra.rTensor_counit_comp_comul`, and
  `Coalgebra.lTensor_counit_comp_comul`, with the displayed tensor identifications.
- The antipode is `HopfAlgebra.antipode k`. Its two identities are the fields
  `HopfAlgebra.mul_antipode_rTensor_comul` and
  `HopfAlgebra.mul_antipode_lTensor_comul`. Although its structure field is initially
  linear, on a commutative algebra it is the algebra map
  `HopfAlgebra.antipodeAlgHom k H`, whose underlying linear map is the same antipode.
  Conversely `HopfAlgebra.ofAlgHom` constructs exactly this structure from the
  node's algebra-map formulation. Thus no hypothesis on the antipode was lost.
- A finite vector-space basis is `(ι : Type w) [Finite ι]
  (basis : Module.Basis ι k H)`. `Module.Basis` is a linear equivalence with finitely
  supported coordinate families, giving exactly unique finite expansions. A supplied
  finite basis is equivalent to admitting one, since the conclusion is independent
  of its choice. `Module.Free.of_basis` also yields the recorded dependency's
  `Module.Free k H`; that class itself does not express finiteness, so it would be
  insufficient as the sole hypothesis here.
- Arbitrary modules are `(U : Type x) (V : Type y) [AddCommGroup U] [Module H U]
  [AddCommGroup V] [Module H V]`, with independent, explicitly declared universes.
  No field action on these modules is added; restriction along the algebra map
  supplies it when proving the assertion.
- The injection is `(j : U →ₗ[H] V) (hj : Function.Injective j)`.
- The given map is `(f : U →ₗ[H] H)`, with the regular `H`-module as codomain.
- The extension and its equation are `∃ g : V →ₗ[H] H, g.comp j = f`.
  Equality of these linear maps means exactly `g (j u) = f u` for every `u`.
- The final absence of finite-generation assumptions is literal: neither `U` nor
  `V` has any `Module.Finite`, `FiniteDimensional`, finite-basis or cardinal bound.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`, publicly imported.
- `lem-weil-pbc-algebra-tensor-pushout-universal-property`: its `mathlib_match`
  names `Algebra.TensorProduct.instCommRing`, `tmul_mul_tmul`, `includeLeft`,
  `includeRight`, `ext` in `Mathlib.RingTheory.TensorProduct.Basic`, and `productMap`,
  `productMap_apply_tmul`, `productMap_left`, `productMap_right` in
  `Mathlib.RingTheory.TensorProduct.Maps`. These source signatures and docstrings
  were read; the Hopf algebra imports use exactly this tensor-product algebra.
- `def-weil-pbc-free-module`: `Module.Free` in
  `Mathlib.LinearAlgebra.FreeModule.Basic`, publicly imported. The statement uses
  its basis notion `Module.Basis` directly, retaining the finite index hypothesis.
- The Hopf structure uses `Mathlib.RingTheory.HopfAlgebra.Convolution`, including
  the algebra-map antipode identified above, and its public Basic/Bialgebra/Coalgebra
  imports. The classes and their full field signatures were read.
- Proof dependency `lem-weil-pbc-vector-space-basis-through-vector` has the Mathlib
  match `Module.Basis.extend`, `coe_extend`, `subset_extend` in
  `Mathlib.LinearAlgebra.Basis.VectorSpace`; that module is imported as a proof
  dependency. Its extension declaration and containment property were read.
- Proof dependency `lem-sfb-finite-hopf-frobenius-form` currently has neither a Lean
  record nor a Mathlib match, so no module exists to import. It is retained in
  `proof_deps` and the complete four-step proof docstring names its role. It is not
  needed to type the present extension statement.

Edge cases checked before writing: all field characteristics are allowed, including
nonsemisimple finite Hopf algebras in positive characteristic; no reducedness,
algebraic closure, characteristic zero or separability is assumed. `U = 0`, `V = 0`
when an injection exists, `j` an isomorphism, and `f = 0` all have the expected
extension interpretation. Infinite modules are allowed. There is no assumption that
the basis index is inhabited: an empty basis for `H` is already incompatible with
its counit algebra map to the nonzero field, rather than excluded by an added binder.
The trivial Hopf algebra `H = k` is covered. The universes of the field, algebra,
basis index, source module and ambient module are all explicit and independent.

Searches made, with results (machine outputs also in sandbox `searches.jsonl`):

- LeanSearch via `msearch.py`, query `Finite dimensional commutative Hopf algebra
  is an injective module over itself`: `Module.Injective.mk`, Hopf structure and
  morphism injectivity facts, and injectivity of finite-group representations.
  None proves self-injectivity of an arbitrary finite commutative Hopf algebra.
- LeanFinder via `msearch.py`, query `A finite dimensional commutative Hopf algebra
  is self injective: maps from any submodule to the algebra extend to the whole
  module`: `CSA.fin_dim`, `CommSemiring.toHopfAlgebra`, `FiniteDimensional.left`,
  `IsSimpleModule.finrank_eq_one_of_isMulCommutative`, `HopfAlgebra`,
  `AlgHom.bijective`, `HopfAlgebra.ofAlgHom`, `FiniteDimensional.isUnit`.
  The structure and constructor are usable notions, but none is the requested theorem.
- Loogle via `msearch.py`, query `HopfAlgebra, Module.Injective`: service unavailable;
  recorded as unavailable, with no negative mathematical verdict.
- Mathlib grep via `msearch.py`, query `selfInjective|[Ii]njective|Frobenius`,
  subdirectory `RingTheory/HopfAlgebra`: six matches in Quotient/Convolution,
  concerning injectivity of convolution encodings, not self-injectivity.
- `rg` of `HopfAlgebra|finite.*[Hh]opf|hopf.*[Ii]njective` over the prescribed
  `lean/WeilConjectures` and `lean/Sheaf` trees found the Hopf infrastructure,
  Cartier/Etale results and the finite-dual Hopf-module statement, not this theorem.
  Targeted `rg` of `finite.*[Ii]nject|self.?[Ii]nject|frobenius` in their Hopf
  directories found no equivalent theorem. `grep -rn` of the exact item id in
  `lean/WeilConjectures` returned no match. The upstream-name index was consulted;
  no declaration for this theorem or for the chosen full name was found.

No new nodes, dependency replacements, statement changes or disputes.

## Second reading by Q105

This is a second pass by the same worker; the dispatcher explicitly prohibits
starting another agent, and the maintainer supplies the independent review.
With the JSON statement and completed module open, I checked the structure fields,
both tensor counit identities and both antipode identities against the explicit
Hopf convention; `antipodeAlgHom` resolves the initially linear field exactly.
I checked that `Finite ι` accompanies a genuine `Module.Basis`, and that the
conclusion quantifies over arbitrary `U : Type x` and `V : Type y` and asks for
equality of the composite with the original map. No finite-module assumption or
equality of universes was introduced. The proof docstring reproduces all four
node proof steps, including restriction of scalars and infinite-basis extension.
No mismatch was found and no change to the node statement was required.

## Validation

Every compiler invocation uses the prescribed `scompile.py` wrapper in module mode.
The only postponed proof is the named item theorem; no data is postponed.
The module passed `scompile.py` with no diagnostics. The prescribed `deliver2.py
Q105 lem-sfb-finite-hopf-self-injective --no-push` passed server preflight and
per-file compilation, reporting `OK (dry run)` on 2026-10-24. A source comparison
also confirms that `lean` is the only changed node field and every Lean line is
at most 100 characters.
