## Worker report

The module `Sheaf.TraceFormula.DominationPushoutUniversalInjective` states
`LinearMap.domination_iff_pushout_universally_injective` for maps `a : P →ₗ[R] Q`
and `b : P →ₗ[R] Q'` over a commutative ring.  The left-hand quantifier ranges
over every module `L : Type v` and renders domination as
`LinearMap.ker (a.rTensor L) ≤ LinearMap.ker (b.rTensor L)`.  The right-hand
side uses the canonical pushout leg
`(pushout.inr (ModuleCat.ofHom a) (ModuleCat.ofHom b)).hom : Q' →ₗ[R]
pushout (ModuleCat.ofHom a) (ModuleCat.ofHom b)` and requires
`Function.Injective (LinearMap.lTensor L ...)` for every such `L`.  The proof is
`sorry`, as required at stage 2.

The ring hypothesis is `[CommRing R]`; `P`, `Q`, and `Q'` are additive commutative
groups with `R`-module structures; `a` and `b` have the common domain `P`.  The
pushout is Mathlib's `ModuleCat` pushout, whose existence is supplied by
`ModuleCat.HasColimit.instHasColimit`.  Tensor products and tensor maps are
Mathlib's `LinearMap.rTensor` and `LinearMap.lTensor`.  The finite-test dependency
is imported as `Sheaf.RingTheory.UniversalInjectiveFiniteTest`, declaration
`LinearMap.universally_injective_tensor_iff`; the other statement dependencies are
Mathlib leaves (`CategoryTheory.Limits.colimit` and `TensorProduct`).

Edge cases checked: `P`, `Q`, `Q'`, or `L` may be zero modules; the quantifier on
`L` includes the zero module and arbitrary modules in its universe; no injectivity
of `a` or `b`, flatness, finite generation, or nonemptiness assumption is added.
The categorical pushout is available for arbitrary module maps, including zero maps.

Searches for an existing declaration: `msearch.py ... leanfinder "domination of
module maps pushout universally injective"` and `... loogle "ModuleCat pushout
LinearMap lTensor rTensor"` found no matching theorem; `rg` over
`WeilConjectures/` and `lean/Sheaf/` found no declaration of this equivalence.
Mathlib searches for pushout/universal-injectivity and tensor-kernel domination found
only general pushout, tensor, and flatness results, with no exact statement.

No `STATEMENT-DISPUTED` issue or node correction was found.

## Second reading by Q132

The node and module were read together.  The common ring and module hypotheses,
the two maps with common domain, the tensor-kernel inclusion, and the universal
injectivity condition on the canonical pushout leg each appear exactly once.  The
module uses the categorical pushout specified by the node and keeps the tensor
orientation explicit (`rTensor` for domination and `lTensor` for the universal
injectivity test).  No hypothesis or conclusion clause is added or omitted.
