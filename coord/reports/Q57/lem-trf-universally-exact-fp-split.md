## Worker report

The module `Sheaf.SecTraceFormula.UniversallyExactFpSplit` states
`LinearMap.universallyExactFpSplit`; its proof is `sorry`. It formalizes the
universally exact short exact sequence with finitely presented quotient from
Stacks Project Tags 058K and 058L. No definition or helper is introduced.

The declaration uses the following binders and clauses.

- `R : Type uR` with `[CommRing R]` is the commutative base ring.
- `A`, `B`, and `C` are the three explicitly bound module types, each with
  `[AddCommGroup]` and `[Module R]`; no finite generation or flatness instance is
  assumed for any of them.
- `i : A →ₗ[R] B` and `p : B →ₗ[R] C` are the stated linear maps.
- `hi : Function.Injective i` is injectivity of the first map.
- `hp : Function.Surjective p` is surjectivity of the second map.
- `hex : Function.Exact i p` says the image of `i` is the kernel of `p`,
  including the required zero composite, so it renders `ker p = i(A)`.
- `[Module.FinitePresentation R C]` is the recorded Mathlib declaration for
  the node `def-sc-finitely-presented-module`.
- `hTensor` quantifies over every module `Q : Type (max uR uA uB uC t)` with
  its additive-group and R-module structures. For each such Q, the three
  conjuncts are respectively `Function.Injective (i.rTensor Q)`,
  `Function.Surjective (p.rTensor Q)`, and
  `Function.Exact (i.rTensor Q) (p.rTensor Q)`. `rTensor` has domain
  `A ⊗[R] Q` (respectively `B ⊗[R] Q` and `C ⊗[R] Q`) and is the Mathlib map
  specified by `def-weil-pbc-module-tensor-product`.
- The conclusion `∃ r : B →ₗ[R] A, r.comp i = LinearMap.id` is the required
  R-linear retraction, with identity on A.

The dependency declarations used are `Module.FinitePresentation` from
`Mathlib.Algebra.Module.FinitePresentation` and `TensorProduct` together with
`LinearMap.rTensor` from `Mathlib.LinearAlgebra.TensorProduct.Map`, the exact
Mathlib matches recorded by the two statement dependencies. The module imports
`Mathlib.Algebra.Exact.Basic` for `Function.Exact` and the tensor-product map
module for `rTensor`.

Edge cases checked before writing include the zero ring and zero modules, the
zero map (where the injectivity and exactness hypotheses force the corresponding
terms to be zero), identity and already split sequences, finitely presented
quotients with zero generators or zero relations, and arbitrary Q including
zero and non-finitely-presented modules. The universe parameter `t` is retained
above the universes of R, A, B, and C, so the tensor test does not impose a
size equality or a finiteness restriction.

Searches for an existing declaration were made with the prescribed tools:

- `msearch.py ... leanfinder "universally exact sequence finitely presented
  quotient splits retraction"`: eight results, including
  `Module.finitePresentation_of_split_exact` and split exactness lemmas, but no
  theorem asserting pure/universal exactness with finitely presented quotient.
- `msearch.py ... loogle "LinearMap.lTensor, Function.Exact,
  Module.FinitePresentation"`: no hits.
- `msearch.py ... grep "universally.exact|finitely.presented.*split|
  Function.Exact.*lTensor" Algebra RingTheory LinearAlgebra`: no hits.
- Direct `rg` over `lean/Sheaf`, `WeilConjectures/`, and `dag/nodes`, including
  the item id and the proposed declaration name, found no existing project or
  upstream declaration. The Mathlib `finitePresentation_of_split_exact`
  theorem assumes a splitting and therefore is not the node's statement.

No statement fault or `STATEMENT-DISPUTED:` condition was found.

## Second reading by Q57

I reopened the node and the completed module. The commutative-ring, three
module, two map, injectivity, surjectivity, kernel-image exactness, finite
presentation, and universal tensor hypotheses all occur once and in the same
roles as the node. The tensor maps are `rTensor`, matching the node's
`A ⊗_R Q` orientation, and all three exactness clauses are present for every
Q. The retraction conclusion is exactly `r ∘ i = id_A`. No hypothesis or edge
case was added or omitted, and the declaration compiles cleanly with only the
expected postponed proof.
