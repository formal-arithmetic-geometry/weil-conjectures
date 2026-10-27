## Worker report

The module `Sheaf.FieldTheory.TensorKernelInseparableInvariants` states the entire
node in two theorems, `Algebra.tensorKernelInseparableInvariants` (the tensor
assertion) and `Algebra.purelyInseparable_compositeKernel` (the final assertion).
Both proofs are `sorry`; there are no new definitions, helper axioms, or assumed
canonical maps. The diagonal tensor map is Mathlib's concrete
`Algebra.TensorProduct.mapRingHom`, not an arbitrary equivariant map.

Hypothesis and clause correspondence for the tensor assertion:

- Field extensions K ⊆ L and K ⊆ M: `[Field K] [Field L] [Field M]`,
  `[Algebra K L] [Algebra K M]`. The fields have independent universes u, v, w.
- M/K finite: `[FiniteDimensional K M]`. L/K is unrestricted.
- The actual algebra tensor product is a field: `hT : IsField (L ⊗[K] M)`.
  The canonical tensor multiplication is retained; no unrelated Field instance
  replaces that multiplication.
- Finite acting group N: `(N : Type g) [Group N] [Finite N]`.
- Automorphism actions on K, L, M: the monoid homomorphisms `σK`, `σL`, `σM`
  to the respective ring-automorphism groups. `hL` and `hM` say that both
  embeddings intertwine the same action `σK` on K. Thus they preserve K and
  restrict to the same automorphism there. There is no faithfulness assumption.
- The diagonal tensor action is the canonical map
  `Algebra.TensorProduct.mapRingHom (σK n).toRingHom (σL n).toRingHom
  (σM n).toRingHom (hL n) (hM n)`. Its pure-tensor formula is the diagonal
  formula by Mathlib's construction. Inverses and the action law follow from
  the group homomorphisms on the factors; neither is additional supplied data.
- Normal subgroup Q: `(Q : Subgroup N) [Q.Normal]`. Its trivial action on L is
  `hQ : ∀ q : Q, ∀ l : L, σL q l = l`.
- A = N/Q and its induced action on L: no extra action is chosen. The induced
  action's fixed elements are exactly those satisfying `∀ n : N, σL n l = l`,
  since the quotient map is surjective and Q acts trivially. The theorem uses
  these defining fixed-point equations directly, as does the landed sibling
  `Algebra.curveFieldKernelInvariantStep`.
- M^Q/K purely inseparable: `E : IntermediateField K M` and `hE` identify E
  exactly with `{m | ∀ q : Q, σM q m = m}`; `hEpi : IsPurelyInseparable K E`
  states its pure inseparability. E is uniquely specified, not an arbitrary
  substitute for M^Q. Its K-algebra structure is the canonical subfield one.
- R ⊆ L^A: `R : Subfield L` and `hR : ∀ r : R, ∀ n : N, σL n r = r`.
- L^A/R purely inseparable: `hRpi` asserts that every such fixed l has some
  `ringExpChar L` power in R. This is exactly the Mathlib criterion
  `isPurelyInseparable_iff_pow_mem`, including characteristic zero.
- The canonical embedding of L tensor E is
  `Algebra.TensorProduct.map (AlgHom.id K L) E.val`. The first conjunct states
  injectivity, making explicit the node's phrase "under the canonical embeddings".
- The fixed-field equality is the second conjunct: for every tensor x,
  x is fixed under every q precisely when it lies in that canonical map's range.
- "This fixed field is purely inseparable over L" is
  `IsField (L ⊗[K] E) ∧ IsPurelyInseparable L (L ⊗[K] E)`, together with the
  preceding injectivity and fixed-image equality. The L-algebra structure is
  Mathlib's canonical left-factor tensor algebra.
- T^N/R purely inseparable is the final conjunct: each N-fixed x has a power
  equal to `includeLeft (r : L)` for some `r : R`. The inclusion R → T is
  canonical and N-fixed by hR. Thus this power statement is the precise
  pure-inseparability criterion for that fixed-field extension.

Hypothesis and clause correspondence for the final assertion:

- Finite tower k ⊆ e ⊆ F: the three fields, `[Algebra k e] [Algebra e F]`
  `[Algebra k F] [IsScalarTower k e F]`, and
  `[FiniteDimensional k e] [FiniteDimensional e F]`.
- Finite groups J, G, H: their `[Group]` and `[Finite]` instances, in independent
  universes g, g', h. The two homomorphisms are `β : J →* G` and `α : G →* H`;
  both surjectivity clauses are `hβ` and `hα`.
- Compatible actions on the tower are `σk : H →* (k ≃+* k)`,
  `σe : G →* (e ≃+* e)`, and `σF : J →* (F ≃+* F)`.
  `hke` and `heF` explicitly give equivariance of each field embedding.
- Q = ker β is expressed by `β j = 1`; A = ker α by `α g = 1`;
  N = ker(αβ) by `α (β j) = 1`. These are their defining kernel equations.
- F^Q/e purely inseparable is `hFpi`: every Q-fixed x has a power in the
  range of `algebraMap e F`. Compatibility ensures e is contained in F^Q.
- e^A/k purely inseparable is `hepi`: every A-fixed element has a power in
  the range of `algebraMap k e`. Compatibility ensures k is contained in e^A.
- F^N/k purely inseparable is the conclusion, using the composite-kernel
  fixed equations and `(algebraMap k F).range`. Compatibility and the tower
  instance identify this embedding with the composite k → e → F.
- No action homomorphism is required to be injective in either theorem.

For every power clause, `ringExpChar` is p in positive characteristic and 1
in characteristic zero. Consequently the zero-characteristic clauses give
membership itself (and, with the already specified smaller-field inclusion,
equality), rather than omitting characteristic zero or assuming it separately.
The report's translations use the existing Mathlib pure-inseparability criterion,
not a second definition of that notion.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`.
- `def-pc-field-extension`: Mathlib `Algebra` and `algebraMap`, in
  `Mathlib.Algebra.Algebra.Defs` (imported transitively by the public imports).
- `def-pc-field-tower`: public import `Sheaf.FieldTheory.FieldTower`, declaration
  `FieldExtension.degree`; the node's finite-degree convention is rendered with
  its documented `FiniteDimensional`/`Module.Finite` Mathlib specialization.
- `def-weil-pbc-module-tensor-product`: Mathlib `TensorProduct`, `TensorProduct.tmul`,
  and `TensorProduct.lift`, in `Mathlib.LinearAlgebra.TensorProduct.Defs` and
  `.Basic`, supplied by public import `Mathlib.RingTheory.TensorProduct.Maps`.
  `Algebra.TensorProduct.map` and `.mapRingHom` give the required concrete maps.
- The already stated proof dependencies are imported privately:
  `Module.Basis.extend`, `.coe_extend`, `.subset_extend`,
  `linearIndepOn_singleton_iff` from `Mathlib.LinearAlgebra.Basis.VectorSpace`
  and its imports; `Module.Basis.baseChange` from
  `Mathlib.LinearAlgebra.TensorProduct.Basis`; and `iterateFrobeniusOfPrime`
  from `WeilConjectures.Mathlib.Algebra.CharP.Lemmas`.
- `def-weil-pbc-finite-purely-inseparable-extension` uses Mathlib
  `IsPurelyInseparable` from public import
  `Mathlib.FieldTheory.PurelyInseparable.Basic`. Its
  `isPurelyInseparable_iff_pow_mem` is the exact fixed-field power criterion.
  This proof dependency is public because its notion appears in the statement.

Edge cases checked: characteristic zero; positive characteristic with exponent
zero; a zero tensor and the empty finite-support sum; Q trivial or Q = N;
trivial N; M = K; L = K; R = L^A; both group surjections identities; trivial
kernels and nonfaithful actions. No finite-degree hypothesis on L/K, universe
identification, prime-characteristic restriction, or faithful-action assumption
was introduced. The source's finite hypotheses were retained even where the
algebra argument may work more generally. A zero tensor ring is correctly
excluded by hT, just as by the source's assumption that T is a field.

Searches performed on 2026-10-24:

- Prescribed `msearch.py ... leanfinder` query:
  "Fixed subfield of a tensor product with a trivial group action on one factor
  and purely inseparable invariants through kernels". Eight hits, including
  `IsPurelyInseparable.exists_pow_pow_mem_range_tensorProduct_of_expChar`,
  `FixedPoints.intermediateField`, and `IsGalois.of_fixed_field`. These provide
  ingredients, but none states the tensor fixed-image and two-kernel conclusion.
- Prescribed `msearch.py ... loogle` query:
  `FixedPoints.subfield, IsPurelyInseparable`. No hits.
- Prescribed `msearch.py ... grep` query:
  `fixedField.*[Tt]ensor|[Tt]ensor.*fixedField|[Ii]nvariant.*[Pp]urely`.
  No hits. The same local rg in Mathlib, WeilConjectures, and Sheaf had no match.
- Local rg in `lean/WeilConjectures` and `lean/Sheaf` for that expression and
  `tensor_kernel|tensorKernel|lem-sfb-tensor-kernel-inseparable-invariants`:
  no existing statement. A broader search of Sheaf/FieldTheory found the landed
  `CurveFieldKernelInvariantTower.lean`; it uses this item in its proof plan,
  with different hypotheses, so is not an existing match. It confirms the
  field-tensor and elementwise-power conventions used here.
- The upstream name index `dag/lean_names_upstream.json` had no match for the
  fixedField/tensor/purely-inseparable expression. No new notion or node is needed.

Sources read: the node and every statement-dependency record; their recorded
source signatures/docstrings; the recorded proof dependencies; Mathlib's tensor
map construction and purely inseparable power criterion; Stacks `fields.tex`,
Definitions/Lemmas 09HE, 09HG, 09HH; current blueprint direct-image reduction.
The de Jong PDF, marked WANTED in the inherited node, was accessible through
https://www.numdam.org/item/10.5802/aif.1575.pdf during this task; Remarks 2.3
confirm the composition context. The node explicitly calls its field calculation
agent-formulated, and its elementary proof is reproduced in the theorem docstrings.
No statement correction or disputed statement was needed.

Validation: `scompile.py Q18 lem-sfb-tensor-kernel-inseparable-invariants <module>`
compiled the module in both the sandbox and library probes with exit code 0,
in 1.5 and 1.6 seconds respectively, and no diagnostics.

## Second reading by Q18

Self-check by the delivering worker, not a claim of independent review (the
brief forbids starting other agents; the maintainer supplies independent review).
Re-read the node against both complete signatures. The quotient action on L is
rendered by its equivalent N-fixed equations; the tensor action is the actual
canonical Mathlib map; every fixed-field extension has its smaller-field inclusion
from hE/hR or action compatibility. Both source assertions and the characteristic
zero cases are present. No mismatch found. No new nodes or dependency modules.
