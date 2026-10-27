## Worker report

The module `Sheaf.Algebra.Lie.FaithfulSemisimpleTraceForm` states
`LieAlgebra.trace_pairing_nondegenerate_of_faithful`. It introduces a field `F` with
`Field F` and `CharZero F`; a Lie algebra `L` with `LieRing L`, `LieAlgebra F L`, and
`FiniteDimensional F L`; semisimplicity as `[HasTrivialRadical F L]`; a module `M` with
`AddCommGroup M`, `Module F M`, and `FiniteDimensional F M`; and a linear representation
`ρ : L →ₗ[F] Module.End F M`. The hypothesis `hbracket` renders the stated bracket
preservation equation, and `hfaithful` renders injectivity. The conclusion is exactly that
for every `x`, vanishing of `LinearMap.trace F M (ρ x ∘ₗ ρ y)` for every `y` implies `x = 0`.
This is the displayed trace form and its left-radical nondegeneracy clause.

The statement uses `Field` and `CharZero` from Mathlib, `LieRing`, `LieAlgebra`, and
`FiniteDimensional`, and `LinearMap.trace`. The semisimplicity interface is the recorded
`LieAlgebra.HasTrivialRadical`; its source declaration is `Mathlib.Algebra.Lie.Semisimple.Defs`.
The proof plan cites `WeilConjectures.Mathlib.Algebra.Lie.Radical` declarations
`LieAlgebra.hasTrivialRadical_iff_forall_isSolvable_eq_bot` and
`WeilConjectures.Mathlib.Algebra.Lie.CartanCriterion` declaration
`LieSubalgebra.isSolvable_of_trace_mul_eq_zero`, plus Mathlib's
`LinearMap.trace_comp_comm'`.

Edge cases checked: the zero Lie algebra and zero module satisfy the finite-dimensional
hypotheses; the conclusion is then the correct equality in a subsingleton/zero space. The
index-free formulation covers arbitrary finite dimensions, including dimension zero. A
nonfaithful representation is excluded exactly by `Function.Injective ρ`, as in the source.

Searches made before writing: `msearch.py ... leanfinder` for “The trace form of a faithful
finite dimensional representation of a semisimple Lie algebra over a characteristic zero field
is nondegenerate” returned eight hits, all Killing-form, Cartan-subalgebra, or irreducible-module
results and no exact theorem. `msearch.py ... loogle` for `"traceForm", "Nondegenerate"`
returned `LieAlgebra.IsKilling.traceForm_cartan_nondegenerate` and field trace-form results,
not this arbitrary faithful representation. `msearch.py ... grep` for
`traceForm.*nondegenerate|trace.*faithful|trace_mul_eq_zero` in `Algebra/Lie` found only
Killing/Cartan criterion files. `msearch.py ... leansearch` with the same natural-language
claim returned `LieModule.traceForm`, field trace forms, and Killing-form results, with no exact
match. Repository `rg` found no existing faithful semisimple trace-pairing declaration.

No statement correction or new node was needed. No `STATEMENT-DISPUTED` flag applies.


The source was read directly in `literature/milne-algebraic-groups_iAG2017.pdf`, §22c,
printed p.475, including the standing convention that the field has characteristic zero and
all Lie algebras and representations are finite-dimensional. It explicitly defines
Bρ(x,y) = Tr(ρ(x) ∘ ρ(y)) and deduces its nondegeneracy for faithful representations from
Cartan's criterion and the absence of nonzero solvable ideals. No algebraic closure, simple
representation, positive dimension, or irreducibility assumption has been added. The formula
is bilinear by linearity of `ρ`, composition, and `LinearMap.trace`; symmetry follows from
`LinearMap.trace_comp_comm'`. The theorem writes its nondegeneracy in precisely the elementwise
form after the colon in the node, so it requires no new definition of the trace form or of a
representation. In particular, it does not introduce a second version of `LieModule.traceForm`.

The statement dependencies and declarations read were:

- `def-weil-field`: `Field` in `Mathlib.Algebra.Field.Defs`, including its docstring and
  commutative-ring/division-ring superclass signature.
- `def-wf-lie-algebra`: `LieRing` and `LieAlgebra` in `Mathlib.Algebra.Lie.Basic`, including
  alternating bracket, Jacobi in Leibniz form, module structure and scalar compatibility.
  The linear map and bracket-preservation hypothesis spell out the representation definition
  from that same node, without relying on an auxiliary action instance.
- `def-wf-semisimple-lie-algebra`: `LieAlgebra.HasTrivialRadical` in
  `Mathlib.Algebra.Lie.Semisimple.Defs`, with
  `LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals` in
  `Mathlib.Algebra.Lie.Semisimple.Basic`; the latter says exactly that every solvable ideal
  vanishes. The recorded upstream specialization in
  `WeilConjectures.Mathlib.Algebra.Lie.Radical` was also read and is imported for the proof.
- `def-weil-finite-dimensional-subspace`: `FiniteDimensional` in
  `Mathlib.LinearAlgebra.FiniteDimensional.Defs`, the abbreviation for `Module.Finite`.
  This is used for both `L` and `M` with independent universes `v` and `w` over `F : Type u`.
- `def-weil-endomorphism-trace`: `LinearMap.trace` in `Mathlib.LinearAlgebra.Trace`,
  its linear-map signature, basis-independent definition and `trace_eq_matrix_trace`.
  On finite-dimensional vector spaces this is exactly the ordinary finite-basis trace.

The proof-only imports are `WeilConjectures.Mathlib.Algebra.Lie.CartanCriterion` for the
recorded characteristic-zero Cartan criterion and `WeilConjectures.Mathlib.Algebra.Lie.Radical`
for the recorded solvability and semisimplicity interfaces. The trace-cyclicity proof dependency
is already provided by the public `Mathlib.LinearAlgebra.Trace` import. The four proof steps are
reproduced in the theorem docstring; its entire proof is `sorry`, as required for stage 2.

Direct searches used `rg` for trace-form/faithful/nondegeneracy terms in `lean/WeilConjectures`,
`lean/Sheaf`, and the Mathlib Lie theory, and `grep -rn` for the item id in
`lean/WeilConjectures`; the item id had no upstream match. Exact proposed declaration names were
also checked for collisions. The wrappers' four search results are logged in the sandbox's
`searches.jsonl`; the Mathlib grep returned seven hits. No repair note for the item was found.

Validation: the prescribed `scompile.py Q16 lem-sfb-faithful-semisimple-trace-form` compiled the
single delivered file both as a sandbox file and with its real module name on the live server.
Both invocations passed, with no unexpected warnings. All universes are declared explicitly,
and `set_option autoImplicit false` prevents hidden implicit variables.

## Second reading by Q16

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
