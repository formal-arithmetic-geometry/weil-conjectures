## Worker report

The module `Sheaf.RingTheory.MittagLefflerQuotientProductVanishing` states
`Module.isMittagLeffler_quotient_product_vanishing`, with a single `sorry` proof.
It packages exactly the two assertions of the unchanged DAG statement as a conjunction.
No definitions, extra nodes, dependency repairs, or statement changes are needed.
Only the item's `lean` field changes.

Source read: `literature/stacks-project/algebra.tex`, `lemma-minimal-contains`
(Tag 0AS6), specifically the two displayed quotient-product maps and their zero-image
implication, and `proposition-ML-tensor` (Tag 059M), condition (2).
The source's later flatness argument is outside this auxiliary statement.
The docstring carries all three DAG proof steps, including the tensor symmetries,
the factorization of the comparison, and the coordinatewise lift calculation.

Hypothesis and clause correspondence:

| DAG hypothesis or clause | Lean rendering |
| --- | --- |
| Commutative ring R | `{R : Type u} [CommRing R]` |
| R-module M | `{M : Type v} [AddCommGroup M] [Module R M]` |
| M is Mittag-Leffler | `(hML : Module.IsMittagLeffler.{u, v, w, t} R M)` |
| R-module E | `{E : Type t} [AddCommGroup E] [Module R E]` |
| Any set J | `{J : Type w}`, without finiteness or nonemptiness |
| Submodule family | `(N : J → Submodule R E)` |
| Quotient E/N_j | `E ⧸ N j`, the existing quotient module |
| P is the module of all families of quotient classes | `(∀ k : J, E ⧸ N k)`, with componentwise module structure |
| q sends e to its quotient classes | `LinearMap.pi (fun j : J => (N j).mkQ)` |
| β sends a tensor m to the family of coordinate tensors | `LinearMap.pi (fun j : J => LinearMap.rTensor M (LinearMap.proj j : (∀ k : J, E ⧸ N k) →ₗ[R] E ⧸ N j))` |
| β is injective | `Function.Injective` of that precise linear map, the first conjunct |
| Every x in E tensor M | `∀ x : TensorProduct R E M` in the second conjunct |
| x lies in every inclusion-induced tensor image | `(∀ j : J, x ∈ Set.range (LinearMap.rTensor M (N j).subtype))` |
| Therefore (q tensor id_M)(x) is zero | `LinearMap.rTensor M (LinearMap.pi (fun j : J => (N j).mkQ)) x = 0` |

The coordinate formula for β follows directly from the existing definitions
`LinearMap.pi`, `LinearMap.proj`, and `LinearMap.rTensor`: the jth coordinate of
β applied to `a ⊗ m` is `a j ⊗ m`. Thus β is constructed canonically in the
statement itself, rather than introduced as an arbitrary map with an extra hypothesis.
The same applies to q. `Set.range` expresses existence of an actual tensor lift
and does not assume inclusion-induced tensor maps injective.

Dependency declarations read and used:

- `def-trf-mittag-leffler-module`: `Module.IsMittagLeffler`, in
  `Sheaf.RingTheory.IsMittagLeffler`. Its full body uses
  `TensorProduct.piRightHom R R P Q` for arbitrary index sets and test modules.
- `def-weil-pbc-module-tensor-product`: Mathlib `TensorProduct`,
  `TensorProduct.mk`, `TensorProduct.lift`, `TensorProduct.ext'`, and
  `LinearMap.rTensor`. Source modules are
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, `.Basic`, and `.Map`.
  The statement directly uses `TensorProduct` and `LinearMap.rTensor`.
- Proof dependency `lem-weil-pbc-module-tensor-comm`: `TensorProduct.comm`,
  `TensorProduct.comm_tmul`, and `TensorProduct.map_comp_comm_eq` in Mathlib
  `.TensorProduct.Basic` and `.Map`. They are already exposed by the public tensor-map
  import needed for the statement, so no additional proof-only import is necessary.
- Canonical coordinates and quotients: `LinearMap.pi`, `LinearMap.proj` in
  `Mathlib.LinearAlgebra.Pi`, `Submodule.mkQ` in
  `Mathlib.LinearAlgebra.Quotient.Defs`, and `Submodule.subtype`.

Universe check: R, M, E, and J have independent universes u, v, t, and w.
The recorded Mittag-Leffler definition uses test modules in `Type (max u v t)`.
Quotients of E can be transported to that universe via their standard ULift module
equivalences; tensor and product transport preserve the injectivity assertion.
This is the same size convention used by the existing least-tensor-support consumer.
No equality of universes or additional size hypothesis is imposed.

Edge cases checked mathematically before writing:

- Empty J: P and both tensor-product targets are zero modules. The first conjunct is
  injectivity between zero modules; the second has a vacuous support premise and concludes
  zero for the zero-target map, without incorrectly requiring x itself to be zero.
- Every N_j top: all quotients vanish, and all support images are the full tensor module;
  q tensor id has zero target.
- Some N_j bottom: its support image is zero, so the premise forces x = 0.
- E = 0, M = 0, x = 0, and the zero ring all give the expected zero assertions.
- Arbitrarily infinite J remains allowed; no finite-product isomorphism is substituted.
- Nonflat Mittag-Leffler modules remain allowed: e.g. a finitely presented nonflat module
  still has injective product comparison. No flatness or quotient-product surjectivity is used.

Searches for an exact existing statement (2026-10-24):

- `msearch.py ... leanfinder`, query
  `Mittag Leffler module product of quotient modules tensor injective comparison and quotient product tensor vanishing`:
  eight hits including `TensorProduct.forall_vanishesTrivially_iff_forall_rTensor_injective`,
  `rTensor_mkQ`, and `Ideal.pi_mkQ_rTensor`. None gives the two-clause arbitrary-product
  Mittag-Leffler assertion; the ideal comparison assumes a finite index.
- `msearch.py ... loogle`, query `"TensorProduct", "piRightHom"`:
  six hits including `TensorProduct.piRightHom`, its bilinear implementation and pure-tensor
  formula, and algebra variants. These construct the comparison with M on the left;
  none states the required theorem.
- `msearch.py ... grep`, query `Mittag|piLeftHom|piRightHom`, subdirectory `LinearAlgebra`:
  five hits in `Mathlib/LinearAlgebra/TensorProduct/Pi.lean`, giving `piRightHom`.
  The finite comparison `piLeft` is not usable for arbitrary J.
- `msearch.py ... leansearch`, query
  `For a Mittag Leffler module the comparison from a product of quotients tensor M to the product of tensors is injective and kills common supported tensors`:
  eight hits including `Module.FaithfullyFlat.tensorProduct_mk_injective`,
  `Ideal.pi_mkQ_rTensor`, `TensorProduct.tensorQuotientEquiv`, and
  `Module.Flat.iff_lTensor_injectiveₛ`; no exact statement.
- Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, query
  `quotient.product|quotientProduct|quotient_product|ml_quotient|piRightHom`:
  found the existing Mittag-Leffler definition, finite-presentation product comparison,
  and least-support theorem; no exact two-clause theorem. Additional `Mittag` searches
  distinguish module Mittag-Leffler from unrelated Mittag-Leffler towers.
- `grep -rn 'lem-trf-ml-quotient-product-vanishing' lean/WeilConjectures`: no hit.
- Exact declaration/module name searched in Mathlib, both project roots, and
  `dag/lean_names_upstream.json`: no collision.

Validation: prescribed `scompile.py Q15 lem-trf-ml-quotient-product-vanishing <module>`
passed both sandbox and final library-path compilation, each in 1.0 seconds,
without errors or unexpected warnings. `autoImplicit` is disabled in the module.
No statement dispute or node fault was found.

## Second reading by Q15

I reread the delivered signature alongside the unchanged node, after the clean compile.
This is a second pass by the assigned single worker; the maintainer's independent review
is separate, and no other agent was started. Both conclusions are present: injectivity
is unconditional in x, while vanishing is quantified over every x under precisely the
all-submodule-image premise. The tensor order is P tensor M throughout, not M tensor P.
The maps are actual coordinate tensor maps and actual quotient maps, with no arbitrary-map
binder. Empty J and independent universes remain included. The statement has no
flatness, nonzero-ring, finiteness, nonemptiness, or surjectivity hypothesis.
No mismatch was found and no mathematical statement was changed.
