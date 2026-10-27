## Worker report

Item: `lem-trf-tensor-base-change-ideal-power-quotients`, group Q24, stage 2.

The module `Sheaf.RingTheory.TensorBaseChangeIdealPowerQuotients` states
`Algebra.TensorProduct.tensor_base_change_ideal_power_quotients`. Its only theorem
has proof `sorry`; no definitions or other theorems are introduced. The node is
unchanged except for its `lean` field. No statement correction, new nodes, or
dependency repairs are needed. No mathematical dispute was found.

The source is the explicit five-step calculation in this node, using Stacks
`algebra.tex`, Tag 00CX, `lemma-tensor-product`. I read the tensor construction,
universal property, and generation argument there. As the node's source and split
report explain, the finite scalar-congruence lemma is an extracted calculation,
not a standalone theorem asserted to be quoted verbatim from Tag 00CX.

### Every hypothesis and conclusion

| Node text | Lean rendering |
| --- | --- |
| Commutative rings R, B, C | `{R : Type u} {B : Type v} {C : Type w}` with the three `CommRing` instances; the universes are independent and explicitly declared. |
| Structure maps iota and rho of R-algebras B and C | `[Algebra R B] [Algebra R C]`, with `algebraMap R B` and `algebraMap R C`. These instances range over all structure maps. |
| Ideals I in R and J in C | `(I : Ideal R) (J : Ideal C)`. |
| Extension IC contained in J | `hIC : I.map (algebraMap R C) ≤ J`. `Ideal.map` is the generated image ideal, rather than a set-theoretic image. |
| Integer n at least 1 | `(n : ℕ) (hn : 1 ≤ n)`; positive natural numbers encode exactly these integer exponents. |
| R-algebra map pi to R/I^n | `π : B →ₐ[R] R ⧸ I ^ n`. The quotient has Mathlib's canonical R-algebra structure. |
| pi composed with iota is the quotient map | Built into `AlgHom.commutes'`: `π (algebraMap R B r) = algebraMap R (R ⧸ I ^ n) r`, whose right side is `Ideal.Quotient.mk (I ^ n) r`. No additional compatibility assumption is needed or omitted. |
| pi surjective | `hπ : Function.Surjective π`. |
| Kernel equals I^n B | `hker : RingHom.ker π.toRingHom = (I ^ n).map (algebraMap R B)`. |
| D = C tensor_R B, with the specified multiplication and unit | `C ⊗[R] B`, with Mathlib's `Algebra.TensorProduct.instCommRing`; multiplication is `tmul_mul_tmul` and the unit is `1 ⊗ₜ[R] 1`. This is the module tensor product of the recorded dependency. |
| f(c) = c tensor 1 | Mathlib's canonical `algebraMap C (C ⊗[R] B)`, definitionally the left inclusion; the forward formula explicitly uses `c ⊗ₜ[R] (1 : B)`. |
| Extended ideal J^n D | `(J ^ n).map (algebraMap C (C ⊗[R] B))`. The power is taken in C before extending, as in the node. |
| Canonical alpha from C/J^n to D/J^n D is an isomorphism | Witness `e : (C ⧸ J ^ n) ≃+* ((C ⊗[R] B) ⧸ (J ^ n).map (algebraMap C (C ⊗[R] B)))`, with the forward identity for every `c : C`. Thus its underlying map is exactly `[c] ↦ [c ⊗ 1]`. |
| rhoBar is induced by rho | Witness `rhoBar : (R ⧸ I ^ n) →+* (C ⧸ J ^ n)` and the first conjunct, requiring its value on every scalar quotient representative to be the class of `algebraMap R C r`. |
| Inverse sends [c tensor b] to [c] rhoBar(pi(b)) for every c, b | The last conjunct universally quantifies `(c : C) (b : B)` and gives exactly this equality for `e.symm`. |

The existential witnesses are fully characterized maps, not arbitrary substitute
maps: quotient representatives exhaust their sources, so the first two conjuncts
uniquely determine `rhoBar` and the forward map of `e`. A ring equivalence includes
both inverse identities. Consequently this is equivalent to the claim that the
canonical map is an isomorphism, together with the stated formula for its inverse.
In particular `rhoBar` is supplied as a conclusion, not assumed as extra data.

### Dependency declarations read and used

Both statement dependencies are Mathlib leaves with `mathlib_match` records, so
neither requires a project `lean` record or a replacement module.

- `def-weil-pbc-module-tensor-product`: `TensorProduct`, `TensorProduct.tmul`, and
  `TensorProduct.mk` in `Mathlib.LinearAlgebra.TensorProduct.Defs`; its universal
  property is `TensorProduct.lift` and `TensorProduct.ext'` in
  `Mathlib.LinearAlgebra.TensorProduct.Basic`. The tensor-product imports expose
  these declarations. Their signatures and surrounding docstrings were read.
- `def-weil-pbc-algebra-hom-quotient`: `AlgHom` in
  `Mathlib.Algebra.Algebra.Hom`; `Ideal.Quotient.algebra`,
  `Ideal.Quotient.mkₐ`, and the quotient algebra-map identities in
  `Mathlib.RingTheory.Ideal.Quotient.Operations`; ideal multiplication and powers
  via the ideal semiring structure in `Mathlib.RingTheory.Ideal.Operations`.
  The signature and defining compatibility of `AlgHom` and the quotient-algebra
  construction were read. The module publicly imports the quotient operations.
- Proof dependency `lem-weil-pbc-algebra-tensor-pushout-universal-property`:
  `Algebra.TensorProduct.instCommRing`, `tmul_mul_tmul`, `includeLeft`,
  `includeRight`, and `ext` in `Mathlib.RingTheory.TensorProduct.Basic`, and
  `productMap`, `productMap_apply_tmul`, `productMap_left`, `productMap_right`
  in `Mathlib.RingTheory.TensorProduct.Maps`. I read the signatures and
  docstrings. Basic is public because the statement needs the algebra tensor
  structure; Maps is a plain proof import as the stage contract requires.

The theorem docstring carries all five proof steps: construct the induced scalar
map, invoke the algebra tensor universal property, descend both maps through
the ideals, use the kernel equality and balancing on a chosen representative,
and check the composites using additive generation by pure tensors.

### Edge cases checked

- `n = 1`: the formula reduces to the same first-level scalar congruence;
  no part of the signature requires `n > 1`.
- `n = 0`: excluded exactly by `hn`, as the node specifies; no further
  positive-exponent restriction is imposed.
- `J = ⊤`: both quotient rings are the zero ring and both characterizing
  formulas remain valid. No `Nontrivial` instances occur.
- `I = ⊤`: `hIC` forces `J = ⊤`, so this is also covered.
- `I = ⊥`: the scalar congruence makes B isomorphic to R via pi, giving
  precisely the ordinary tensor cancellation on every J-power quotient.
- `B = R`, pi the quotient map: all assumptions hold and the equivalence is
  the usual identification of C tensor_R R with C, modulo J^n.
- Zero rings, nilpotents, arbitrary characteristic, and distinct universes:
  none is excluded. No local, Noetherian, finite-type, flat, or domain
  assumption has been introduced.
- Dropping the kernel equality would be wrong: over a field, take
  `B = R[X]`, pi evaluation at zero, `I = J = 0`, `C = R`, `n = 1`.
  The conclusion would identify R with R[X]. The required `hker` excludes it.

### Searches for existing statements

All search commands used the prescribed `msearch.py` wrapper for Q24 and this
item. Queries and results on 2026-10-24:

- LeanSearch: `Tensor base change preserves larger ideal power quotients under
  a finite level scalar congruence`. Eight hits, including
  `TensorProduct.AlgebraTensorModule.cancelBaseChange.congr_simp`,
  `LinearMap.liftBaseChange_tmul`, `LinearEquiv.baseChange`, and
  `IsBaseChange.tensorEquiv`. These are structural tensor results and do not
  assert the node's kernel-congruence cancellation or inverse formula.
- LeanFinder: `If B modulo I^n B is R modulo I^n as an R algebra, then C/J^n
  is isomorphic to (C tensor_R B)/J^n whenever IC is contained in J`.
  Eight hits, principally `Algebra.TensorProduct.quotIdealMapEquivTensorQuot`
  and its representative formulas, plus adic-completion tensor equivalences.
  The principal quotient equivalence concerns tensoring with the quotient
  of the base ring, rather than the given B with its specified pi and kernel.
- Loogle: `TensorProduct, "quot"`. Twelve hits including
  `Ideal.quotMapEquivTensorQuot`, `TensorProduct.quotTensorEquivQuotSMul`,
  `tensorQuotEquivQuotSMul`, `quotientTensorEquiv`, and
  `tensorQuotientEquiv`, and their representative formulas. None is the
  asserted finite-congruence result.
- Mathlib grep through the wrapper:
  `quotIdealMapEquivTensorQuot|quotientTensorEquiv|quotientMap` in
  `RingTheory/TensorProduct`. Five hits in
  `Mathlib/RingTheory/TensorProduct/Quotient.lean`. I opened that file and read
  the canonical quotient equivalence and its formulas. They are tools for
  a proof, not an exact existing declaration of this theorem.
- Project `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the item id
  found only a proof-docstring citation in `AdicBaseTensorLocalComparison`.
  I opened that module: it states a completion/localization comparison
  under Noetherian and finite-type assumptions, not this theorem.
- Project searches for tensor/ideal/quotient combinations found related
  quotient, adic-completion, and localization statements, with no exact
  match. Searches for `tensor_base_change_ideal_power_quotients` and
  `TensorBaseChangeIdealPowerQuotients` in those trees and
  `dag/lean_names_upstream.json` found no declaration/name clash.

### Validation

`scompile.py Q24 lem-trf-tensor-base-change-ideal-power-quotients` compiled this
module cleanly in module mode, first as the sandbox probe (6.2 seconds), then
under its library module name (5.5 seconds). No errors or unexpected warnings.
All variables/universes are explicit, auto-implicits are disabled, and the
maximum Lean line width is 89 characters. Only the prescribed wrappers compile
or perform Git bookkeeping; no live project sources were modified directly.

## Second reading by Q24

I reread the node and the completed module after compilation. This is a second
pass by the dispatched worker; the dispatch explicitly prohibits starting other
agents, and the maintainer's independent review remains separate.

I checked the three ring binders, both algebra structures, both ideals, the
extension containment, positivity, pi's algebra compatibility and surjectivity,
and its kernel equality against the node. Each appears exactly as mapped above.
I then checked the factor order is C tensor_R B, that the extended ideal comes
from J^n in C, and that the forward formula is c tensor 1 rather than the
opposite inclusion. Finally I checked rhoBar on every scalar representative and
the inverse formula on every pair c, b, including the order of the two factors.

No mismatch was found and no change was needed. In particular the existential
equivalence is constrained by its full forward representative formula, and
rhoBar is characterized in the conclusion rather than imposed as a hypothesis.
This does not replace either canonical map by an unconstrained witness. The
only postponed result is the one named theorem matching this DAG node.
