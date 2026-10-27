## Worker report

Stage 2, group Q35, item `lem-sfb-finite-dual-hopf-module`.

The module `Sheaf.RingTheory.HopfAlgebra.FiniteDualHopfModule` defines the concrete bilinear map `HopfAlgebra.finiteDualAction` and states `HopfAlgebra.finiteDual_hopfModule`. The theorem has the sole postponed proof, `sorry`. The action has real data: the composite of the antipode, linear multiplication, and `Module.Dual.transpose`. No choice of unspecified data, private definition, local instance, or additional axiom is used. There are no new nodes, dependency repairs, or statement corrections. The accepted natural-language statement and split are unchanged.

The inherited BLOCKED ending concerned the already accepted stage-1 split by Q87. The current node has no Lean record and is a stage-2 queue item. The stage-handoff instruction in `coord/brief-stage2.md` §0 explicitly authorizes writing the stage-2 statement in this situation; this delivery preserves Q87's accepted split.

Hypotheses and clauses, in their original order:

- A field k: `(k : Type u) [Field k]`. This is exactly `def-weil-field`'s Mathlib match, including nontriviality. There is no characteristic restriction.
- A unital commutative k-algebra H with the specified Hopf structure: `(H : Type v) [CommRing H] [HopfAlgebra k H]`. Mathlib's `HopfAlgebra` extends `Bialgebra`, hence supplies its k-algebra, linear comultiplication and counit, their algebra-map laws, coassociativity, both counit identities, and both antipode identities. The node takes S as an algebra map; Mathlib takes it as linear and its algebra-map property in the commutative case follows from the usual antipode anti-multiplicativity and unit identities (Zheng Proposition 4.2). These are equivalent descriptions of the same commutative Hopf algebra, without an extra hypothesis.
- A finite k-basis: `(ι : Type w) [Finite ι] (basis : Module.Basis ι k H)`. `Module.Basis` is exactly a linear coordinate equivalence with finitely supported functions, as used by the recorded `Module.Free` interface. The theorem is quantified over every such basis and does not restrict its cardinality or indexing universe. `Finite` asserts finiteness without choosing an enumeration.
- H* and pointwise vector operations: `Module.Dual k H`, definitionally `H →ₗ[k] k`, with Mathlib's usual linear-map module structure.
- Module tensors and algebra tensors: Mathlib's `TensorProduct`, with `Algebra.TensorProduct` structures on the same tensor type. All unit/associativity identifications are explicitly applied.
- The displayed action formula: the first conjunct is `∀ h f x, finiteDualAction k H h f x = f (antipode k h * x)`. Bilinearity is in the real definition's type `H →ₗ[k] Module.Dual k H →ₗ[k] Module.Dual k H`.
- Unital action: the second conjunct `∀ f, finiteDualAction k H 1 f = f`.
- Associative left action: the third conjunct `∀ h h' f, finiteDualAction k H h (finiteDualAction k H h' f) = finiteDualAction k H (h * h') f`.
- Existence of the linear coaction: `∃ ρ : Module.Dual k H →ₗ[k] H ⊗[k] Module.Dual k H`.
- Its characterization: for every f and x, the first conjunct under the existential equates `TensorProduct.rid k H ((Module.Dual.eval k H x).lTensor H (ρ f))` with `TensorProduct.lid k H (f.rTensor H (Coalgebra.comul x))`. On pure tensors these are respectively sum f_(-1) f_(0)(x) and sum f(x_1) x_2, exactly the node's equation. Evaluation is on the final dual factor, not the first factor of Delta.
- Uniqueness: the next conjunct quantifies over every linear map `ρ'` satisfying only that characterization and asserts `ρ' = ρ`. Thus uniqueness is not restricted to maps already known to satisfy the coaction or compatibility identities.
- Coassociativity: `∀ f, TensorProduct.assoc ... ((Coalgebra.comul ...).rTensor ... (ρ f)) = ρ.lTensor H (ρ f)`. This is precisely `(Delta tensor id) rho = (id tensor rho) rho` under the associator.
- Counit: `∀ f, TensorProduct.lid ... ((Coalgebra.counit ...).rTensor ... (ρ f)) = f`.
- Diagonal compatibility: the final conjunct applies `TensorProduct.tensorTensorTensorComm` to `Coalgebra.comul h ⊗ₜ ρ f`, swaps the two middle factors, and then applies `TensorProduct.map (LinearMap.mul' k H) (TensorProduct.lift (finiteDualAction k H))`. A pure term `(h_1 tensor h_2) tensor (a tensor g)` becomes `(h_1*a) tensor (h_2 dot g)`, exactly the specified double Sweedler sum. This is not multiplication on only the first coaction factor.

The module docstring and the theorem docstring cite both primary sources and the blueprint id. The theorem docstring reproduces the accepted six-step proof: action laws; finite dual-basis reconstruction and uniqueness; counit; coassociativity detected by evaluation; the antipode anti-coalgebra identity via convolution inverses; and diagonal compatibility by antipode cancellation.

Dependency declarations inspected and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs` (re-exported through the imports); its complete class signature and documentation were read.
- `def-weil-pbc-free-module`: `Module.Free`, `Mathlib.LinearAlgebra.FreeModule.Basic`, with `Module.Free.exists_basis` and the underlying `Module.Basis` from `Mathlib.LinearAlgebra.Basis.Defs`. The finite basis hypothesis directly uses that existing basis type.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` in `Mathlib.LinearAlgebra.TensorProduct.Defs`; `TensorProduct.lift`, `.lift.tmul`, `.ext'` in `.Basic`; `LinearMap.lTensor` and `.rTensor` in `.Map`. The recorded declarations' signatures and documentation were read.
- `lem-weil-pbc-algebra-tensor-pushout-universal-property`: `Algebra.TensorProduct.instCommRing`, `.instAlgebra`, `.tmul_mul_tmul`, `.includeLeft`, `.includeRight`, `.ext` in `Mathlib.RingTheory.TensorProduct.Basic`; `.productMap`, `.productMap_apply_tmul`, `.productMap_left`, `.productMap_right` in `.Maps`. The source signatures and documentation were read; the tensor algebra and multiplication are these existing structures, not copied constructions.
- Proof dependency `lem-sfb-convolution-linear-map-algebra`: `LinearMap.convRing`, `.convAlgebra`, `.convMul_apply`, `.convOne_apply`, `.convAlgebraMap_apply`, `Mathlib.RingTheory.Coalgebra.Convolution`, imported via `Mathlib.RingTheory.HopfAlgebra.Basic`. These give the accepted convolution-inverse proof route.

Other existing interfaces used: `HopfAlgebra`, `HopfAlgebra.antipode`, `Coalgebra.comul`, `Coalgebra.counit`; `Module.Dual`, `.transpose`, `.eval`; `TensorProduct.lid`, `.rid`, `.assoc`, `.tensorTensorTensorComm`; `LinearMap.mul`, `.mul'`. Their definitions/signatures were inspected. There is no second Hopf algebra, dual, action structure, or tensor-product definition.

Edge cases checked before writing:

- H=k with its usual Hopf structure: S=id, the action is scalar multiplication and rho(f)=1 tensor f under the unit identifications. The evaluation formula and all laws reduce to scalar multiplication.
- An empty basis would force H=0, impossible since a counit algebra map H→k preserves 1 and k is nontrivial. The Lean statement nevertheless imposes no `Nonempty ι`, so it silently excludes no indexing case.
- In characteristic 2, H=k[t]/(t^2) with primitive t is allowed. For the dual basis epsilon, lambda with lambda(t)=1, rho(epsilon)=1 tensor epsilon+t tensor lambda, rho(lambda)=1 tensor lambda, t dot epsilon=0, and t dot lambda=epsilon. These satisfy the displayed diagonal law; no sign or separability assumption is needed.
- The commutative function Hopf algebra k^G for a finite nonabelian group need not be cocommutative. No `Coalgebra.IsCocomm`, commutation of the two comultiplication factors, or bijectivity of S occurs in the statement.
- Zero functionals and h=0 are included by the bilinear map and linear coaction; universes u, v, w are independent and explicit.

Searches (run through the prescribed msearch.py wrapper):

- LeanFinder: `The dual of a finite dimensional commutative Hopf algebra has an antipode action and compatible left coaction`: eight hits, on Hopf algebra structures and antipode cancellation, including `HopfAlgebra.mul_antipode_lTensor_comul_apply`, `HopfAlgebra.ofAlgHom`, and `HopfAlgebraStruct.antipode`; none asserts the dual Hopf-module construction or its uniqueness and compatibility.
- Loogle: `HopfAlgebra, Module.Dual`: zero hits.
- Mathlib grep: `dual|comodule|coaction|HopfModule` under `RingTheory/HopfAlgebra`: zero hits.
- Project rg: `dual.*[Hh]opf|[Hh]opf.*dual|[Hh]opfModule|lem-sfb-finite-dual-hopf-module` under `lean/WeilConjectures` and `lean/Sheaf`: only an unrelated Lie-subalgebra `dualUnit` declaration; no match for the item. The further Hopf-module/coaction search under the RingTheory trees found affine action modules, not this construction.
- Name collision search: `finiteDualAction|finiteDual_hopfModule` in both project trees and `dag/lean_names_upstream.json`: no hits.

Sources read: [Zheng, Proposition 4.12(2), printed p.8](https://math.uchicago.edu/~may/REU2020/REUPapers/Zheng,Siqi.pdf) and [Farnsteiner, printed p.1](https://www.math.uni-bielefeld.de/~sek/select/HopfMod2.pdf). They give the antipode action and convolution characterization. The evaluation characterization is the same formula after testing the remaining dual factor against all functionals. The node already makes the diagonal action explicit; no source or statement change is required. The local PDFs remain absent as noted by the accepted split; no shared repository files were changed.

Validation: the first server scompile.py run elaborated the entire file and reported only the unused-Fintype-in-type linter. Replaced `[Fintype ι]` by the equivalent finiteness hypothesis `[Finite ι]`; the final server compile and required delivery preflight are recorded by the delivery wrapper. All writes are in this item's sandbox, and all builds use the authorized single-file wrapper.

## Second reading by Q35

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
