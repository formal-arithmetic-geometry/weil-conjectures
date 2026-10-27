## Worker report

The new module `Sheaf.LinearAlgebra.FreeSurjectionsCommonStabilization` states
`Module.free_surjections_common_stabilization`, with a single `sorry` proof.
It states the unchanged DAG statement, including existence of lifts and the
assertion for **every** pair of lifts. No definitions, helper nodes, dependency
repairs, or statement corrections are needed.

The hypothesis and conclusion correspondence is as follows.

| DAG clause | Lean rendering |
| --- | --- |
| Commutative ring R | `(R : Type u) [CommRing R]` |
| R-module M | `(M : Type v) [AddCommGroup M] [Module R M]`, with independent universes `u v` |
| Nonnegative integers n,m | `(n m : ℕ)` |
| F=R^n and G=R^m | `Fin n → R` and `Fin m → R`, the standard finite free modules |
| Surjective R-linear maps π and π' | Linear-map binders followed by `hπ : Function.Surjective π` and `hπ' : Function.Surjective π'` |
| There are f:G→F and g:F→G | First conjunct `∃ (f : (Fin m → R) →ₗ[R] (Fin n → R)) (g : (Fin n → R) →ₗ[R] (Fin m → R)), ...` |
| πf=π' and π'g=π | `π.comp f = π' ∧ π'.comp g = π` |
| For any such f,g | Second conjunct `∀ f g, π.comp f = π' → π'.comp g = π → ...` |
| U:F⊕G→G⊕F is a linear isomorphism | `∃ U : ((Fin n → R) × (Fin m → R)) ≃ₗ[R] ((Fin m → R) × (Fin n → R)), ...` |
| U(x,y)=(y+g(x-fy),x-fy) | First property of U, universally quantified over `x` and `y`, gives exactly this formula |
| The specified inverse | Second property, universally quantified over `a` and `b`, is `U.symm (a, b) = (b + f (a - g b), a - g b)` |
| p(x,y)=πx, q(a,b)=π'a, q∘U=p | `π.comp (LinearMap.fst R (Fin n → R) (Fin m → R))`, the analogous `π'` composite, and equality of their composites with `U.toLinearMap` |
| U(ker π⊕G)=ker π'⊕F | `Submodule.map U.toLinearMap ((LinearMap.ker π).prod ⊤) = (LinearMap.ker π').prod ⊤` |

For a binary direct sum of modules, the ordinary product is its canonical
underlying module. `Submodule.prod` therefore represents the embedded kernel
direct sums, and `Submodule.map` is their actual image in the target. The forward
formula determines U uniquely, so the existential equivalence states that the
displayed map itself is an isomorphism, with the displayed inverse. It does not
merely assert an unrelated abstract isomorphism of stabilized modules or kernels.

Dependencies read and used:

- `def-weil-pbc-free-module`: `Module.Free` in
  `Mathlib.LinearAlgebra.FreeModule.Basic`, whose `exists_basis` field is exactly
  existence of an indexed basis. The standard finite powers are the concrete
  free modules of the node; no extra freeness hypothesis or duplicate notion is
  introduced. This recorded module is publicly imported.
- `lem-weil-pbc-free-module-projective`: the Mathlib match
  `Module.Projective.of_free` in `Mathlib.Algebra.Module.Projective`.
- `def-weil-pbc-projective-module`: `Module.Projective` and its equivalent lifting
  theorem `Module.projective_lifting_property` in the same module. Its full
  signature gives `∃ h, f.comp h = g` for a surjection f and map g from a
  projective domain. The two proof dependencies share one plain proof import.
- `Mathlib.LinearAlgebra.Prod` supplies the binary-product linear maps and
  equivalences and `Submodule.prod`. `LinearMap.comp`, `LinearMap.ker`, and
  `Submodule.map` are Mathlib constructions, not new definitions.

Sources inspected: `literature/stacks-project/more-algebra.tex`, the complete
proof of `lemma-fitting-ideal` (Tag 07Z8), especially its last paragraph; and
`literature/stacks-project/algebra.tex`, `lemma-Schanuel` (Tag 00O3), including
the commuting diagram and explicit shear proof. The node's four-step natural
language proof is included in the theorem docstring: projective lifting,
linearity and both inverse computations, quotient compatibility, and both
kernel-image inclusions.

Edge cases checked before writing:

- If n=0, surjectivity of π forces M=0. Both maps involving F are zero; U
  sends `(0,y)` to `(y,0)` and the inverse sends `(a,0)` to `(0,a)`.
- If m=0 the symmetric computation holds. If both ranks are zero all the
  modules in the displayed equivalence are zero. `Fin 0 → R` is retained.
- If M=0 and the ranks are positive, every pair f,g qualifies. The two inverse
  computations use cancellation alone and still hold for arbitrary f,g.
- The zero ring and its modules cause no failure; no `Nontrivial` assumption
  is imposed. Characteristic two works because only additive cancellation is
  used. No division, domain condition, or equality of ranks is assumed.
- For R=ℤ, n=m=1, π=π'=id, f=g=id, the formulas give U(x,y)=(x,x-y)
  and its stated inverse, confirming the coordinate order and signs.
- Both inverse identities and qU=p were checked algebraically in the stated
  order. The kernel-image equality is equality of ambient submodules, not
  only an isomorphism between their carriers.

Searches actually performed (no exact existing statement found):

- `msearch.py leanfinder`, query: "Two finite free surjections onto a common
  module admit lifts and an explicit common zero stabilization linear
  isomorphism commuting with the quotient maps and mapping the kernels".
  Eight hits included `Module.Finite.exists_free_surjective`,
  `Module.finitePresentation_of_free_of_surjective`, and the three
  `LinearMap.splittingOfFunOnFintypeSurjective` results. These concern one
  surjection or splitting; none states the two lifts and all four properties.
- `msearch.py loogle`, query: `LinearEquiv.skewProd, LinearEquiv.skewSwap`.
  The service returned zero hits for that combined query. The declarations
  themselves were located and read directly in Mathlib.
- `msearch.py grep`, query:
  `schanuel|surjective.*prod.*equiv|equiv.*prod.*surjective`.
  Eighteen hits included ModuleCat split-exact biproduct decompositions and
  `LinearMap.equivProdOfSurjectiveOfIsCompl`. These are ingredients, not this
  two-presentation statement with the prescribed formulas.
- `msearch.py leansearch`, query: "Two surjective maps from finite free
  modules admit a common zero stabilization isomorphism commuting with the
  quotient maps and identifying their kernels". Eight hits included
  `ModuleCon.quotientKerEquivOfSurjective`,
  `LinearMap.quotKerEquivOfSurjective`, `Module.Finite.reprEquiv`, and
  `Module.Flat.exists_factorization_of_comp_eq_zero_of_free`. No exact match.
- Direct `rg` searches for `skewProd|skewSwap` in Mathlib's
  `LinearAlgebra/Prod.lean` found the canonical shear equivalences; these do
  not state the combined assertion. Searches for
  `free_surjections_common_stabilization|zeroStabil|commonStabil|lem-trf-free-surjections-common-stabilization`
  in `lean/WeilConjectures` and `lean/Sheaf` found no declaration of this
  statement. The exact proposed name was also searched in Mathlib and
  `dag/lean_names_upstream.json`, with no hits. The required `grep -rn` for
  the item id in `lean/WeilConjectures` found no hits.
- Direct searches for `stabiliz|Schanuel` in the relevant project algebra
  directories found `WeilConjectures.Algebra.Schanuel` and the row-minor
  invariance module. The full `Module.schanuel` signature and docstring were
  read: it asserts an abstract kernel direct-sum isomorphism for projective
  presentations, not the explicit commuting equivalence asserted here.

Validation: `scompile.py Q73 lem-trf-free-surjections-common-stabilization`
compiled the delivered file both as a sandbox module and under its final
library module name, with no errors or warnings (1.9 s and 1.8 s). Every
universe and variable is explicitly bound. Only the item's `lean` field is
changed in its copied JSON, with the exact source signature. No node fault
or `STATEMENT-DISPUTED` concern remains.

## Second reading by Q73

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
