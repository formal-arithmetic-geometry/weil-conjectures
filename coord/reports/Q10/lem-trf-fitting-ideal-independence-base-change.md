## Worker report

The module `Sheaf.RingTheory.PresentationFittingIdeal` states
`LinearMap.presentationFittingIdeal_independence_baseChange`, with proof `sorry`.
Its three helper definitions construct exactly the ideal and canonical presentations
introduced in this node; their data contain no `sorry`. No statement correction,
new DAG node, or dependency repair is needed.

Hypothesis and clause correspondence:

- The commutative ring is `{R : Type u} [CommRing R]`. The module is
  `{M : Type v} [AddCommGroup M] [Module R M]`; finite generation is
  `[Module.Finite R M]`. Ring and module universes are independently bound.
- The nonnegative integer is `(k : ℕ)`. The finite free source `R^{⊕n}` is
  `Fin n → R`, canonically the finite direct sum; `n : ℕ` includes zero.
- The linear surjection is `(π : (Fin n → R) →ₗ[R] M)` and
  `(hπ : Function.Surjective π)`.
- Its kernel rows are encoded in `presentationFittingIdeal` by
  `A : Matrix (Fin (n-k)) (Fin n) R` and `∀ i, π (A i) = 0`.
  No generating set or finite generation of the kernel is assumed.
- Its minors are `(A.submatrix (fun i ↦ i) c).det`, for every embedding
  `c : Fin (n-k) ↪ Fin n`. These select all distinct columns; allowing their
  permutations changes determinants only by sign and hence leaves the generated
  ideal unchanged. All rows are used because there are exactly `n-k` of them.
  `Ideal.span` forms the generated ideal. The explicit `if n ≤ k then ⊤`
  gives the node's unit-ideal convention, including `n=k` and `n=0`.
- Clause (1) is the first conjunct: every `n' : ℕ`, every linear `π'` of
  that rank, and every proof of its surjectivity give equality of the ideals.
- Clause (2) is the second conjunct: every commutative `A : Type w` and
  every `[Algebra R A]` give surjectivity of `π.baseChangePresentation A`
  and equality of its ideal with
  `Ideal.map (algebraMap R A) (π.presentationFittingIdeal k)`.
  Quantifying over all algebra structures represents every ring homomorphism
  `φ : R →+* A` via `φ.toAlgebra`; no flatness, injectivity, finiteness,
  finite presentation, or nontriviality assumption occurs.
- `baseChangePresentation` is `π.baseChange A` composed with the inverse
  of `TensorProduct.piScalarRight R A A (Fin n)`. Its source is exactly
  `Fin n → A`, and its codomain is `A ⊗[R] M`. This is the recorded
  dependency's order of tensor factors, canonically isomorphic to `M ⊗[R] A`.
  It sends `e_i` to `1 ⊗ π(e_i)`; it is the canonical tensor-induced map.
- The final conjunct explicitly specializes to every `g : R`, with codomain
  `LocalizedModule.Away g M` and coefficient ring `Localization.Away g`.
  `localizePresentationAway` composes the tensor presentation with
  `(IsLocalizedModule.isBaseChange ...).equiv.toLinearMap` for the actual
  `LocalizedModule.mkLinearMap`. It therefore sends a localized coefficient
  times `e_i` to that coefficient times `π(e_i)/1`, and is not an arbitrary
  map to a merely isomorphic module. It is surjective and its ideal is the
  extension by `algebraMap R (Localization.Away g)`. With clause (1), this
  is the presentation-independent ideal of the localized module.

Dependency declarations read and used:

- `def-weil-finitely-generated-module`: `Module.Finite`, from
  `Mathlib.RingTheory.Finiteness.Defs` (definition and full class signature read).
- `def-weil-matrix`, `def-weil-submatrix`: `Matrix`, `Matrix.submatrix`, from
  `Mathlib.LinearAlgebra.Matrix.Defs` (reached through the determinant import).
- `def-weil-pbc-matrix-determinant`: `Matrix.det`, from
  `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`, including `det_apply`.
- `def-weil-pbc-free-module`: `Module.Free`, from
  `Mathlib.LinearAlgebra.FreeModule.Basic`; the finite coordinate module is its
  standard finite-free instance, and the proof plan uses standard basis lifts.
- `def-weil-module-base-change`: `LinearMap.baseChange`, from
  `Mathlib.LinearAlgebra.TensorProduct.Tower`, including its tensor formula.
- `def-weil-pbc-module-localization-away`: `LocalizedModule.Away` and
  `LocalizedModule.mkLinearMap`, from
  `Mathlib.Algebra.Module.LocalizedModule.Basic`.
- `def-weil-ring-localization-away`: `Localization.Away`, from
  `Mathlib.GroupTheory.MonoidLocalization.Away`; the ring and algebra instances
  are available through `Mathlib.RingTheory.Localization.BaseChange`.
- Proof dependency `lem-weil-pbc-tensor-right-exact`: Mathlib's
  `LinearMap.lTensor_exact` / `LinearMap.rTensor_exact`, in
  `Mathlib.LinearAlgebra.TensorProduct.RightExactness`, imported non-publicly.
- Proof dependency `def-weil-pbc-module-tensor-product`: `TensorProduct`,
  `TensorProduct.mk` and its universal construction in Mathlib's tensor modules.
- Proof dependency `lem-weil-pbc-localization-module-tensor`:
  `IsLocalizedModule.isBaseChange`, from
  `Mathlib.RingTheory.Localization.BaseChange`, and `IsBaseChange.equiv`,
  `IsBaseChange.equiv_tmul`, from `Mathlib.RingTheory.IsTensorProduct`.
- `TensorProduct.piScalarRight`, from `Mathlib.LinearAlgebra.TensorProduct.Pi`,
  supplies the canonical finite-coordinate identification (signature and docstring read).
- Proof dependency `lem-trf-fitting-ideal-minor-inclusions` has no recorded
  Lean declaration or Mathlib match on the base; no module exists to import.
  It is cited step by step in the proof docstring for stage 3. The present
  statement does not need a new notion from that proof-only prerequisite.

Source checked: `literature/stacks-project/more-algebra.tex`,
`lemma-fitting-ideal` (07Z8), its kernel-row description and stabilization proof,
and `lemma-fitting-ideal-basics` (07ZA), part (3) and its right-exactness proof.
Stacks writes kernel elements as columns; the node uses their transposes as rows.
The determinants of the corresponding square matrices agree.

Edge cases checked:

- `n=0` forces a surjective target to be zero and gives the unit ideal for every
  `k`; a redundant presentation of zero also has a unit minor when needed.
- `n=k` and `n<k` use the explicit unit-ideal branch; `k=0`, `n>0` uses full
  `n`-minors of arbitrary kernel rows, with no finite-presentation assumption.
- A free rank-one module with its identity presentation has zero zeroth ideal
  and unit first ideal. For `R → R/(a)`, the quotient presentation gives `(a)`
  as its zeroth ideal, and arbitrary further base change maps it to `(φ(a))`.
- Nonflat base change is included: the proof uses the image of the tensor kernel,
  not injectivity. Infinite/non-finitely-generated relation modules are allowed.
- The zero ring is allowed throughout. `g=0` gives the zero localization and
  its unique ideal; `g=1` gives the original presentation up to canonical equivalence.
- All universes `u v w` are explicit, as are all variables; no universe equality
  or nonempty indexing assumption is imposed.

Searches for existing declarations (all performed through the prescribed wrappers):

- LeanFinder: `Fitting ideal generated by minors of kernel rows is independent of
  finite free generators and commutes with base change`. Eight hits, including
  `Algebra.PreSubmersivePresentation.jacobian`, `KaehlerDifferential.ideal_fg`,
  `Ideal.smithCoeffs`, and matrix representation/PID results; no match.
- Loogle: `Module.fittingIdeal, Matrix.minor, LinearMap.baseChange`.
  Zero hits, unknown identifier `Module.fittingIdeal`.
- LeanSearch: `Fitting ideal of a finite module and base change`. Eight hits
  about rank, `Submodule.baseChange`, finite presentations and ring-map finiteness;
  none defines a Fitting ideal or states its presentation independence.
- Mathlib grep wrapper: `fittingIdeal|FittingIdeal|idealOfMinors|minorIdeal`.
  Zero hits across Mathlib.
- `rg` in `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the same notion and proposed declaration names: no implementation found.
  `rg` for this exact item id in `WeilConjectures`: no hits.
- DAG searches found only the assigned lemma and downstream singular-subscheme
  consumers, plus its proof-only matrix-minor lemma; no separate definition node
  already gives this presentation ideal. `tools/blueprint_refs.py search Fitting`
  returned zero blueprint nodes. The helpers elaborate the notions introduced
  by this very statement and remain in its owning module, listed in `lean.declarations`.

Validation: `scompile.py Q10 lem-trf-fitting-ideal-independence-base-change
lean/Sheaf/RingTheory/PresentationFittingIdeal.lean` passed sandbox and library
compilation with no errors or warnings. The only theorem proof is `sorry`.
There is no STATEMENT-DISPUTED issue.

## Second reading by Q10

Author self-check for direct remote delivery; independent mathematics review is
performed by the maintainer. I reread the node and all four declarations together.
The theorem has exactly the ring, finite module, nonnegative index, finite-rank
surjection, arbitrary second presentation, arbitrary scalar extension, and every
principal localization. The unit-ideal branch is explicit. The minors use every
kernel row tuple and every injective column selection; no finite generating
relation matrix has been substituted. The scalar extension is the actual Mathlib
`LinearMap.baseChange` transported along the finite-free equivalence, and the
localization targets the recorded `LocalizedModule.Away`, not a replacement.
The three conjuncts match independence, surjectivity/base-change equality, and
the localization consequence. The extra surjectivity conclusion in the last
conjunct is precisely the localized instance of the surjectivity in clause (2).
During compilation, unqualified `id` in the submatrix expression resolved to
`LinearMap.id`; I replaced it with the explicit identity lambda. The final file
compiles cleanly. No mathematical statement change was made.
