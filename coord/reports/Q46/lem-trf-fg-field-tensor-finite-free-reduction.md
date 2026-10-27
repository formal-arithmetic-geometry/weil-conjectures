## Worker report

The module `Sheaf.FieldTheory.FgFieldTensorFiniteFreeReduction` states
`Algebra.exists_finiteFree_tensorProduct_reduction`, with `sorry` as its only proof.
It introduces no definitions. Source read: `literature/stacks-project/algebra.tex`,
Tag 045M, `lemma-tensor-fields-CM`, lines 47266–47293, especially the finite free
map from the rational-function subfield tensor L to K tensor L in the proof.
The node's four proof steps are transcribed into the declaration docstring.
The node is changed only in `lean`; no statement correction or extra nodes are needed.

The statement correspondence is as follows.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| k is a field | `(k : Type u) [Field k]` |
| K/k and L/k are field extensions | `(K : Type v) (L : Type w) [Field K] [Field L] [Algebra k K] [Algebra k L]` |
| K is generated as a field by finitely many elements | `(hfg : (⊤ : IntermediateField k K).FG)`; `FG` means a finite set whose intermediate-field adjoin is top, not finite generation as an algebra |
| There is a finite list t of length r, with r nonnegative | `∃ (r : ℕ) (t : Fin r → K)` |
| t is a transcendence basis | `IsTranscendenceBasis k t` |
| F is the subfield k(t) of K | `∃ F : IntermediateField k K, F = IntermediateField.adjoin k (Set.range t) ∧ ...` |
| Positive integer d | `∃ d : ℕ, 1 ≤ d ∧ ...` |
| F-basis e_1,...,e_d of K | `∃ e : Module.Basis (Fin d) F K, ...` |
| A and T have algebra tensor multiplication | `F ⊗[k] L` and `K ⊗[k] L` with Mathlib's commutative ring structures |
| Give T the A-algebra structure f tensor l maps to f tensor l | The existential `Algebra (F ⊗[k] L) (K ⊗[k] L)` is constrained by `∀ (f : F) (l : L), algebraMap ... (f ⊗ₜ[k] l) = (f : K) ⊗ₜ[k] l` |
| A tensor_F K to T is an A-algebra isomorphism with the given formula | `∃ α : ((F ⊗[k] L) ⊗[F] K) ≃ₐ[F ⊗[k] L] (K ⊗[k] L), ∀ f l z, α ((f ⊗ₜ[k] l) ⊗ₜ[F] z) = ((f : K) * z) ⊗ₜ[k] l` |
| A^d to T is an A-linear isomorphism with the given coordinate formula | `∃ β : (Fin d → F ⊗[k] L) ≃ₗ[F ⊗[k] L] (K ⊗[k] L), ∀ c, β c = ∑ i, c i • (e i ⊗ₜ[k] (1 : L))` |
| T is finite free over A | `Module.Free (F ⊗[k] L) (K ⊗[k] L) ∧ Module.Finite (F ⊗[k] L) (K ⊗[k] L)` |
| A to T is flat | `(algebraMap (F ⊗[k] L) (K ⊗[k] L)).Flat` |
| A to T is integral | `(algebraMap (F ⊗[k] L) (K ⊗[k] L)).IsIntegral` |
| No separability hypothesis | No `IsSeparable`, perfectness, or characteristic restriction occurs |

The existential algebra structure is part of the conclusion, not an extra input
hypothesis. Its formula specifies the canonical tensor map on every pure tensor;
additivity and the pure-tensor generation of the tensor product determine it
uniquely. It therefore does not substitute an arbitrary algebra map. The same
structure supplies all subsequent scalar actions. The formula for alpha determines
its map on tensor generators, and the formula for beta determines it on every
coordinate vector. No merely abstract isomorphism replaces either required map.
`Fin d` indexes a d-element list from 0 rather than from 1, with no mathematical change.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`.
- `def-weil-pbc-transcendence-basis`: `IsTranscendenceBasis`,
  `Mathlib.RingTheory.AlgebraicIndependent.Defs`. Its maximal-independent definition
  is exactly the node's transcendence-basis notion by the recorded Mathlib match.
- `def-weil-pbc-free-module`: `Module.Free`,
  `Mathlib.LinearAlgebra.FreeModule.Basic`, and `Module.Basis`,
  `Mathlib.LinearAlgebra.Basis.Defs`.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`,
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, with `TensorProduct.tmul` and the
  algebra multiplication in `Mathlib.RingTheory.TensorProduct.Basic`.
- `def-weil-pbc-flat-ring-map`: `RingHom.Flat`,
  `Mathlib.RingTheory.RingHom.Flat`, defined using `Module.Flat`.
- `def-weil-pbc-integral-closure`: `IsIntegral` and `integralClosure`,
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`; the statement uses
  `RingHom.IsIntegral` from its public import
  `Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs`, which is elementwise
  integrality for precisely the displayed algebra map.

The public imports expose the recorded notions through these modules. All proof
prerequisites are Mathlib leaves. Their modules are imported without `public` when
needed only in the proof: `Mathlib.FieldTheory.FinTrdeg`
(`exists_finset_isTranscendenceBasis`),
`Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`
(`IntermediateField.finiteDimensional_adjoin`),
`Mathlib.LinearAlgebra.TensorProduct.Basis` (`Module.Basis.baseChange` and
`Module.Basis.baseChange_apply`), and `Mathlib.Algebra.Module.FinitePresentation`
(`Module.finitePresentation_of_projective`). The flatness ingredient
`Module.Flat.of_free` and finite-integrality ingredient
`Algebra.IsIntegral.of_finite` are already in the public imports. Their signatures
and relevant docstrings were read in the pinned Mathlib source. There are no
unstated or unusable dependencies and no omitted proof imports.

Edge cases checked before writing and again after compilation:

- K=k permits r=0, F the bottom intermediate field, and d=1; no nonempty
  transcendence-basis assumption occurs.
- A finite algebraic extension also permits r=0 and d its positive field degree.
  Inseparable extensions in characteristic p are included; no separability is used
  by the tensor equivalence or free-module base change.
- A purely transcendental finitely generated extension permits F=K and d=1.
- L=k and arbitrary larger extensions L are both included.
- The empty basis of K over F is correctly excluded by `1 ≤ d`, since K is a
  field and nonzero. The conclusion never permits a rank-zero field extension.
- k, K, and L have independent explicit universes u, v, and w. Finite indexing is
  sufficient and excludes no finite family; the intermediate subfield has K's
  universe and tensor products use Mathlib's universe maxima.

Searches performed (2026-10-24):

- `msearch.py ... leanfinder` with query “A finitely generated field extension is
  finite over a rational function subfield, and tensoring with another field gives
  a finite free algebra with the base changed basis”: 8 hits, including
  `functionField_iff`, `FunctionField`, `Algebra.EssFiniteType.baseChange`, and
  `IntermediateField.FG.of_restrictScalars`; no exact assembled statement.
- `msearch.py ... leansearch` with query “A finitely generated field extension has
  a finite transcendence basis over which it is finite dimensional and tensor base
  change is finite free”: 8 hits, including
  `IntermediateField.finite_of_fg_of_isAlgebraic`, `IsTranscendenceBasis`, and
  `IntermediateField.FG`; only ingredients, not the two specified isomorphisms.
- `msearch.py ... loogle 'Algebra.TensorProduct, AlgEquiv'`: 0 hits and the service
  reported unknown identifier `Algebra.TensorProduct` (a namespace, not a
  declaration); this query did not establish absence.
- `msearch.py ... grep 'cancelBaseChange|leftAlgebra|baseChange.*[Aa]lgebra'
  RingTheory/TensorProduct`: 13 hits, including
  `Algebra.TensorProduct.cancelBaseChange` and `leftAlgebra`. These supply generic
  tensor infrastructure, not the finite-basis existence and full stated package.
- `rg` in Mathlib's tensor-product sources read `map`, `map_tmul`, `leftAlgebra`,
  `cancelBaseChange`, and the module tensor action. Searches in the project's
  `lean/WeilConjectures` and `lean/Sheaf` for `TensorProduct.*toAlgebra`,
  `tensorProductAlgebra`, and intermediate-field tensor maps found existing
  canonical tensor-map infrastructure, reused through Mathlib's tensor and
  algebra structures rather than copied.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for
  `fgField|finiteFreeReduction|fg_field_tensor|lem-trf-fg-field-tensor-finite-free-reduction`
  found no matching declaration; the required item-id search in
  `lean/WeilConjectures` likewise found none. Searches for finite/free tensor and
  base-change basis terms in both FieldTheory directories found neighboring
  separability/reducedness and tensor nontriviality results, not this statement.

Validation: `scompile.py Q46 lem-trf-fg-field-tensor-finite-free-reduction` compiled
this file in both sandbox and library module mode on the server, cleanly (3.3 s and
3.5 s). Every variable and universe is explicit. The only theorem proof is `sorry`.
There is no `STATEMENT-DISPUTED` finding.

## Second reading by Q46

This is a second pass by the delivering worker; the maintainer supplies the
independent review under the dispatcher's brief. I reopened the node and the
completed Lean statement. The field-generation hypothesis is `.FG` on the top
intermediate field, so it includes positive transcendence degree. The two finite
lists are indexed separately by `Fin r` and `Fin d`, with only d required positive.
The intermediate-field equality is to the field adjoin, not the algebra adjoin.
The A-action is fixed on every f tensor l, and both alpha and beta use that same
existential structure. Alpha is an A-algebra equivalence and has the exact
multiplication-by-f formula; beta is an A-linear equivalence and has the exact
finite-sum formula. The final conjunction contains both finite and free, then
flatness and integrality for the same algebra map. There is no separability
restriction, no choice-based definition, and no weaker replacement of either
map. This pass found no mismatch and required no changes.
