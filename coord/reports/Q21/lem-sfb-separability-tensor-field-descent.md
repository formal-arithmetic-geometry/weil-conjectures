## Worker report

Item: `lem-sfb-separability-tensor-field-descent` (Q21, stage 2, 2026-10-24).

The module `Sheaf.FieldTheory.SeparabilityTensorFieldDescent` states
`Algebra.isSeparableExtension_of_isField_tensorProduct`. Its only theorem has
`by sorry` as its whole proof. It introduces no definitions, instances, or auxiliary theorems.
The node changes only in `lean`; no statement correction or dependency repair is needed.

The source read was `literature/stacks-project/algebra.tex`, Definition
`definition-separable-field-extension` (030O), Lemma
`lemma-separable-extension-preserves-reducedness` (030U), and Lemma
`lemma-characterize-separable-field-extensions` (030W). The statement is the
specified descent corollary, not a claim that the corollary is verbatim in 030U/030W.
The six-step proof docstring reproduces the node's characteristic split, common
extension field, finite-coefficient reduction, explicit tensor reassociation,
injective scalar extension, and positive-characteristic separability criterion.

Clause and hypothesis correspondence:

| Node text | Lean rendering |
| --- | --- |
| Fields k, k', F | `(k : Type u) (k' : Type v) (F : Type w)` with `[Field k] [Field k'] [Field F]` |
| Extensions k ⊆ k' and k ⊆ F | `[Algebra k k'] [Algebra k F]`; their structure maps are injective because the source and targets are fields |
| The commutative tensor algebra F tensor_k k' | `F ⊗[k] k'`, with Mathlib's existing `Algebra.TensorProduct.instCommRing` |
| Multiplication (a tensor b)(c tensor d) = ac tensor bd | The canonical ring instance satisfies `Algebra.TensorProduct.tmul_mul_tmul`; no new multiplication is quantified |
| This ring is a field | `(hfield : IsField (F ⊗[k] k'))` is a predicate on that canonical ring |
| Its field structure for the separability predicate | `hfield.toField`, supplied explicitly to `@IsSeparableExtension`; `IsField.toField` retains the original ring operations and supplies inverses |
| It is an extension of the right factor k' | Explicit `Algebra.TensorProduct.rightAlgebra (R := k) (A := F) (B := k')`, whose structure map sends b to 1 tensor b |
| It is separable over k' in the possibly transcendental sense | `hsep : @IsSeparableExtension k' (F ⊗[k] k') _ hfield.toField (...)` uses the dependency's exact definition, quantifying over every finitely generated intermediate field |
| F/k is separable in that same sense | `IsSeparableExtension k F` |
| No algebraicity or finite generation assumed | Neither `Algebra.IsAlgebraic`, `Algebra.IsSeparable`, `Module.Finite`, `Algebra.EssFiniteType` nor a finite-generation hypothesis is present |

The explicit `@` application avoids a file-local instance or an arbitrary field
structure on the tensor's underlying type. It also fixes the scalar action to the
right-factor map rather than an independently quantified algebra structure.
All type variables and universes are explicit, and `autoImplicit` is false.
No independent small test-field universe occurs in this statement.

Dependency declarations read and used:

- `def-pc-field-extension`: `Algebra` in `Mathlib.Algebra.Algebra.Defs`.
  The definition takes a ring homomorphism as `algebraMap`, exactly as its record says.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` and `TensorProduct.mk`
  in `Mathlib.LinearAlgebra.TensorProduct.Defs`; `TensorProduct.lift`, `lift.tmul`
  and `ext'` in `.Basic`; `LinearMap.rTensor`, `rTensor_tmul` and `rTensorHom`
  in `.Map`. The ring structure and right scalar action used here are in
  `Mathlib.RingTheory.TensorProduct.Basic`.
- `def-weil-pbc-separable-field-extension`: `Algebra.IsSeparablyGenerated` and
  `Algebra.IsSeparableExtension` in `WeilConjectures.FieldTheory.SeparableExtension`.
  The latter is literally `∀ E : IntermediateField k K, E.FG → IsSeparablyGenerated k E`.
  The former is a transcendence basis followed by `Algebra.IsSeparable` over its adjoin.

Every stated proof dependency is imported, without `public` for the proof-only modules:

- `lem-weil-pbc-char-zero-field-extension-separable`:
  `exists_isTranscendenceBasis_and_isSeparable_of_perfectField`,
  `Mathlib.FieldTheory.SeparablyGenerated` (the recorded Mathlib match).
- `lem-weil-common-extension-fields`: `Field.exists_common_extension`,
  `WeilConjectures.FieldTheory.CommonExtensionFields`.
- `lem-weil-pbc-separably-generated-tensor-reduced`:
  `Algebra.isReduced_tensorProduct_of_isSeparablyGenerated`,
  `WeilConjectures.FieldTheory.SeparablyGeneratedTensorReduced`.
- `lem-weil-pbc-module-over-field-flat`: `Module.Free.of_divisionRing`,
  `Mathlib.LinearAlgebra.Basis.VectorSpace`, and `Module.Flat.of_free`,
  `Mathlib.RingTheory.Flat.Basic`.
- `lem-trf-flat-tensor-preserves-injection`:
  `Module.Flat.lTensor_preserves_injective_linearMap`, `Mathlib.RingTheory.Flat.Basic`.
- `lem-weil-pbc-algebra-tensor-pushout-universal-property`:
  `Algebra.TensorProduct.instCommRing`, `tmul_mul_tmul`, `includeLeft`, `includeRight`,
  and `ext` in `Mathlib.RingTheory.TensorProduct.Basic`; `productMap` and
  `productMap_apply_tmul` in `Mathlib.RingTheory.TensorProduct.Maps`.
- `lem-weil-pbc-geometrically-reduced-extension-separable`:
  `Algebra.isSeparableExtension_of_forall_isReduced_tensorProduct`,
  `WeilConjectures.FieldTheory.GeometricallyReducedExtensionSeparable`.

The tensor-product and separability definitions are already public statement imports.
`Mathlib.Algebra.Field.IsField` supplies the predicate and the canonical field promotion.
No dependency module is missing or unusable, and no import is omitted for a cycle.

Edge cases checked before writing:

- `k' = k`: the tensor ring is canonically F and the assertion reduces to separability
  implying itself; the explicitly chosen right action remains the base-field action.
- `F = k`: the tensor ring is canonically k', and the conclusion is separability
  of the identity extension.
- `F = k(t)` and `k' = k`: the tensor is a field and the extension is separable in
  the transcendental sense. No algebraic-separability assumption excludes this case.
- In characteristic p, take `k = F_p(s)` and `F = k(s^(1/p))`. With `k' = k`,
  fieldness holds but the separability hypothesis fails. With `k' = F`, the tensor
  has a nonzero nilpotent and fieldness fails. The statement does not incorrectly
  deduce separability of this inseparable extension.
- Characteristic zero and every prime characteristic are included; no `CharP` or
  `CharZero` binder restricts the theorem. No finiteness or algebraicity condition
  restricts either extension. Independent universes u, v, w cover all field sizes.
- `IsField` includes nontriviality, as required for a field; no zero-ring case
  accidentally meets the hypothesis. The multiplication is fixed before `hfield`.

Searches for an existing statement, all through the prescribed wrapper where applicable:

- `msearch.py ... leanfinder`: "Separability for possibly transcendental field
  extensions descends if tensor product with an extension field is a separable field".
  Eight hits: `Algebra.IsSeparable.trans`, `IsSeparable.tower_bot`,
  `Algebra.isSeparable_tower_bot_of_isSeparable`,
  `Algebra.isSeparable_tower_top_of_isSeparable`, `IsSeparable.tower_top`,
  `IsSeparable.of_algebra_isSeparable_of_isSeparable`, `Algebra.IsSeparable.of_algHom`,
  and `IntermediateField.isSeparable_tower_top`. These concern algebraic separability
  or separability of elements, not the arbitrary-extension predicate required here.
- `msearch.py ... loogle`: `Algebra.IsSeparable, TensorProduct`. Zero hits.
- `msearch.py ... grep`: `IsSeparableExtension|[Ss]eparab.*[Dd]escen` in `FieldTheory`.
  Zero Mathlib hits.
- `msearch.py ... leansearch`: "If F tensor over k with kprime is a field separable
  over kprime then F is separable over k, for arbitrary possibly transcendental
  extensions". Eight hits involving the algebraic-separability tower results,
  `IsSeparable`, and `Field.sepDegree`; none states this node.
- `rg` in `lean/WeilConjectures/FieldTheory` and `lean/Sheaf/FieldTheory` for
  `IsSeparableExtension`, separability/descent, and separability/tensor patterns found
  the definitions and tensor reducedness/finite or algebraic special cases, but no
  arbitrary tensor-field descent statement. In particular the geometric-reducedness
  criterion has a reducedness-for-every-extension hypothesis, not this hypothesis.
- `grep -rn "lem-sfb-separability-tensor-field-descent" lean/WeilConjectures`
  found no attachment. `rg` for `isSeparableExtension_of_isField_tensorProduct` in
  Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  found no declaration with the proposed name.

Validation: prescribed `scompile.py Q21 lem-sfb-separability-tensor-field-descent`
compiled the delivered file in both sandbox and actual module contexts, each in
1.3 seconds, with no errors or warnings. Dry-run and delivery results follow below.
No node fault or disputed statement was found.

## Second reading by Q21

This is a separate rereading by the same worker; the maintainer supplies the independent
review, as specified by the dispatcher brief. No second agent was started.

Reread the node's statement and the final Lean signature together. Both extension
maps are exactly the two `Algebra k ...` instances. Checked that `IsField` is applied
before any field promotion, so its multiplication is the canonical pure-tensor
multiplication. Checked the two explicit arguments of `@IsSeparableExtension`:
`hfield.toField` preserves this ring and `rightAlgebra` fixes b ↦ 1 tensor b.
Unfolded the recorded separability definition while reading it: both hypothesis
and conclusion quantify over every FG intermediate field, using a transcendence
basis and algebraic separability only in the residual extension. Neither side
silently becomes Mathlib's algebraic `Algebra.IsSeparable`. Checked that the three
field universes are independent and no finiteness or characteristic restriction
was introduced. The source, proof docstring, dependency modules, and the node's
`lean.statement` were also reread. No mismatch was found, so no correction was made.

Delivery dry run: `deliver2.py Q21 lem-sfb-separability-tensor-field-descent --no-push`
reported `OK (dry run): commit 231bc9ce454 passes the preflight and compiles; nothing pushed`.
A comparison of parsed base and sandbox node records confirms `lean` is the only
changed field; every Lean source line is at most 100 characters.
