## Worker report

Repair of the returned immutable head 9352222f71fa. The retained sandbox had only
launcher marker files, so the delivery was rebuilt from the current main node.
It now supplies one statement module,
`Sheaf.RingTheory.GeometricReducednessSeparableScalarRestriction`, with the single
sorry-only theorem `Algebra.forall_isReduced_tensorProduct_iff_of_isSeparable`.
No definitions, proofs, dependency modules, or new nodes are introduced.

The current main node's repaired `proof`, `proof_deps`, `statement`, and all other
non-Lean fields are preserved verbatim. In particular, proof step 1 cites tensor
cancellation for its iterated tensor identification; step 2 constructs the
balanced maps explicitly and does not misuse that cancellation lemma. Its
localization argument uses `zx^n = 0`, then `(zx)^n = 0`, then `zx = 0`.
The module docstring records Tag 0C2Y and the blueprint item; the theorem
docstring contains both repaired proof steps and the nodes used in each.

Clause-by-clause correspondence:

- Fields `k ⊆ k₁`: `(k : Type u) (k₁ : Type v)`, `[Field k] [Field k₁]`,
  and `[Algebra k k₁]`. A field algebra map is injective.
- Separable algebraic extension: `[Algebra.IsSeparable k k₁]`. Its source
  definition requires separable minimal polynomials for every element, which
  already implies algebraicity (`Algebra.IsSeparable.isAlgebraic`). No separate
  finite-degree hypothesis occurs.
- Commutative `k₁`-algebra `A`, with restricted `k`-structure:
  `(A : Type w) [CommRing A] [Algebra k₁ A] [Algebra k A]`
  and `[IsScalarTower k k₁ A]`. The tower enforces compatibility; the two
  algebra structures are not unrelated.
- Condition (1): `∀ (E : Type (max u v w t)) [Field E] [Algebra k E],
  IsReduced (E ⊗[k] A)`.
- Condition (2): the same quantification with `[Algebra k₁ E]` and
  `IsReduced (E ⊗[k₁] A)`.
- Equivalence of the two conditions: the outer `↔`.
- The node puts `A` first, while the requested repair and Stacks proof put `E`
  first. These are the same conditions under `Algebra.TensorProduct.comm`.
- Reduced means every nilpotent is zero: exactly the field `IsReduced.eq_zero`
  of Mathlib's `IsReduced`, read in `Mathlib.Algebra.GroupWithZero.Basic`.
- Tensor multiplication and unit are the existing Mathlib ring structure:
  `Algebra.TensorProduct.tmul_mul_tmul` and `Algebra.TensorProduct.one_def`
  give the node's two formulas, with the factors swapped as just explained.
- The zero algebra is allowed: no `[Nontrivial A]`, domain, or field assumption
  on `A`. No finite-type condition and no finite-dimensionality condition occur.

Universes are explicitly bound as `u v w t`. The extension-field universe is
`max u v w t`, not an independent potentially smaller universe and not just
`u`, `v`, or `w`. The arbitrary additional `t` permits tests in every larger
universe; smaller test fields embed in this common universe by universe lift,
which preserves the ring and algebra structures and reducedness of the tensor
product. There is no silent same-universe assumption on `k`, `k₁`, `A`, or
extension fields. All type and instance binders in the signature are explicit.

Dependency declarations read and used:

- `def-pc-field-extension`: `Algebra`,
  `Mathlib.Algebra.Algebra.Defs`, publicly available through the field and tensor imports.
- `def-weil-pbc-separable-algebraic-extension`: `Algebra.IsSeparable`,
  `Mathlib.FieldTheory.Separable`, public import.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`,
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, publicly available through
  `Mathlib.RingTheory.TensorProduct.Basic`; it is the actual quotient construction.
- Proof import `WeilConjectures.FieldTheory.SeparablyGeneratedTensorReduced`:
  `Algebra.isReduced_tensorProduct_of_isSeparablyGenerated`. Its full current
  source, including its docstring and proof, was read using `scompile.py --source`;
  the older local upstream checkout lacks this module. This import also supplies
  `Algebra.IsSeparablyGenerated` and `Algebra.IsSeparableExtension` from
  `WeilConjectures.FieldTheory.SeparableExtension`, whose current source was read
  using the same wrapper, and the transcendence-basis definitions.
- Proof import `Mathlib.RingTheory.Localization.BaseChange`:
  `IsLocalization.tensor`, with its full signature read.
- Proof import `Mathlib.RingTheory.TensorProduct.Maps`:
  `Algebra.TensorProduct.cancelBaseChange`, with its full signature, pure-tensor
  formula, and inverse formula read. It is used only for proof step 1.
- The nodes `lem-trf-geometrically-reduced-base-change` and
  `lem-trf-separable-algebraic-diagonal-localization` have neither Lean records
  nor Mathlib matches on the main node snapshot. They are proof prerequisites,
  not notions needed to type this statement. Their future imports are therefore
  omitted, as required for as-yet-unstated proof dependencies.

Source and edge-case checks: read `literature/stacks-project/algebra.tex`,
including the definition of geometric reducedness and Tags 034N, 030U, 0C2X,
and 0C2Y; the tags table confirms 0C2Y's label. The node's blueprint origin is
`sk-i-curve-zero`, through `lem-trf-local-term-locality`; this is a supporting
algebra lemma, not the unit statement. Checked `k₁ = k` (the same tests),
`A = 0` (both tensors zero and reduced), `A = k₁` (separable extension),
a polynomial algebra with arbitrarily many generators, infinite separable
algebraic extensions, and dual numbers over `k₁` (both conditions fail).
Characteristic is unrestricted. Dropping separability would fail for a
nontrivial purely inseparable `k₁/k` with `A = k₁`, so that binder is essential.

Existing-declaration searches, repeated for this repair:

- `msearch.py NY <item> leanfinder` with query
  `geometric reducedness is invariant under restriction of scalars along a separable algebraic field extension`:
  eight hits, including `Algebra.IsGeometricallyReduced.of_injective`,
  `Algebra.IsGeometricallyReduced`, `Algebra.isGeometricallyReduced_iff`, and
  `Algebra.instIsReducedTensorProductOfIsAlgebraicOfIsGeometricallyReduced`;
  none states this scalar-restriction equivalence.
- `msearch.py ... loogle 'Algebra.IsGeometricallyReduced'`: nine hits on the
  algebraic-closure test, injections, finite subalgebras, and algebraic tensor
  extensions. The local Mathlib source was opened in full: its TODO explicitly
  says the all-field-extensions characterization still needs proving. Therefore
  the theorem directly states the requested universal conditions instead of
  silently substituting this different interface.
- `msearch.py ... grep 'geometrically.*reduced.*separable|separable.*geometrically.*reduced|0C2Y'`:
  zero hits.
- `rg` for `IsGeometricallyReduced|geometrically.*reduced|<item>` in the upstream
  `WeilConjectures` tree and shared `lean/Sheaf`: related scheme statements and
  the separability criterion, no exact statement. Searching the upstream names
  table gave no matching scalar-restriction declaration. Searching the chosen
  declaration name and module name in both trees and Mathlib gave zero hits.

The module was compiled alone with the prescribed `scompile.py` wrapper.
Both wrapper checks passed with no diagnostics: sandbox 4.2 seconds and library
file 12.9 seconds. There are no errors or warnings; the only postponed proof is
the one named theorem, whose body is exactly `by sorry`.
No statement correction or STATEMENT-DISPUTED flag is needed.

## Second reading by NY

Author's second pass for the direct-delivery repair; no independent NY worker
was launched, in accordance with the dispatcher instruction. The maintainer
provides the independent reading. This section records the actual rereading of
the main node and the delivered file, not a claim of independent review.

Reopened both signatures and checked fields, algebra structures, separability,
scalar restriction, both universal field tests, and the outer equivalence. The
scalar tower supplies precisely restriction of scalars. `CommRing A` leaves
zero algebras available; no finiteness or characteristic binder was introduced.
The additional universe `t` prevents a fixed base-universe restriction on the
test field. Tensor factor reversal is justified by the canonical ring
isomorphism, and the usual Mathlib tensor structure gives the exact unit and
multiplication formulas. `IsReduced` has exactly the node's nilpotence meaning.

Compared the current node's repaired proof text with the return's defects:
the explicit balanced maps remain in step 2, tensor cancellation is cited only
where its actual signature applies, and localization uses the precise
annihilator computation. The new declaration docstring reproduces these two
steps. Unlike the returned stage-1 head, this packet includes a sorry-only
module, a verbatim Lean signature record, and this report. No non-Lean node
field has been changed, and there are no new or dependency modules to review.
