## Worker report

The module `Sheaf.RingTheory.GeometricReducednessLocalBaseChange` states
`Algebra.isReduced_localization_tensorProduct_iff`, with `sorry` as its entire proof.
It states precisely the affine local-ring equivalence of Stacks Varieties Tag 0384,
using Tag 035W to express geometric reducedness at a point by its local ring.
The local source `literature/stacks-project/varieties.tex`, lines 354–397 and 491–529,
was opened, including both proofs. No definitions, helper nodes, dependency modules,
or statement corrections are needed. Only the item's `lean` field changes.
There is no repair-note file for this item.

The correspondence with every hypothesis and clause is as follows.

| Node text | Lean rendering |
| --- | --- |
| A field k | `(k : Type u) [Field k]` |
| A field extension L/k | `(L : Type v) [Field L] [Algebra k L]`; the map is `algebraMap k L` |
| A commutative k-algebra R | `(R : Type w) [CommRing R] [Algebra k R]` |
| S = R tensor_k L, with the specified multiplication | `R ⊗[k] L`, with Mathlib's tensor-product commutative ring; `Algebra.TensorProduct.tmul_mul_tmul` gives `(r ⊗ a) * (s ⊗ b) = (r*s) ⊗ (a*b)` |
| A prime ideal q of S | `(q : Ideal (R ⊗[k] L)) [q.IsPrime]` |
| p consists of the r with r tensor 1 in q | `q.comap (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] L).toRingHom`; `includeLeft` sends `r` to `r ⊗ 1` |
| A = R_p | `Localization.AtPrime` of that exact comap ideal; primality follows from Mathlib's `Ideal.IsPrime.comap` instance |
| B = S_q | `Localization.AtPrime q` |
| Every field extension E/k | `∀ (E : Type (max u v w t)) [Field E] [Algebra k E]` |
| A tensor_k E is reduced | `IsReduced (Localization.AtPrime (q.comap ...) ⊗[k] E)` |
| Equivalent to condition (2) | The outer `↔` |
| Every field extension H/L | `∀ (H : Type (max u v w t)) [Field H] [Algebra L H]` |
| B tensor_L H is reduced | `IsReduced (Localization.AtPrime q ⊗[L] H)` under the explicitly supplied canonical right-factor L-action |
| Reduced means every nilpotent is zero | Mathlib's `IsReduced.eq_zero : ∀ x, IsNilpotent x → x = 0` |
| No finite type, Noetherian, algebraicity, or closed-point assumption | None of these appears among the binders or in either extension-field quantifier |

The upstairs L-action is important: `Algebra.TensorProduct.rightAlgebra` is not a
global instance in Mathlib because it would conflict with the left action when the
factors coincide. The signature explicitly applies the instance-parameterized
predicate to this particular canonical action, through `@_root_.id`. Beta reduction
therefore supplies the action `l ↦ 1 ⊗ l`, inherited by `Localization.AtPrime q`.
There is no arbitrary action hypothesis, file-local instance, private definition,
`let`, or hidden proof in the signature. The lambda and identity application are
ordinary transparent function applications. In namespace `Algebra`, the root-qualified
identity is necessary to avoid resolving `id` as the algebra homomorphism constructor.

All universes and variables are explicitly bound and `autoImplicit` is false.
The independent universes `u`, `v`, `w` allow different sizes for k, L, and R.
The extension-field universe is their maximum with an arbitrary further universe `t`.
Thus neither test condition can be vacuous because its test-field universe is below
its base field. Identity extensions and algebraic closures can be lifted to that
universe; arbitrary larger field sizes are covered by enlarging `t`. The same test
universe is used on both sides.

Dependency declarations read and used:

- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra`, with fields
  `algebraMap`, `commutes'`, and `smul_def'`. Applied to fields, this is exactly the
  recorded extension interface, with no injectivity assumption added.
- `def-weil-pbc-module-tensor-product`: its Mathlib match `TensorProduct` from
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, reexported through the public import
  `Mathlib.RingTheory.TensorProduct.Basic`. The quotient definition, `TensorProduct.mk`,
  `TensorProduct.lift`, uniqueness, and `LinearMap.rTensor` were opened. The ring
  structure and its pure-tensor multiplication come from the latter public import.
  This dependency is a Mathlib leaf with no `lean` record, which needs no repair.
- `def-weil-pbc-localization-at-prime`: `Mathlib.RingTheory.Localization.AtPrime.Basic`,
  `Localization.AtPrime`, the quotient localization at `p.primeCompl`. Its docstring
  and full definition were opened. The additional recorded residue-field and fibre
  interfaces `Ideal.ResidueField` and `Ideal.Fiber` were also read, but are not used
  by this statement.

Every already-stated proof dependency is imported without `public`, except the
localization definition already imported publicly: `Sheaf.FieldTheory.CommonExtensionFields`
(`Field.exists_common_extension`), `Sheaf.RingTheory.PowerGeneratedSpectrumHomeomorphism`
(`AlgebraicGeometry.universally_isHomeomorph_specMap_of_power_generated`),
`Mathlib.FieldTheory.PurelyInseparable.Basic`,
`Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`,
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`,
`Mathlib.RingTheory.RingHom.Flat`, `Mathlib.RingTheory.Localization.BaseChange`,
and `Mathlib.RingTheory.TensorProduct.Maps`. These supply the recorded faithful
flatness, spectrum surjectivity, tensor injectivity, flat-local comparison,
localization base change, and tensor cancellation interfaces.
`lem-trf-geometric-reducedness-finite-inseparable-test` has no recorded Lean
or Mathlib declaration in the read DAG, so there is no module to import yet.
It is only a proof dependency; no missing notion is needed to state this item.
The theorem docstring retains all eight natural-language proof steps, naming the
nodes they use, including the final finite-inseparable test.

Edge cases checked mathematically before writing:

- Identity extension L=k: both local rings identify, so the equivalence includes
  this case and does not require a proper extension.
- Arbitrary nonmaximal q: only `q.IsPrime` is assumed. There is no closed-point
  hypothesis and R may be non-Noetherian and of arbitrary dimension.
- Zero ring R: its tensor product is zero and has no prime q, so the lack of any
  such input is the same in the node and Lean, rather than an added nontriviality
  assumption on R.
- Nonreduced example R=k[ε]/(ε²): the surviving nilpotent in the localized ring
  violates both conditions. No unconditional reducedness was accidentally asserted.
- Characteristic p: inseparable extensions such as adjoining a pth root over
  F_p(t) remain allowed; there is no perfectness or separability assumption.
- Characteristic zero: the finite purely inseparable test in the proof reduces to
  the identity extension, without excluding characteristic zero from the statement.
- Different universes and arbitrary field extensions: no equality of universes,
  finiteness, algebraicity, or finite-generation constraint is imposed. In particular
  the extension quantifiers include nonalgebraic fields, unlike the algebraic-only
  instance presently provided by the pinned geometrically-reduced Mathlib API.

Searches made (all candidate signatures were checked against the pinned source):

- `msearch.py leanfinder`: “Geometric reducedness of local rings at corresponding
  primes is invariant under arbitrary extension of the base field”. Eight hits,
  mainly `Algebra.IsGeometricallyReduced`, its injective descent lemma, and
  `Algebra.FormallyUnramified.isReduced_of_field`; none states the local base-field
  equivalence.
- `msearch.py loogle`: `Algebra.IsGeometricallyReduced`. Nine hits; no localization
  equivalence. `isGeometricallyReduced_field_iff` tests an algebraic closure,
  `of_injective` keeps the same base field, and the scalar-extension reducedness
  instance assumes `Algebra.IsAlgebraic`.
- `msearch.py grep`, subdirectory `RingTheory`:
  `geometricallyReduced.*[Ll]ocal|isGeometricallyReduced.*(iff|[Bb]ase)|geometrically.*upstairs`.
  Five hits, all in `Mathlib/RingTheory/Nilpotent/GeometricallyReduced.lean`, with
  no equivalent statement. That entire source file was read; its TODO explicitly
  records the missing arbitrary-field-extension comparison with the Stacks definition.
- `msearch.py leansearch`: “A localization of a scalar extended algebra at a prime
  is geometrically reduced over the extension field if and only if the original
  local ring is geometrically reduced”. Eight hits; algebraic-closure criteria,
  generic localizations and reduced-localization preservation, with no exact match.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for
  `geometricallyReduced|isGeometricallyReduced|lem-trf-geometric-reducedness-local-base-change`:
  scheme-level smoothness and geometric-integrality results, but no local-ring
  field-extension equivalence. The exact blueprint id has no upstream declaration.
- Exact proposed name `isReduced_localization_tensorProduct_iff` searched in Mathlib,
  upstream `WeilConjectures`, project `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  no collision.

The only postponed proof is the named theorem of this node. No statement dispute
or source discrepancy was found. No second worker was started: the dispatcher brief
requires direct delivery, with independent review by the maintainer.

Validation: `scompile.py NB lem-trf-geometric-reducedness-local-base-change`
compiled the delivered module cleanly in both sandbox and library contexts.
`deliver2.py NB lem-trf-geometric-reducedness-local-base-change --no-push`
returned OK: server preflight passed and the file compiled without warnings.
The delivered Lean file has a maximum line width of 93 characters, and the node
signature is copied verbatim from its theorem header. A source comparison confirms
that the only changed node field is `lean`.

## Second reading by NB

Independent reading (maintainer reviewer, 2026-10-18). I read it with the node, Stacks varieties.tex
Tags 035W (l. 354–397) and 0384 (l. 491–529), the three stmt_deps records and the delivered file
open side by side. It replaces the delivered placeholder.

Node statement as a list, with its Lean rendering and verdict:

| Node clause | Lean | Verdict |
| --- | --- | --- |
| k a field | `(k : Type u) [Field k]` | ok |
| L/k a field extension (def-pc-field-extension) | `(L : Type v) [Field L] [Algebra k L]` | ok, the recorded Mathlib convention; no injectivity assumed (it is automatic) |
| R a commutative k-algebra | `(R : Type w) [CommRing R] [Algebra k R]` | ok |
| S = R ⊗_k L with (r⊗a)(s⊗b) = rs⊗ab | `R ⊗[k] L` with Mathlib's ring structure (`Algebra.TensorProduct.tmul_mul_tmul`) | ok |
| q ⊂ S prime | `(q : Ideal (R ⊗[k] L)) [q.IsPrime]` | ok |
| p = {r : r⊗1 ∈ q} | `q.comap (includeLeft).toRingHom`; a probe checks `r ∈ p ↔ r ⊗ₜ 1 ∈ q` by `Iff.rfl` | ok |
| A = R_p, B = S_q | `Localization.AtPrime (…comap…)`, `Localization.AtPrime q` | ok |
| (1) for every E/k, A ⊗_k E reduced | `∀ (E : Type (max u v w t)) [Field E] [Algebra k E], IsReduced (… ⊗[k] E)` | ok (universe: see below) |
| (2) for every H/L, B ⊗_L H reduced | `∀ (H : Type (max u v w t)) [Field H] [Algebra L H], IsReduced (Localization.AtPrime q ⊗[L] H)` | ok |
| L-structure on S, B: l ↦ 1⊗l | `@_root_.id … (fun [Algebra L (R ⊗[k] L)] ↦ …) rightAlgebra`. A probe shows it is definitionally the `letI := rightAlgebra` form, and that `algebraMap L B l = (1 ⊗ₜ l)/1`, both by `rfl` | ok |
| equivalence | outer `↔` | ok |
| reduced = nilpotents vanish | Mathlib `IsReduced` | ok |
| no finite type / Noetherian / algebraic / closed-point hypothesis | none among the binders | ok |

Universes: the test fields of both sides live in `max u v w t`, with `t` free. For every `t` the
iff is the node's statement. Forward, (1) is applied to H itself, which lies in the same universe.
Reverse, the proof's fields E'' (finite over k) and the common extension F (a quotient of
L ⊗_k E'') have size at most max u v, so they lift to the test universe. The 030V test then gives
every E. Neither side is vacuous, and no universe equality is imposed.

Edge cases: L = k (both local rings agree); q is any prime, not necessarily maximal; R = 0 has no
prime q, the same in the node and in Lean; characteristic 0 and characteristic p, with
inseparable E and H allowed; nonalgebraic extensions are allowed on both sides.

Searches: `Algebra.IsGeometricallyReduced` (Mathlib GeometricallyReduced.lean) uses the
algebraic closure and has no local base-field change lemma; the node's explicit quantifier is the
right rendering. rg on the project's lean/Sheaf found no declaration with this content or name.

Gates: one theorem, proof `sorry`; module and theorem docstrings carry Tags 0384/035W and
`(blueprint: lem-trf-geometric-reducedness-local-base-change)`; the 8 proof steps are in the
docstring; `lean.statement` is verbatim the header; only the node's `lean` field changes.
Per-file compile through nt_compile.py: clean, 3.0 s.

Mismatches found: none in the Lean or node. Changed: only this section, which replaces the placeholder.

## Second reading by Q118

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
