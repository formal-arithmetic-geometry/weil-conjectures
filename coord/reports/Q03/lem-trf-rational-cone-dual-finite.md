## Worker report

`Sheaf.TraceFormula.RationalConeDualFinite` states `Weil.rationalConeDualFinite`, the finite
rational half-space description of a finitely generated cone. Its sole proof is `by sorry`.
No definition, helper theorem, dependency module, new node, or statement correction is needed.

The node and Lean match hypothesis by hypothesis and clause by clause:

- The ambient rational vector space is `{V : Type u} [AddCommGroup V] [Module ℚ V]`, with
  explicitly declared `universe u`. The scalar field is exactly `ℚ`, not an arbitrary field.
- Finite dimension is `[FiniteDimensional ℚ V]`.
- The arbitrary finite generator list is `(m : ℕ) (v : Fin m → V)`. There is no positivity
  assumption on `m`, no independence or spanning assumption, and no pointedness assumption.
- Membership in the specified cone is
  `∃ q : Fin m → ℚ, (∀ j : Fin m, 0 ≤ q j) ∧ (∑ j : Fin m, q j • v j) = x`.
  Rational coefficients with nonnegativity proofs give precisely nonnegative rationals;
  neither negative coefficients nor real coefficients are admitted.
- The finite family of rational linear forms is
  `∃ s : ℕ, ∃ forms : Fin s → V →ₗ[ℚ] ℚ`, including `s = 0`.
- Equality of the two subsets is rendered pointwise by `∀ x : V, ... ↔ ...`.
  The right side is exactly `∀ i : Fin s, 0 ≤ forms i x`, so both inclusions are asserted.
  `m` and `v` precede this existential family; `x` follows it, so the family works for every
  vector simultaneously.

Both statement dependencies are Mathlib leaves with no project `lean` record required.
`def-weil-field` records `Field`; I read its signature and docstring in
`Mathlib.Algebra.Field.Defs`: it extends `CommRing` and `DivisionRing` and supplies inverses
for nonzero elements. The fixed rational field is provided by
`Mathlib.Algebra.Order.Field.Rat`, publicly imported to supply the ordered rational scalars.
`def-weil-finite-dimensional-subspace` records `FiniteDimensional`; I read its signature and
docstring in `Mathlib.LinearAlgebra.FiniteDimensional.Defs`, publicly imported here. It is
`Module.Finite`, whose `fg_top` field says the whole vector space is finitely generated.
This is precisely the finite spanning-family notion in the node. The only proof dependency
is this same Mathlib leaf, already imported. The declaration uses Mathlib's `LinearMap`,
finite sums, rational order, and scalar multiplication directly, with no private copies.

Edge cases were checked before revising the module. For `m = 0` the empty sum is zero,
so the cone is `{0}`; signed coordinate forms describe it in finite dimension. For `s = 0`
the right side is vacuous and describes the whole ambient space. For `V = 0` this permits
an empty form family for every generator list. Zero/repeated generators change no cone.
For a nonspanning line in `ℚ²`, the two signed transverse coordinate forms retain its
codimension. A half-plane permits lineality; generators of both coordinate signs permit the
whole plane and its empty form family. These cases require no extra Lean hypotheses.

Searches actually run for this repair (under this Q03/item key, logged in `searches.jsonl`):

- `msearch.py leanfinder`: “finitely generated cone over the rationals is the intersection
  of finitely many rational linear halfspaces”. Eight hits included `PointedCone.span`,
  `PointedCone.mem_span_set`, generating/reproducing cones and the standard simplex, but no
  finite rational half-space existence theorem.
- `msearch.py loogle`: `PointedCone.DualFG`. Twelve hits gave the H-cone definition and its
  API, including `DualFG.dual_of_fg`, `exists_fg_dual`, and double-dual identities under an
  existing `DualFG` hypothesis. I read `Geometry/Convex/Cone/DualFinite.lean` through its end.
  The dual of an FG cone being DualFG does not say the original FG cone is DualFG.
- `msearch.py grep`: `polyhedr|Minkowski|Fourier|Motzkin`, restricted to
  `Geometry/Convex/Cone`. Two hits were documentation in `DualFinite.lean` mentioning the
  Minkowski-Weyl theorem; the file does not prove that theorem.
- `msearch.py leansearch`: “finite rational half-space description of a finitely generated
  cone”. Eight hits concerned the `ConvexCone` structure and convex half-space predicates,
  not the required finite family.
- Read-only `rg` in upstream `WeilConjectures/` and project `lean/Sheaf/` for
  `rationalConeDualFinite|rational.*[Cc]one|[Pp]olyhedral|Minkowski|Motzkin|Farkas`, plus the
  exact node-tag `grep` upstream and name search in `dag/lean_names_upstream.json`.
  Upstream and its name table gave no matching declaration. Project hits were the integral
  dual-forms theorem, Gordan's lemma and an unrelated torsion theorem. I opened the complete
  integral dual-forms module: it adds a lattice, pointedness and dual spanning, so it is not
  this unrestricted rational theorem and itself cites this node.

I read ILO Exposé VIII, Remark 3.1.29, printed p. 103, from the local PDF (text conversion
retained in `scratchpad/ilo.txt`). It discusses combinatorial desingularization and points
at Kato 9.6 and Nizioł §4. It does not state or prove this theorem. The module accurately
labels this citation contextual and carries the node's full six-step agent-written proof:
signed coordinates, induction, explicit mixed-sign forms, necessity, a rational maximum
witness for sufficiency, and all degenerate cases. No unread Kato theorem is claimed.
The current blueprint local-term-locality ancestor likewise does not contain a cone theorem;
its historical ancestry and the source limitation are already explicit in the unchanged node.
There is no mathematical statement dispute and no source-based statement change.

## Repair of the returned delivery

The immutable head `0c5168b22793` was a stage-1 artifact without a Lean module or `lean` record.
The independent reviewer supplied a mathematically matching module and record, but its
`fixes/coord/reports/Q03/...md` and full existing-node JSON were rejected by the stage-2
`--apply-fixes` file-layout rules. The sandbox initially retained only its four brief markers;
I recovered the review's supplied module, node and report from its retained `fixes/` directory.

This repair supplies the actual three delivery artifacts in the prescribed worker sandbox:
`lean/Sheaf/TraceFormula/RationalConeDualFinite.lean`,
`dag/nodes/sec-trace-formula/lem-trf-rational-cone-dual-finite.json`, and `report.md`.
`deliver2.py` maps these to the landing paths itself; no malformed reviewer-fix directory
is passed to `--apply-fixes`. The report now has the exact `## Worker report` heading and
an explicit clause audit. The module has the standard public-module header, explicit
universe/index binders, a complete six-step proof docstring, and contextual source wording.
The node was refreshed from current shared main and changes only `lean`, with indent 1,
Unicode preserved and a final newline. `lean.statement` is extracted verbatim from the
actual theorem keyword up to `:=`; its date uses UTC. No inherited stage-1 fields or searches
were changed. This is substantive artifact repair rather than an unchanged re-push.

Compilation, the required dry run, and delivery use only the prescribed wrappers. The final
validation results are recorded below after running them. No independent second reading by
another Q03 worker is claimed; the maintainer's independent review is the review of this repair.

Validation: `scompile.py Q03 lem-trf-rational-cone-dual-finite
lean/Sheaf/TraceFormula/RationalConeDualFinite.lean` passed both sandbox and library compilation
with no errors or warnings. The module has one named theorem and its only proof is `sorry`.

## Second reading by Q03

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
