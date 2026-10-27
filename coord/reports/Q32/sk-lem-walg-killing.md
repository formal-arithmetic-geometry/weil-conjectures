## Worker report

The module `Sheaf.Algebra.Lie.KillingFormOfTrivialRadical` states the complete
conjunction of sk-lem-walg-killing as
`LieAlgebra.killingForm_nondegenerate_and_derived_eq_top_of_radical_eq_bot`.
Its only proof is `by sorry`. No notion is redefined, no helper theorem or node
is added, and only the item's `lean` field changes.

Read the node, its two statement-dependency nodes and their Mathlib match records,
the current blueprint at
`literature/blueprint/latest/blueprint/sec-algebraic-groups-lie-algebras/sk-lem-walg-killing/`
(both `_section.md` and `sk-lem-walg-killing.proof.md`), and the reviewed DAG proof.
The DAG explicitly includes the reviewed extension to every characteristic-zero
field. There is no repair note for this item. The older algebraic-closedness
objection in split_report is resolved by the accepted stage-1 repair: this
statement adds no algebraic-closedness assumption.

Hypotheses and conclusions, clause by clause:

| Node text | Lean rendering |
| --- | --- |
| Any field L | `(k : Type u) [Field k]` |
| Characteristic zero | `[CharZero k]` |
| A Lie algebra over L | `(g : Type v) [LieRing g] [LieAlgebra k g]` |
| Finite dimensional | `[FiniteDimensional k g]` |
| Radical is the sum of solvable ideals | Existing `LieAlgebra.radical k g`, defined as `sSup { I : LieIdeal k g \| IsSolvable I }` |
| Radical vanishes | `(hrad : radical k g = ⊥)` |
| B(x,y) = trace(ad x composed with ad y) | Existing `killingForm k g`, whose formula is `killingForm_apply_apply` |
| B is nondegenerate | `(killingForm k g).Nondegenerate` |
| [g,g] = g | `derivedSeries k g 1 = ⊤` |
| Both conclusions | The conjunction `∧` |

The universes `u v` and every variable are explicitly bound; both auto-implicit
options are false. There is no restriction relating the field and algebra
universes. No nontriviality assumption is imposed on g.

Dependency declarations used and read:

- def-wf-lie-algebra: Mathlib.Algebra.Lie.Basic, `LieRing` and `LieAlgebra`;
  Mathlib.Algebra.Lie.Ideal, `LieIdeal`; Mathlib.Algebra.Lie.OfAssociative,
  `LieAlgebra.ad`; Mathlib.Algebra.Lie.Solvable, `derivedSeriesOfIdeal`,
  `derivedSeries`, `IsSolvable`, and `coe_derivedSeries_one_eq`.
  In particular the last identifies the first derived term with the linear span
  of all brackets, exactly the node's meaning of [g,g].
- def-wf-lie-radical-centre: Mathlib.Algebra.Lie.Solvable, `LieAlgebra.radical`,
  `radicalIsSolvable`, `LieAlgebra.LieIdeal.solvable_iff_le_radical`,
  `center_le_radical`; Mathlib.Algebra.Lie.Abelian, `LieAlgebra.center` and
  `LieModule.mem_maxTrivSubmodule`. The statement only uses radical; centre and
  solvability are used in its documented proof. These nodes are Mathlib leaves
  and have no `lean` record, so their recorded Mathlib interfaces are used.
- Killing-form identities: Mathlib.Algebra.Lie.TraceForm, `killingForm`,
  `killingForm_apply_apply`, `LieModule.traceForm_comm`,
  `LieModule.traceForm_apply_lie_apply`, and `LieIdeal.killingForm_eq`.
- Scalar extension: Mathlib.LinearAlgebra.Trace, `LinearMap.trace_baseChange`;
  Mathlib.Algebra.Lie.Solvable, `derivedSeries_baseChange` and
  `isSolvable_tensorProduct_iff` (all signatures read).
- Double orthogonal: Mathlib.LinearAlgebra.BilinearForm.Orthogonal,
  `LinearMap.BilinForm.orthogonal_orthogonal`.
- Algebraic closure: Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure,
  `AlgebraicClosure`.
- det-d-linear: its recorded module
  WeilConjectures.RepresentationTheory.CompositionSeries is imported privately
  as a proof dependency; its coefficient conventions are used only after
  extending the temporary ideal to the algebraic closure.
- Trace criterion: the node's attached declaration
  `LieSubalgebra.isSolvable_of_trace_mul_eq_zero` is in
  WeilConjectures.Mathlib.Algebra.Lie.CartanCriterion; its full signature and
  docstring were read. It is imported privately. No import cycle was found.

`Nondegenerate` is Mathlib's two-sided separation predicate. This is the usual
nondegeneracy of the symmetric Killing form; symmetry also makes it equivalent
to either one-sided condition. No extra assertion of symmetry is added.

Edge cases checked before writing:

- The zero Lie algebra is allowed: its zero form is nondegenerate on the zero
  space, and its first derived ideal is both bottom and top.
- For a nonzero abelian algebra the radical is the whole algebra, so hrad fails;
  its zero Killing form is therefore no counterexample.
- Over Q, sl_2 has nonzero-dimensional nondegenerate Killing form and is perfect;
  no algebraic-closure hypothesis excludes the existing rational-field consumer.
- The field need not have finite degree over Q and the algebraic closure need
  not have finite degree over the field. Only g is finite dimensional.
- Positive characteristic and infinite-dimensional algebras are excluded by
  precisely the hypotheses in the accepted node, not by hidden assumptions.

Searches actually run using
`/home/ubuntu/weil-launcher-all/batch2/msearch.py Q32 sk-lem-walg-killing`:

- leanfinder: "A finite dimensional Lie algebra over a characteristic zero field
  with zero solvable radical has nondegenerate Killing form and equals its
  derived algebra". Eight hits included IsKilling, HasTrivialRadical,
  IsSemisimple and the Killing-to-trivial-radical instance. None states the full
  conjunction.
- loogle: `LieAlgebra.HasTrivialRadical, LieAlgebra.IsKilling`. Three hits:
  `IsKilling.instHasTrivialRadical`, `HasTrivialRadical.instIsKilling`,
  `hasTrivialRadical_iff_isKilling`. These cover nondegeneracy, not perfectness.
- leansearch: "A finite dimensional characteristic zero Lie algebra with zero
  radical has a nondegenerate Killing form and is perfect". Eight hits included
  `IsKilling.killingForm_nondegenerate` and semisimplicity instances. No full match.
- grep in Algebra/Lie:
  `killingForm_nondegenerate|derivedSeries.*top|radical_eq_bot|IsPerfect`.
  Sixteen hits: partial nondegeneracy results, the HasTrivialRadical field, and
  general derived-series identities, with no full match.
- rg in project Sheaf and WeilConjectures sources for
  `nondegenerate.*derived|derived.*nondegenerate|killingForm.*radical|radical.*killingForm|derivedSeries.*eq_top`:
  the upstream nondegeneracy theorem and
  `LieAlgebra.center_sup_derivedSeries_eq_top` are partial matches. The latter
  has a central-radical hypothesis and a different conclusion, not the full item.
- rg for `sk-lem-walg-killing` in WeilConjectures found no declaration. Searching
  radical/Killing in its Lie directory found the partial CartanCriterion and
  Radical modules, whose relevant signatures and docstrings were read.
- rg of the proposed full name in Mathlib, WeilConjectures, Sheaf and
  dag/lean_names_upstream.json found no match.

Validation: scompile.py compiled this file successfully both as sandbox
Sheaf.Stage2.Sandbox0 (21.7 s) and as its intended library module (11.9 s),
with no errors or non-sorry warnings. The declaration docstring carries all five
accepted proof steps, including scalar extension and descent. No outstanding
statement fault or STATEMENT-DISPUTED assertion is raised by this worker.

## Second reading by Q32

The dispatcher brief prohibits starting other agents and assigns independent
review to the maintainer. This section records the worker's own second pass,
not an independent review.

Reopened the node and the completed module. The field and characteristic binders
match the first sentence, the LieRing/LieAlgebra instances match its algebra,
FiniteDimensional matches finite dimension, and hrad uses exactly the radical
recorded by def-wf-lie-radical-centre. The formula for killingForm was checked
against TraceForm.lean; it uses the adjoint representation on g itself, not an
auxiliary representation. The first conjunct is nondegeneracy of that form;
the second is equality of the first derived ideal with top, checked against
coe_derivedSeries_one_eq. Both parts remain in one conjunction. The zero algebra
and the rational-field case remain included. No mismatch or correction was
needed. The unrelated central-radical result was not substituted for this item.
