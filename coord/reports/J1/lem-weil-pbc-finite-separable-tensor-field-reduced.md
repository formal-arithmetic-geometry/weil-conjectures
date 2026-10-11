## Worker report

Module: `Sheaf.FieldTheory.FiniteSeparableTensorFieldReduced`.
Declaration: `Algebra.isReduced_tensorProduct_of_finiteSeparable`.
This states the node unchanged, with one `sorry` proof and no definitions or other theorems.
The docstring carries all four proof steps and every dependency used by those steps.

Hypothesis and clause correspondence:
- L is a field: `(L : Type u) [Field L]`.
- K'/L is a field extension: `(K : Type v) [Field K] [Algebra L K]`.
  `K` names the node's K'; `algebraMap L K` is its structural ring homomorphism.
- The extension is finite-dimensional over L: `[FiniteDimensional L K]`.
- The extension is separable algebraic: `[Algebra.IsSeparable L K]`.
  The class requires each minimal polynomial to be separable and already implies algebraicity;
  no separate algebraicity assumption is necessary.
- E/L is any field extension: `(E : Type w) [Field E] [Algebra L E]`.
  There is no finiteness, algebraicity, separability or algebraic-closure assumption on E.
- The ring K' tensor E over L: `K ⊗[L] E`, with Mathlib's canonical commutative ring instance.
  `Algebra.TensorProduct.tmul_mul_tmul` gives the multiplication specified in the node;
  `Algebra.TensorProduct.one_def` gives its unit `1 tensor 1`.
- Reducedness/no nonzero nilpotents: `IsReduced (K ⊗[L] E)`.
  Its defining field is `eq_zero : ∀ x, IsNilpotent x → x = 0`.

Dependency declarations read and used:
- `def-pc-field-extension` is Mathlib leaf `Algebra`,
  `Mathlib.Algebra.Algebra.Defs`: fields equipped with the two L-algebra structures.
- `def-weil-pbc-separable-algebraic-extension` is Mathlib leaf `Algebra.IsSeparable`,
  `Mathlib.FieldTheory.Separable`: its full class definition, `IsSeparable`, and
  `Algebra.IsSeparable.isAlgebraic` were read. Neither leaf needs a dependency module.
- `FiniteDimensional` from `Mathlib.LinearAlgebra.FiniteDimensional.Defs`,
  tensor-product ring operations from `Mathlib.RingTheory.TensorProduct.Basic`, and
  `IsReduced` from `Mathlib.Algebra.GroupWithZero.Basic` render the remaining standard notions.

Edge cases checked: the degree-one extension K=L and E=L are included. Fields are nontrivial,
so dimension zero is not a field-extension case. Positive characteristic, imperfect L,
nonalgebraic E and arbitrary differing universes u/v/w are included. For example, K=E=C over
L=R gives a product of fields, so asking only reducedness rather than a domain is necessary.
Separability cannot be dropped in positive characteristic: adjoining a p-th root of a
non-p-th-power and tensoring with the same field produces a nonzero nilpotent.
No statement correction or disputed statement was needed.

Source checked: the local Stacks checkout is absent on this machine. Read the official page
https://stacks.math.columbia.edu/tag/030U, first proof paragraph, which uses a separable
minimal polynomial and the reducedness of the resulting quotient over a field. The node's
primitive-element reduction extends that argument to any finite separable algebraic extension.

Searches (actual queries logged in searches.jsonl):
- LeanFinder: "A finite separable field extension tensored over its base field with any field
  extension is reduced". Eight hits, including geometrically reduced algebra results and
  linear-disjointness results; none has the node's hypotheses and conclusion.
- Loogle: `Algebra.IsSeparable, IsReduced`. No hits.
- LeanSearch: "tensor product of finite separable field extension with arbitrary field
  extension is reduced". Service unavailable (Internal Server Error); other searches used.
- msearch grep: `IsReduced.*⊗|isReduced_tensorProduct|IsSeparable` in
  `RingTheory/Nilpotent`. Three hits on geometric reducedness, not this statement.
- rg in WeilConjectures and lean/Sheaf for
  `isReduced_tensorProduct|tensor.*[Ss]eparab|[Ss]eparab.*tensor`, plus an item-id search
  in WeilConjectures. Read the source module
  `WeilConjectures/Mathlib/RingTheory/Nilpotent/GeometricallyReduced.lean` in full.
  Existing results require a perfect base field or a formally-unramified tower and a
  reducedness premise. The landed algebraically-closed tensor theorem only treats
  algebraically closed E. No exact existing statement; no item-id match upstream.
- Exact proposed-name search in dag/lean_names_upstream.json, Mathlib and WeilConjectures:
  `finiteSeparable.*[Rr]educed|isReduced_tensorProduct_of_finiteSeparable`. No collision.

Validation: server single-file compilation and deliver2.py --no-push dry run; see worker
completion line for the dry-run result. No second-reading section is supplied by the author.

## Second reading by J1

Independent reader: opened the sandbox node and module, both statement-dependency
nodes, and their Mathlib declarations. No mismatch found; the Lean and node record
are unchanged. Only this second-reading section was added.

Object/hypothesis/conclusion inventory and comparison (H3):
1. Base field L: `(L : Type u) [Field L]`. Exact, including the source's nontrivial
   commutative field convention.
2. Field K' with a specified extension structure over L: `(K : Type v) [Field K]
   `[Algebra L K]`. Exact; K is the renamed K'. The recorded declaration of
   `def-pc-field-extension` is `Algebra` in `Mathlib.Algebra.Algebra.Defs`.
   Its `algebraMap : L →+* K` and scalar action give precisely this extension,
   not an unspecified inclusion or a second extension notion.
3. Finite-dimensional L-vector space K': `[FiniteDimensional L K]`. Exact;
   opened `Mathlib.LinearAlgebra.FiniteDimensional.Defs`, where this abbreviates
   `Module.Finite L K`. It means finite dimension, not a finite underlying field.
4. Separable algebraic extension K'/L: `[Algebra.IsSeparable L K]`. Exact;
   opened the dependency `def-weil-pbc-separable-algebraic-extension` and
   `Mathlib.FieldTheory.Separable` lines 535–580. The class says every element's
   minimal polynomial is separable; `IsSeparable.isIntegral` and the instance
   `Algebra.IsSeparable.isAlgebraic` show algebraicity is included. No algebraicity
   hypothesis was dropped and no perfection or characteristic hypothesis added.
5. Any field extension E/L: `(E : Type w) [Field E] [Algebra L E]`. Exact;
   no assumption of finite dimension, algebraicity, separability, or algebraic
   closedness on E, and no map between K and E is requested.
6. Tensor-product ring K' tensor E over L: `K ⊗[L] E`. Exact factor order and
   base. Opened `Mathlib.RingTheory.TensorProduct.Basic`: `one_def` at line 113
   gives unit 1 tensor 1 and `tmul_mul_tmul` at lines 155–157 gives exactly the
   multiplication in the node. Canonical commutative ring structure is used.
7. No nonzero nilpotents: `IsReduced (K ⊗[L] E)`. Exact; opened
   `Mathlib.Algebra.GroupWithZero.Basic` lines 191–193: the field is
   `eq_zero : ∀ x, IsNilpotent x → x = 0`. No domain, field, or product
   decomposition conclusion is asserted. All three objects are universally
   quantified before their structures and extension hypotheses.

Source reading: the local Stacks checkout is absent. Read the official raw
[algebra.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex),
label `lemma-separable-extension-preserves-reducedness`, currently lines 9260–9299,
and its chapter conventions (commutative unital rings). The first paragraph's
simple algebraic extension has separable minimal polynomial; over the fraction
field its polynomial quotient is a product of fields. No perfection or
characteristic assumption occurs. The finite-type reductions on S in that proof
are reductions of the general theorem, not restrictions on this field E.
Also read raw
[fields.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/fields.tex)
at `lemma-primitive-element`, and official [030N](https://stacks.math.columbia.edu/tag/030N):
finite separable field extensions admit a primitive element, including finite
base fields. Together these justify exactly the node's finite separable K'/L
specialization of [030U](https://stacks.math.columbia.edu/tag/030U).

Edge cases: degree one (K=L) and E=L are covered. Degree zero and the zero ring
are excluded by the node's field hypotheses themselves, not by an extra binder.
No index set, scheme, zero object, or natural-number parameter is present.
The conclusion permits zero divisors (e.g. complex numbers tensored with complex
numbers over the reals), so reducedness has not been silently strengthened.
Arbitrary positive characteristic and imperfect L are covered when K/L is
separable. E may be transcendental or inseparable over L. Universes u, v, w are
explicit, independent, and all variables and instances are bound.

Independent H4 searches, using different queries from the author:
- LeanFinder through msearch: `Reduced base change of finite etale field algebras
  along arbitrary field extensions`. Eight hits, including `Algebra.Etale.baseChange`,
  `RingHom.Etale.isStableUnderBaseChange`, and `Algebra.Etale.comp`; no exact
  finite-separable tensor reducedness statement.
- Loogle through msearch: `IsReduced, TensorProduct`. Six hits, including
  `IsReduced.tensorProduct_of_flat_of_forall_fg` (needs reducedness of all
  finitely generated subalgebra tensors) and
  `Algebra.instIsReducedTensorProductOfIsAlgebraicOfIsGeometricallyReduced`
  (needs geometric reducedness); no exact match.
- LeanSearch through msearch: `Base extension of a finite separable algebra is
  a ring without nilpotents`. Service returned Internal Server Error; unavailable,
  not evidence of absence. Other searches and source inspection completed.
- rg in Mathlib, WeilConjectures and lean/Sheaf with
  `reduced.*tensor|tensor.*reduced|separable.*tensor|tensor.*separable`
  (case-insensitive). Read upstream `Mathlib/RingTheory/Nilpotent/GeometricallyReduced.lean`
  and `Mathlib/RingTheory/Etale/Basic.lean`, and Mathlib's geometric-reducedness
  file. Perfect-field results add perfection; the formally-unramified result
  takes a tower, unramified/finite-type structures and a reduced tensor premise;
  the etale result takes etaleness. These are ingredients, not the present
  signature. Opened landed `Sheaf.FieldTheory.SeparableTensorAlgebraicClosure`:
  it requires algebraically closed E and states a product decomposition, so is
  not this node. Proposed-name rg in dag/lean_names_upstream.json, Mathlib,
  WeilConjectures and lean/Sheaf found no collision.

H5–H9: no definitions, hollow data, new definition nodes or dependency modules;
no statement correction. One theorem, whose proof remains `by sorry`. Module
and theorem docstrings carry the source and exact blueprint id. The four proof
steps cover primitive-element/power-basis presentation, tensor scalar/quotient
base change, preservation of separability via the derivative Bezout identity,
and transport of quotient reducedness, naming all proof dependencies. Topic,
namespace, explicit universes, line lengths and canonical notions are correct.
The recorded `lean.statement` is verbatim the file signature before `:=`.

Validation: single-file server compilation via scompile.py; delivery dry run
and final delivery via deliver2.py (outcomes checked by this reader).
