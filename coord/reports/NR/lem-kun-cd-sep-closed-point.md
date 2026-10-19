## Worker report

The module states the numerical torsion étale cohomological dimension of a separably
closed point is zero. The sole theorem is
`AlgebraicGeometry.Scheme.torsionEtaleCohomologicalDimension_eq_zero_of_isSepClosed`,
with its entire proof postponed by `sorry`.

Clause-by-clause correspondence:
- A field K: `(K : Type u) [Field K]`, with arbitrary explicitly declared universe `u`.
- K is separably closed: `[IsSepClosed K]`, the recorded Mathlib notion.
- Its spectrum: `Spec (.of K)`, using the field's commutative-ring structure.
- The complete conclusion cd(Spec K) = 0:
  `(Spec (.of K)).torsionEtaleCohomologicalDimension = 0`.
  This is the recorded numerical definition in `ℕ∞`, not merely a statement about
  individual cohomology groups. Compactness and quasi-separatedness are inferred for
  this affine scheme; neither is an added hypothesis.

Dependency declarations read and used:
- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed` (`def-kun-separably-closed`).
  Its splitting-polynomial formulation is the recorded equivalent of having no
  nontrivial finite separable extension.
- `Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension`:
  `AlgebraicGeometry.Scheme.torsionEtaleCohomologicalDimension` (`def-kun-cd`).
  This is the infimum in `ℕ∞` of the finite torsion étale cohomology bounds.
- Proof-only import `WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport`:
  `AlgebraicGeometry.Scheme.subsingleton_H_of_isSepClosed`
  (`lem-kun-03qu-sep-closed`), whose full signature and docstring were read.
  It covers every abelian étale sheaf and every positive degree `n + 1`.

Edge cases checked: a field is nontrivial so its spectrum is not empty; all
characteristics are allowed, including imperfect separably closed fields. Degree zero
is not asserted to vanish; only positive-degree vanishing is used in the documented
proof. Torsion sheaves need not have a uniform annihilator. The dimension's codomain
includes infinity, and zero remains the least possible bound. No algebraic-closedness,
finite-type hypothesis or characteristic restriction is imposed.

Searches for an existing statement:
- `msearch.py leanfinder`: "The torsion etale cohomological dimension of the spectrum
  of a separably closed field is zero" returned eight results about étale algebras,
  local rings and cotangent modules, none the numerical dimension equality.
- `msearch.py loogle`: `IsSepClosed, AlgebraicGeometry.Spec` returned seven results
  concerning geometric points of the small étale site, none the equality.
- `msearch.py grep`: `cohomologicalDimension|CohomologicalDimension|subsingleton_H_of_isSepClosed`
  returned zero Mathlib hits.
- `msearch.py leansearch`: "The etale cohomological dimension of a separably closed
  field is zero" was unavailable (Internal Server Error).
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for
  `cohomologicalDimension|CohomologicalDimension|lem-kun-cd-sep-closed-point` found
  the recorded numerical definition, bound predicates, and positive-degree vanishing.
  `FiniteSupport` cites this blueprint id but states vanishing, not the numerical
  equality. `SeparablyClosedTorsionCohomologicalDimension` states the zero-bound
  predicate, not this numerical equality; no notion is redefined here.
- Exact-name `rg` in the upstream-name inventory, upstream sources and project
  sources found no occurrence of the new theorem name.

No statement correction, new node, dependency repair or disputed statement is needed.

## Second reading by NR

Read the node, its blueprint source and proof, both statement-dependency nodes and
their actual declarations, and the proof-dependency theorem in FiniteSupport.
Also read Stacks etale-cohomology.tex, Tags 0F0Q (definition-cd) and 03QU
(lemma-compare-cohomology-point), including the preceding 04JQ hypotheses:
S = Spec K for a field K, a geometric point, and its absolute Galois group.
For separably closed K this group is trivial. There is no characteristic,
perfectness, finite-type, or Noetherian assumption in these source statements.

Object/hypothesis/conclusion checklist:
- Field K, arbitrary size: `(K : Type u) [Field K]`, with `universe u`
  explicitly declared. Exact match; no hidden universe equality.
- Separably closed K: `[IsSepClosed K]`. Read Mathlib's class definition:
  every separable polynomial splits, the recorded equivalent of no nontrivial
  finite separable extension. Exact match, including imperfect fields.
- The scheme Spec K: `Spec (.of K)`. The spectrum is of the given field,
  not its algebraic closure or an arbitrary geometric point. Exact match.
- Numerical torsion etale dimension: the recorded
  `Scheme.torsionEtaleCohomologicalDimension`, whose actual definition is
  the infimum in ENat of finite bounds. Its bound predicate quantifies over
  all locally torsion abelian small-etale sheaves, in AddCommGrpCat.{u+1},
  and all natural cohomological degrees above the bound. Read that predicate
  too; it uses ordinary derived sections, not compactly supported cohomology.
  CompactSpace and QuasiSeparatedSpace are inferred for this affine spectrum,
  not additional hypotheses. Exact match to def-kun-cd and Stacks 0F0Q.
- Entire conclusion cd(Spec K) = 0:
  `(Spec (.of K)).torsionEtaleCohomologicalDimension = 0`. This is the
  numerical equality requested, including its least-bound meaning. Exact match.

Edge cases: a Field is nontrivial, so the empty spectrum and zero ring are
outside the stated objects. The zero sheaf is included in the dimension
predicate; no nonzero-coefficient hypothesis is imposed. Degree zero is not
asserted to vanish. All positive degrees are covered, since each is n+1 in
`Scheme.subsingleton_H_of_isSepClosed`. No index set or positive integer
parameter is introduced. All characteristics, including characteristic p
coefficients and imperfect separably closed fields, are retained. Infinity
is a possible value of the definition but the conclusion establishes zero.
There is no uniform-annihilator assumption on torsion sheaves.

Independent uniqueness searches:
- msearch leanfinder: "Numerical etale torsion cohomology dimension of
  separably closed point equals zero": eight hits on cotangent spaces and
  formally etale algebras, no numerical etale-dimension equality.
- msearch loogle: `"IsSepClosed"`: twelve hits, the class and field-theoretic
  properties, none the numerical equality.
- msearch leansearch: "etale cohomological dimension of spectrum of separably
  closed field equals zero": unavailable, Internal Server Error.
- Direct rg in Mathlib for cohomologicalDimension/CohomologicalDimension:
  no hits. Direct rg in upstream WeilConjectures and project lean/Sheaf for
  numerical dimension, bound-predicate names and separably closed variants
  found the definition, the zero-bound theorem and positive-degree vanishing.
  Opened SeparablyClosedTorsionCohomologicalDimension: its conclusion is
  HasTorsionEtaleCohomologicalDimensionLE ... 0, not this numerical equality.
  Opened FiniteSupport: its theorem is Subsingleton (Sheaf.H H (n+1)),
  not the equality. The upstream name inventory contains no occurrence of
  the delivered theorem name. No duplicate declaration or definition found.

No mismatch found and no Lean or node change made. There are no new nodes,
dependency modules, or statement correction to review. The module and theorem
have source/blueprint docstrings, and the theorem docstring carries the node's
one-point qcqs check, positive-degree vanishing, and least-bound argument.
The only proof is the whole named theorem's sorry; there are no new definitions,
local notation or instances, unbound parameters, or hollow data. Checked the
node lean.statement equals the file signature verbatim and all lines are at
most 100 characters. Server scompile.py compiled the sole delivered module
successfully, with no warnings or errors (sandbox 1.8 s, library 1.9 s).
