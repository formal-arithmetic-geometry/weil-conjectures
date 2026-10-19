## Worker report

The module `Sheaf.FieldTheory.OneVariableFieldCohomologicalDimension` states
`AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_ratFunc` with
`sorry`. No definitions or proofs are added, and the node changes only in `lean`.
The source blueprint lemma and its full DAG proof were read. No statement fault
or disputed statement was found.

Clause-by-clause correspondence:

- “If F is separably closed”: `(F : Type u) [Field F] [IsSepClosed F]`.
  The universe is explicit and arbitrary. `IsSepClosed` is Mathlib's class requiring
  separable polynomials to split, without a perfection or characteristic restriction.
- “F(x)”: `RatFunc F`, Mathlib's fraction field of the univariate polynomial ring.
  It is not a finite extension or an algebra of finite type over F.
- “cd_tor(F(x)) ≤ 1, with the bound of def-sc-etale-torsion-cd”:
  `HasTorsionEtaleCohomologicalDimensionLE (Spec (.of (RatFunc F))) 1`.
  This is the dependency's exact scheme predicate applied to the affine spectrum,
  as its field convention specifies. It quantifies over all locally torsion abelian
  étale sheaves and all natural degrees q > 1, requiring ordinary derived-section
  cohomology to be subsingleton. There is no common annihilator assumption.

Dependency declaration used:
`Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`,
`AlgebraicGeometry.Scheme.HasTorsionEtaleCohomologicalDimensionLE`.
Its complete definition and docstring were read. Mathlib notions come from
`Mathlib.FieldTheory.IsSepClosed` (`IsSepClosed`) and
`Mathlib.FieldTheory.RatFunc.Basic` (`RatFunc`, its field instance; the underlying
structure and fraction-field documentation are in `RatFunc.Defs`).

Proof-plan imports cover the recorded, already stated proof dependencies:
`Mathlib.AlgebraicGeometry.GammaSpecAdjunction` (Spec limit preservation),
`Mathlib.AlgebraicGeometry.Morphisms.Affine` (affine transition maps),
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` (affine qcqs),
`Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance`
(`AlgebraicGeometry.Etale.universalHomeomorphism_invariance`), and
`Mathlib.CategoryTheory.MorphismProperty.Limits` (`MorphismProperty.universally`).
The dimension definition is already a public statement import. The proof nodes
`lem-sc-arbitrary-curve-cd` and `lem-sc-cd-affine-limit` have neither a Lean record
nor a Mathlib match in this snapshot, so there is no module to import for them.
There is no new notion needed to state this item.

Edge cases checked: characteristic zero and positive characteristic both remain
included; separably closed imperfect fields are included (no `PerfectField` or
`IsAlgClosed` hypothesis); there is exactly one transcendental variable. The
predicate allows the zero sheaf and torsion sheaves with unbounded annihilators.
Degree 0 and degree 1 are not forced to vanish. Negative cohomological degrees are
already zero for degree-zero sheaves, consistent with the natural-degree predicate.
A field is nontrivial by its Mathlib class; no extraneous empty-scheme case is
excluded by the theorem. No cardinality or independent universe restriction is
introduced.

Searches performed before writing:

- `msearch.py leansearch`: “The rational function field over a separably closed
  field has torsion etale cohomological dimension at most one”. The service returned
  Internal Server Error; this unavailable search supplies no mathematical verdict.
- `msearch.py leanfinder`, same query: eight hits, including
  `Algebra.FormallyEtale.of_isSeparable`, `functionField_iff` and `FunctionField`;
  none states an étale cohomological dimension bound.
- `msearch.py loogle`: `IsSepClosed, RatFunc`: zero hits.
- `msearch.py grep`: `cohomologicalDimension|CohomologicalDimension|torsion.*cohomological|cohomological.*torsion`
  throughout Mathlib: zero hits.
- `rg` in source `WeilConjectures` and project `lean/Sheaf`: searched
  `EtaleTorsion|etaleTorsion|torsion.*[Cc]ohomological|[Cc]ohomological.*torsion`.
  Read the existing source `AlgebraicGeometry/Sites/CohomologicalDimension.lean`:
  it gives the different finite-type bound `2d+c`, not this field theorem.
  The project hit is the dependency predicate used here.
- `rg` for `lem-sc-one-variable-field-cd`, rational-function/cohomology patterns
  and the proposed declaration name in source, Mathlib, project Lean and
  `dag/lean_names_upstream.json`: no existing matching declaration or name conflict.

The module docstring gives the source and blueprint id; the theorem docstring
reproduces all four DAG proof steps, including filtered localization, purely
inseparable transfer with the prime/basic-open argument, the curve bound, and
passage to the limit. Validation uses only the prescribed server `scompile.py`
and `deliver2.py --no-push`; no local compiler or build is run. An independent
second reading is reserved for the next worker.

## Second reading by NC

The node introduces a field `F` that is separably closed, then asserts the torsion étale
cohomological dimension bound for the rational function field `F(x)`.  In the Lean
signature, `(F : Type u) [Field F] [IsSepClosed F]` renders the field and separably
closed hypotheses.  `RatFunc F` is Mathlib's fraction field of `F[X]`, rendering `F(x)`,
and `Spec (.of (RatFunc F))` is the affine scheme convention required by the dependency.
The conclusion `HasTorsionEtaleCohomologicalDimensionLE (Spec (.of (RatFunc F))) 1`
uses exactly the dependency predicate, so it states the bound `cd_tor ≤ 1`; its predicate
quantifies over all locally torsion abelian étale sheaves and all natural `q > 1`, with
ordinary derived-section cohomology subsingleton.  No clause or quantifier is added or
removed.  The theorem has no extra finiteness, characteristic, algebraic-closedness,
or perfection hypothesis.

Edge cases checked: `u` is arbitrary; both characteristic zero and positive
characteristic fields are admitted; separably closed need not mean algebraically closed;
`RatFunc F` has exactly one transcendental variable; the bound predicate includes the
zero sheaf and does not require a uniform annihilator; degrees zero and one are not
claimed to vanish.  The field instance excludes the degenerate zero ring, as in the
source convention.  No index type, empty scheme, or independent universe is introduced.

I reread the dependency node `def-sc-etale-torsion-cd` and its declaration
`AlgebraicGeometry.Scheme.HasTorsionEtaleCohomologicalDimensionLE` in
`Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`; it is the exact predicate used
by the conclusion.  Searches were repeated with `rg` in Mathlib, `WeilConjectures`, and
`lean/Sheaf`, and with `msearch.py` LeanSearch, LeanFinder, and Loogle for the theorem
and for the torsion étale cohomological-dimension notion.  No existing theorem or
alternative definition was found; the only project match is the recorded dependency.

No mismatch was found, so no source, node statement, dependency, or Lean declaration
was changed.  The module compiled successfully with the prescribed server
`scompile.py` invocation; only the expected `sorry` proof remains.
