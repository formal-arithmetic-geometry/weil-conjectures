## Worker report

The module `Sheaf.AlgebraicGeometry.PerfectGeneratorExists` states
`AlgebraicGeometry.exists_perfect_generator`, with its proof `sorry`.

Hypothesis and conclusion correspondence:

- Scheme X: `(X : Scheme.{u})`.
- Quasi-compact: `[CompactSpace X]`; quasi-separated: `[QuasiSeparatedSpace X]`.
- D(O_X): the shared `HasDerivedCategory.{w}` instance for `SheafOfModules.{u}`;
  instances on every open are supplied for the recorded perfect-complex definition.
  These are construction infrastructure, not restrictions on X.
- M in D_QCoh(X): `∃ M : schemeDerivedQCohCategory X`; its `.1` is the underlying
  object of D(O_X), with quasi-coherent cohomology certified by `.2`.
- Perfect: `Scheme.IsPerfect X M.1`, exactly the dependency's local strictly-perfect model.
- Generator in the stated sense: `IsWeakTriangulatedGenerator M`, in D_QCoh(X).
  The existential `htri` supplies the inherited triangulated structure via `letI`,
  so no triangulation is imposed as an extra hypothesis.
- Smallest localizing, retract-closed full subcategory is all D_QCoh(X): for every
  `P : ObjectProperty (schemeDerivedQCohCategory X)`, if `P.IsTriangulated`,
  `P.IsStableUnderRetracts`, `∀ I : Type u, P.IsClosedUnderColimitsOfShape (Discrete I)`,
  and `P M`, then `∀ E, P E`. This is the universal characterization of the smallest
  such subcategory being the whole category. Retract closure implies isomorphism closure,
  so these are strictly full subcategories. Discrete-diagram colimits are coproducts.
  All component notions are Mathlib declarations, used directly; no new definition needed.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` (locally ringed space
  with local affine charts) and `Scheme.Hom` (locally ringed-space morphisms).
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `AlgebraicGeometry.schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory`.
- `Sheaf.AlgebraicGeometry.PerfectComplex`: `AlgebraicGeometry.Scheme.IsPerfect`.
- `Sheaf.CategoryTheory.WeakTriangulatedGenerator`:
  `CategoryTheory.IsWeakTriangulatedGenerator`.
- Mathlib `ObjectProperty.IsTriangulated`, `ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.IsClosedUnderColimitsOfShape` supply the closure clauses.

Edge cases checked: the empty scheme is admitted; perfection's pointwise condition is
vacuous and the zero derived category has a vacuous weak-generator condition. There is
no nonzero requirement on M. Empty index sets and singleton coproducts are covered by
`I : Type u`, including the zero coproduct. Shifts range over all integers through the
recorded generator definition. No field or characteristic hypothesis is present. The
coproduct index universe u matches the module-sheaf universe, as in the landed
`derivedQCohDirectSums` theorem. The localizing clause asks closure under existing
colimits, not an extra existence property of P.

Searches made on this machine:

- `msearch.py ... leanfinder "A quasi compact quasi separated scheme has a single perfect
  generator of its quasi coherent derived category"`: eight general DerivedCategory
  T-structure hits, none a scheme generator theorem.
- `msearch.py ... loogle "IsWeakTriangulatedGenerator, Scheme.IsPerfect"`: zero hits,
  unknown identifier `IsWeakTriangulatedGenerator` in the search index.
- `msearch.py ... grep "perfect.*generator|exists_perfect_generator" CategoryTheory`:
  zero hits in Mathlib.
- `rg` for `perfect.*generator|exists_perfect_generator|lem-pc-perfect-generator-exists`
  in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`: no hits.
- `rg` for `perfect.*generator|exists_perfect_generator` in project `lean/Sheaf`: no hits.
- `rg` of `dag/lean_names_upstream.json` for `exists_perfect_generator`: no hits.
- Mathlib source search identified the three existing ObjectProperty closure classes;
  their signatures and docstrings were read.

Source read: [Stacks 09IS](https://stacks.math.columbia.edu/tag/09IS) gives the perfect
weak generator for qcqs schemes; [Stacks 09SN](https://stacks.math.columbia.edu/tag/09SN)
gives the homotopy-colimit construction used for the closure clause. The node's referenced
local TeX file is absent on this machine, so the official source pages were read instead.
The docstring follows all four proof steps and names the proof dependencies.

No statement correction, dependency repair, or disputed assertion.

Validation: server single-file compilation succeeded without errors or warnings.


## Second reading by C1

I independently opened the item node, its complete proof, the delivered module, each of
its four statement-dependency nodes, and the source of each dependency declaration.
There are no new nodes or dependency modules in this delivery and no statement_change.

Source checked: Stacks Tag 09IS, Theorem 36.15.3, and the surrounding Generating derived
categories section. The repository's literature checkout is absent. I read the official
Stacks page and fetched the official stacks/stacks-project `perfect.tex` into this item's
scratchpad, reading lines 3830–3952, including the section's assumptions and the complete
`theorem-bondal-van-den-Bergh`. The node's historical document filename and label are not
the current source filename/label; Tag 09IS identifies the intended theorem unambiguously.
Only quasi-compactness and quasi-separatedness are assumed; there is no base ring, field,
Noetherian, separatedness, characteristic, or nonemptiness assumption. I also read the
official Tag 09SN statement and telescope proof for the node's final closure clause.

Object/hypothesis/conclusion checklist, written from the node before matching the Lean:

- Object: arbitrary scheme X. Lean `(X : Scheme.{u})` uses Mathlib's scheme, the recorded
  `def-pc-scheme` declaration. Verdict: exact, arbitrary universe u.
- Hypothesis: X quasi-compact. Lean `[CompactSpace X]` is quasi-compactness of its underlying
  space without a Hausdorff condition. Verdict: exact.
- Hypothesis: X quasi-separated. Lean `[QuasiSeparatedSpace X]` says intersections of
  quasi-compact opens are quasi-compact. Verdict: exact, not separatedness.
- Ambient category: D(O_X), and its full subcategory D_QCoh(X). Lean uses the recorded
  `schemeDerivedCategory`, `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory` from
  `Sheaf.AlgebraicGeometry.DerivedCategory`. I read their bodies: the ambient category is
  DerivedCategory of the shared SheafOfModules carrier, and the subcategory requires every
  integer cohomology sheaf to be Mathlib IsQuasicoherent. Verdict: exact, not D(QCoh(X)),
  not a bounded category, and not a category with just coherent cohomology.
- Derived-category construction: the shared `[HasDerivedCategory.{w} ...]`, globally and
  on all opens, is needed by the recorded IsPerfect signature. These supply localization
  models, not finiteness or geometric conditions. Verdict: accepted dependency infrastructure;
  u and w are bound explicitly and no chosen alternate Abelian instance is used.
- Conclusion: one object M in D_QCoh(X), existentially chosen after X. Lean
  `∃ M : schemeDerivedQCohCategory X`. Its `.1` is the ambient object and `.2` certifies
  quasi-coherent cohomology. Verdict: exact; no fixed preselected generator.
- Conclusion: M perfect. Lean `Scheme.IsPerfect X M.1`. I read IsStrictlyPerfect,
  IsPerfect, and perfectSubcategory in the dependency module: bounded complexes whose
  terms retract off finite free module sheaves, and a strictly-perfect model of the derived
  restriction on a neighbourhood of every point. Verdict: exact local definition, with
  no global bounded finite-free presentation imposed.
- Conclusion: M weakly generates in the node's sense. Lean
  `IsWeakTriangulatedGenerator M`, from the recorded dependency. I read its body:
  every nonzero K admits `n : ℤ` and `f : M ⟶ K⟦n⟧` with `f ≠ 0`. Verdict: exactly
  def-pc-generators. The shifted-source Hom detection in 09IS is equivalent by shifting
  and negating n, using the full-subcategory Hom identification.
- Conclusion: the smallest localizing retract-closed full subcategory containing this same
  M is all D_QCoh(X). Lean universally quantifies `P : ObjectProperty ...`, assumes
  `P.IsTriangulated`, `P.IsStableUnderRetracts`,
  `∀ I : Type u, P.IsClosedUnderColimitsOfShape (Discrete I)`, and `P M`, and concludes
  `∀ E, P E`. Verdict: exact universal characterization. I read Mathlib's three closure
  classes: IsTriangulated gives zero, all integer shifts and distinguished-triangle closure;
  retract stability implies isomorphism stability (the explicit instance in Retract.lean),
  hence strictly full; discrete colimits are coproducts. Closure applies to any existing
  colimit, not just the chosen presentation. The u-indexed sums are the same set-size
  convention as the recorded `derivedQCohDirectSums : HasCoproducts.{u} ...`.
- Infrastructure assertion: `(schemeDerivedQCohProperty X).IsTriangulated` supplies the
  inherited triangulation, whose distinguished triangles are the ambient ones (I read
  Mathlib Subcategory.lean's Pretriangulated instance). Verdict: canonical triangulation,
  not a freely chosen extra structure or an extra hypothesis on X.

Mismatch found and repaired: the first file used `∃ htri, letI := htri; ...` in its
statement, contrary to the no-let statement convention. I replaced it with the conjunction
asserting the same IsTriangulated proposition and `∀ [htri : ...], ...`. The first conjunct
ensures the instance binder cannot make the conclusion vacuous. IsTriangulated is Prop,
so proof irrelevance makes the universal instance version equivalent to the original
existential-proof version, including the induced shifts and triangles. The generator is
still chosen before P and shared by both conclusion clauses. I synchronized lean.statement
verbatim with the revised signature. The Worker report's account of letI describes the
original file; this section supersedes that account. No mathematical node correction was
needed, and all already-correct definitions and proof-docstring steps were left intact.

Edge cases: the empty scheme is admitted (no Nonempty X); perfection is then pointwise
vacuous, and a zero generator is allowed. No nonzero M condition is imposed; on a nonzero
category the weak-generator condition itself rules out a zero M. All integers n including
zero and negative values are covered. Empty, singleton and infinite coproduct indices are
included by `I : Type u`; no Nonempty or Fintype condition is present. No characteristic
or field is fixed. All universe variables are bound; the ambient/local derived-category
instances use the same w and the shared module-sheaf universe u.

Independent H4 searches (different terms from the first writer):

- msearch leanfinder: "Bondal van den Bergh compact object generates derived quasi coherent
  sheaves"; eight generic derived-category/Grothendieck sheaf results, none the statement.
- msearch loogle: "IsClassicalTriangulatedGenerator"; unknown identifier in the service
  index, zero hits; not treated as a successful identification.
- msearch leansearch: "quasi separated quasi compact scheme admits perfect weak generator";
  service Internal Server Error, recorded unavailable; no match claim based on it.
- msearch grep: "single.*generat|weak.*generat|generat.*derived" in AlgebraicGeometry;
  zero hits.
- Direct rg over Mathlib, WeilConjectures, and project lean/Sheaf for Bondal,
  van.den.Bergh, perfect.*generat, generat.*perfect, and exists_perfect_generator. Mathlib
  Generators.lean has classical and strong triangulated generators, not this theorem.
  Upstream Perfect.lean concerns ring complexes, not this scheme result. Project
  DerivedQCohCompactGeneration gives a set of compact generators, not a single perfect
  object with both clauses. None is an exact existing declaration; no module dropped.

H5/H6/H8/H9: no definitions or private notion copies were added, no hollow data, the
only theorem proof is sorry. The docstring records all four node proof steps and their
uses (including quasi-coherent cohomology of perfect objects and the inherited
triangulation). Imports serve the category, perfect and weak-generator predicates and
ObjectProperty closures. Lines are at most 100 characters. The repaired module compiled
on the server cleanly (no errors or warnings) using scompile.py.

## Reviewer fix (R-pge1508)

The statement is restated in the house form of the landed affine base
(lem-pc-perfect-generation-affine-base, 773f742f5): a tied existential
`∃ P : schemeDerivedCategory X, Scheme.IsPerfect X P ∧ schemeDerivedQCohProperty X P ∧ …`;
generation in the sense of def-pc-generators written inline as
`∀ E : schemeDerivedQCohCategory X, IsZero E.obj ↔ ∀ n : ℤ, Subsingleton (P⟦n⟧ ⟶ E.obj)`;
the localizing clause stated in D(O_X): every triangulated, retract-closed, `Type u`-sum-closed
`Q : ObjectProperty (schemeDerivedCategory X)` with `Q P` contains every object of D_QCoh(X).
This removes the extra conjunct `(schemeDerivedQCohProperty X).IsTriangulated` and the
`∀ [htri]` instance binder. Equivalence with the node's subcategory reading: D_QCoh(X) is
triangulated and closed under the direct sums of D(O_X), so Q ∩ D_QCoh is localizing in
D_QCoh, and conversely a localizing subcategory of D_QCoh is one of D(O_X). The Worker report
and second reading above describe the delivered form.
