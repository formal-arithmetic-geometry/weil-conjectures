## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteGeometricallyReducedEtale` states
`AlgebraicGeometry.etale_of_isFinite_of_geometricallyReduced` with a single `sorry`.
The node statement, accepted proof plan, dependencies and all other fields are unchanged.
No new definition or dependency repair is needed.

Clause-by-clause reading:
- The field k is `(k : Type u) [Field k]`.
- The scheme T is `(T : Scheme.{u})`; its given structure morphism to Spec k is
  `(f : T ⟶ Spec (CommRingCat.of k))`, without a chosen affine presentation.
- The finite-morphism hypothesis is `[IsFinite f]`.
- Geometric reducedness is `[GeometricallyReduced f]`, the exact recorded Mathlib
  notion from def-pc-geometrically-irreducible. Its class docstring quantifies over
  all field-valued points of the base. Over Spec k, `geometrically_iff_of_commRing`
  and `geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms` identify this
  with reducedness of the pullback along every `Spec.map (algebraMap k L)`.
  This uses precisely field extensions `[Field L] [Algebra k L]` and the canonical
  pullback from def-pc-base-change. The common arbitrary universe u is Mathlib's
  convention, not a restriction to finite or algebraic extensions.
- The conclusion that the given morphism is etale is `Etale f`.
- Empty T is allowed: there is no `Nonempty`, connectedness or integrality binder.
- There is no `PerfectField k`, characteristic restriction or extra assumption.

Dependency declarations used, read in their recorded sources:
- `Mathlib.Algebra.Field.Defs`: `Field` (line 180).
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`
  (lines 42, 74, 470, 479). The scheme and spectrum modules are exposed transitively
  by the public imports.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite` (line 39).
- `Mathlib.Algebra.Algebra.Defs`: `Algebra` (line 95), used by the interpretation
  of the existing geometric-reducedness class, not redefined.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: base-change conventions
  for `Limits.pullback f T.hom`, with the two projections; its recorded
  `Scheme.Modules.moduleBaseChange` is only the module clause and is not substituted
  for scheme base change.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral` imports the recorded
  `GeometricallyReduced` class from `Geometrically.Reduced` (line 44).
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale` (line 41).

The public imports expose the statement dependencies. Proof imports follow every
already stated proof dependency: `Properties` is exposed transitively; Artinian
and algebraic-closure leaves are imported through `Artinian.Module` and
`IsAlgClosed.AlgebraicClosure`; the remaining five project proof modules are
`SpecFiniteProductFields`, `FiniteAffineTensorBaseChange`,
`FiniteExtensionTensorAlgebraicClosureReduced`, `SeparableExtension`, and
`EtaleCoproductOfFiniteSeparableFields`. Their source signatures and docstrings
were read. The docstring reproduces all five accepted proof steps, including
canonical quotient components, separability and the empty-product case.

Edge cases checked before writing: T empty (coordinate ring zero, no maximal
ideals); T = Spec k (identity); a finite product of finite separable extensions;
a finite purely inseparable nontrivial extension of an imperfect field (excluded
by geometric reducedness, since algebraic-closure base change has nilpotents);
and k[epsilon]/epsilon² (excluded even before extension). These justify keeping
geometric reducedness rather than only reducedness and adding no perfectness.

Searches actually run on 2026-10-24:
- `msearch.py ... leansearch "A finite geometrically reduced scheme over a field
  is etale."`: 8 results including the etale definition and algebraic separability
  criteria; none is the scheme statement.
- `msearch.py ... leanfinder "A finite geometrically reduced scheme over an arbitrary
  field is etale."`: 8 results, including `Algebra.Etale.iff_exists_algEquiv_prod`
  and `Algebra.FormallyEtale.iff_exists_algEquiv_prod`; none proves the present
  scheme statement from geometric reducedness.
- `msearch.py ... loogle "AlgebraicGeometry.GeometricallyReduced,
  AlgebraicGeometry.Etale"`: 0 hits.
- `msearch.py ... grep "GeometricallyReduced|geometricallyReduced"
  AlgebraicGeometry/Morphisms`: 0 hits.
- Direct `rg` searches of Mathlib geometric and morphism files found the exact
  class definitions. Searches of both `lean/WeilConjectures` and `lean/Sheaf` for
  `GeometricallyReduced`, `geometrically reduced`, finite-etale statements and
  the item id found no exact statement. The closest was
  `AlgebraicGeometry.etale_of_isFinite_of_isReduced` in
  `WeilConjectures.WeilSheaf.VerdierDualFinite`, which requires `PerfectField K`
  and only reducedness; its full signature and proof were read. It cannot be
  recorded as this item because imperfect fields are allowed here.
- Direct searches of `dag/lean_names_upstream.json`, Mathlib and both project
  trees for the proposed declaration name found no collision.
- No released repair note exists for this item.

Sources opened: `literature/stacks-project/morphisms.tex` lines 8175–8210,
`lemma-etale-over-field` (02GL); `algebra.tex` lines 10360–10400,
`lemma-characterize-separable-field-extensions` (030W); and algebra's
`lemma-etale-over-field`, lines 39394–39436. The node explicitly synthesizes the
finite reduced Artinian decomposition with the separability test; it does not
assert that 030W alone covers characteristic zero. No statement fault was found.

## Second reading by NA

A second pass opened the copied node and delivered Lean module together. The
three mathematical hypotheses match exactly: field k, the given finite map
T → Spec k, and geometric reducedness of that map. The sole conclusion is etaleness
of the same f. The Lean neither replaces T by a supplied spectrum nor supplies
an affine decomposition as extra input. The absence of a nonempty-source or
perfect-field assumption preserves both explicit edge-case clauses. All binders
and the universe are explicit, and auto-bound implicits are disabled. The module
contains no definition and no proved theorem. The proof docstring matches the
node's five steps. No mismatch required a change. This is the dispatch worker's
second pass; the maintainer performs the independent review after delivery.
