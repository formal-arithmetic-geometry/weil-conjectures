## Worker report

The module `Sheaf.AlgebraicGeometry.AmpleExistenceFieldExtension` states
`AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_field_extension`, with its sole
proof `sorry`. No definition or helper theorem is introduced. The source is Stacks
Project, Varieties, Tag 0BDC, `lemma-ample-after-field-extension`, read directly in
`literature/stacks-project/varieties.tex:2740-2779`. Its statement and proof agree
with the DAG node. Only the item's `lean` field changes.

Hypotheses and conclusion, clause by clause:

- The field `k` is `{k : Type u} [Field k]`.
- The arbitrary field extension `K/k` is `{K : Type u} [Field K] [Algebra k K]`.
  Its actual structure map is `algebraMap k K`; no finiteness, algebraicity,
  separability, finite generation, or characteristic condition is assumed.
- The `k`-scheme is `{X : Scheme.{u}} (f : X ⟶ Spec (.of k))`. There is no
  finite-type, separatedness, properness, normality or Noetherian hypothesis.
- The scheme `X_K` is the chosen canonical fibre product
  `Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))`.
  This uses the specified `k`-algebra map, not an arbitrary unrelated morphism.
- The existence hypothesis is `hK : ∃ L : X_K.Modules, ∃ hL : L.IsInvertible,
  @IsAmple X_K L hL`, with the fibre product written in full in the file.
  `hL` supplies exactly the typeclass argument needed by the recorded absolute
  ampleness predicate. No module on `X` or descent datum is supplied as input.
- The conclusion is `∃ M : X.Modules, ∃ hM : M.IsInvertible, @IsAmple X M hM`.
  It asserts only existence of an absolutely ample invertible module, with no
  isomorphism between its pullback and the chosen `L`.

Recorded statement dependencies used, after reading their full signatures and
docstrings in the read-only live source:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`, with
  `algebraMap` specifying the homomorphism of fields.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`; its scheme
  existence instance is supplied by `Mathlib.AlgebraicGeometry.Pullbacks`.
- `def-sc-invertible-module`: `AlgebraicGeometry.Scheme.Modules.IsInvertible`,
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, the condition of being
  locally isomorphic to the structure module in the Zariski topology.
- `def-weil-pbc-ample-invertible-module`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple`,
  `WeilConjectures.AlgebraicGeometry.Ample`. This is `CompactSpace X` together
  with affine nonvanishing neighbourhoods of positive tensor-power sections.
  The similarly named `AlgebraicGeometry.IsAmple` in
  `WeilConjectures.AlgebraicGeometry.Modules.VeryAmple` was inspected and is not
  substituted: its definition requires a projective embedding of a tensor power.

All recorded proof-dependency modules are imported privately, including Mathlib
leaves: surjectivity and its base change, compact images, separatedness and
quasi-separatedness, affine transition limits, base change of limit cones,
affine and qcqs permanence, invertible and ample affine-limit descent, maximal
ideals, Zariski's lemma, closed immersions, restriction of ampleness, finite free
module properties, and finite locally free morphisms. The eight-step docstring
transcribes the node's proof, including the finite presentation in step 7 and
the final use of `lem-sfb-finite-locally-free-ample-existence`. That last node
has neither a Lean attachment nor a Mathlib match, so no import for it exists;
it is a proof dependency only, not a missing notion needed to type this statement.

Edge cases checked before writing:

- Empty `X` is permitted: no `Nonempty X` is required, and both sides use the
  same invertibility/ampleness definitions on the empty scheme.
- The identity extension `K = k` is permitted and imposes no extra constraint.
- Infinite algebraic extensions, transcendental extensions, and inseparable
  extensions are permitted by the unrestricted `Algebra k K` binder.
- Arbitrary positive characteristic and characteristic zero are included.
- Nonreduced schemes and schemes not of finite type are permitted. Quasi-compactness
  follows from the existence hypothesis and is not assumed separately on `X`.
- The ambient universe `u` is explicit and arbitrary; the fields and scheme are
  objects in one ambient universe, as required by the scheme category and its
  pullback API. There is no small test-object quantifier that could become vacuous.
- The conclusion has no compatibility clause for a supplied module; such a clause
  would incorrectly strengthen existence to descent of that module.

Searches performed with the prescribed `msearch.py` wrapper:

- LeanFinder: "If a scheme has an ample invertible module after an arbitrary field
  extension then it has an ample invertible module". Eight results concern affine
  morphism properties; none states this existence assertion.
- LeanSearch: "Existence of an ample line bundle descends along arbitrary extensions
  of the ground field". Eight results concern unramified/etale base change,
  valuative criteria, and intermediate fields; no exact statement.
- Loogle: `"IsAmple"`. Zero results.
- Mathlib grep: `ample.*field|field.*ample|exists.*[Aa]mple`, subdirectory
  `AlgebraicGeometry`. Two irrelevant comments about elliptic-curve normal forms.
- `rg` with these patterns and `theorem exists_.*isAmple`, `IsAmple.*pullback`,
  and ampleness/extension variants across `lean/WeilConjectures` and `lean/Sheaf`
  found other ample existence and pullback statements, but no arbitrary-field
  existence descent. In particular finite normal descent adds normality, and
  very-ample field extension is an ascent theorem about a different predicate.
- `grep -rn 'lem-sfb-ample-existence-field-extension' lean/WeilConjectures`
  found no match. The proposed theorem/module names also have no match in the
  project or `dag/lean_names_upstream.json`.

No statement dispute, missing notion, dependency interface repair, or statement
correction was needed. No released repair note exists for this item.

Validation: the prescribed `scompile.py Q71 lem-sfb-ample-existence-field-extension`
accepted the file both as a sandbox module and under its final library module name
(2.3 s and 2.1 s). There were no errors or unexpected warnings. The initial
elaboration failure was caused by the namespace's module `pullback`; qualifying
both fibre products as `Limits.pullback` resolved it. Both auto-implicit options
are disabled and every source line is at most 100 characters.

## Second reading by Q71

This is a separate self-audit, not a claim of an independent worker review: the
dispatcher brief prohibits starting other agents and assigns independent review
to the maintainer. Reopened the node and final source and compared all binders:
`Field k`, `Field K`, `Algebra k K`, `X`, and its structure map account for exactly
the input objects. The fibre product uses the actual algebra map; the dependent
existentials supply invertibility to absolute `IsAmple` on precisely that scheme.
The output existential uses the original `X`, and imposes no pullback equality.
The qualification of `Limits.pullback` is the only elaboration repair; no
mathematical hypothesis or conclusion changed. The source's generality is
preserved. The complete eight-step source/DAG proof remains in the docstring,
and the Lean proof remains exactly `sorry`.
