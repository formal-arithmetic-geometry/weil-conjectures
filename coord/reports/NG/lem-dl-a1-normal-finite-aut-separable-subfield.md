## Worker report

Item: `lem-dl-a1-normal-finite-aut-separable-subfield` (NG, stage 2).

The module `Sheaf.FieldTheory.NormalFiniteAutSeparableSubfield` states
`separableClosure.finiteDimensional_of_normal_of_finite_aut`. Its only proof is
`sorry`, as required for stage 2. No definitions or helper assertions are added.
The node copy changes only `lean`; there is no statement correction, disputed
statement, dependency-interface repair, or new node.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The fields k and E are `(k : Type u) (E : Type v) [Field k] [Field E]`, with
  independent explicitly declared universes `u v`.
- The inclusion/field extension k ⊆ E is `[Algebra k E]`: the structure map is
  `algebraMap k E`, injective because its source and target are fields.
- The assertion that every element of E is algebraic over k and the assertion
  that every minimal polynomial splits in E are together `[Normal k E]`.
  The full definition in `Mathlib.FieldTheory.Normal.Defs` extends
  `Algebra.IsAlgebraic k E` and has field
  `splits' (x : E) : Polynomial.Splits ((minpoly k x).map (algebraMap k E))`.
  Thus bundling the two hypotheses neither omits algebraicity nor assumes that
  the whole extension is finite, separable, or Galois.
- The finite group Aut_k(E) is `[Finite (E ≃ₐ[k] E)]`. The type `AlgEquiv`
  consists of ring equivalences commuting with the structure map from k;
  its elements are precisely the field automorphisms fixing k. `Finite`
  expresses finiteness without choosing or requiring an enumeration.
- The specified subfield E_s is exactly the existing Mathlib intermediate
  field `separableClosure k E`, not an abstract separable closure or an
  arbitrary separable subfield. Its carrier is `{x : E | IsSeparable k x}`;
  `IsSeparable k x` means `Polynomial.Separable (minpoly k x)` and implies
  algebraicity. This is the dependency's recorded notion verbatim.
- The conclusion E_s/k is finite-dimensional is
  `FiniteDimensional k (separableClosure k E)`. This is Mathlib's finite-module
  predicate on this very subfield, not an inequality for Nat-valued finrank
  (which would not establish finiteness).
- The clause “No finite-dimensionality of E/k is assumed” is respected:
  there is no `FiniteDimensional k E` hypothesis, and the docstring makes
  this scope explicit.

Statement dependencies read and used:

- `def-pc-field-extension`: `Algebra` in
  `Mathlib.Algebra.Algebra.Defs`, together with `Field` structures. Its recorded
  declaration and docstring were read; this import is public.
- `def-weil-pbc-relative-separable-closure`: its usable `mathlib_match` is
  `separableClosure` in `Mathlib.FieldTheory.SeparableClosure`; its definition
  and `mem_separableClosure_iff` were read. It has no Lean record and needs no
  repair. This import is public.

Other statement vocabulary is Mathlib's `Normal`, `AlgEquiv`, `Finite`, and
`FiniteDimensional`; the definition and docstrings of `Normal`, `AlgEquiv`,
`IsSeparable`, and `FiniteDimensional` were inspected. `Normal.Defs` is a
public import because normality appears in the signature.

The proof dependencies were also read. They are all already matched to
Mathlib declarations, imported without `public` when used only in the proof:

- `lem-weil-pbc-algebraic-generators-finite-extension`:
  `IntermediateField.finiteDimensional_adjoin` in
  `Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`.
- `lem-weil-pbc-finite-separable-extension-primitive-element`:
  `Field.exists_primitive_element` in `Mathlib.FieldTheory.PrimitiveElement`.
- `lem-weil-pbc-simple-algebraic-extension-power-basis`:
  `IntermediateField.adjoin.powerBasis`, `adjoin.finiteDimensional`, and
  `adjoin.finrank` in `Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`.
- `def-weil-pbc-separable-algebraic-extension`: `Algebra.IsSeparable` and
  `IsSeparable` in `Mathlib.FieldTheory.Separable`.
- `lem-pc-algebraic-closure-exists-unique`: `AlgebraicClosure` in
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` and `IsAlgClosure.equiv`
  in `Mathlib.FieldTheory.IsAlgClosed.Basic`, imported through that module.
- `lem-pc-separable-polynomial-distinct-roots-alg-closed`:
  `Polynomial.card_rootSet_eq_natDegree` and `Polynomial.nodup_roots` in
  `Mathlib.FieldTheory.Separable`, with the splitting/factorization API that
  module and `IsAlgClosed.AlgebraicClosure` import.
- `lem-weil-pbc-normal-extension-conjugate-by-automorphism`:
  `minpoly.exists_algEquiv_of_root'` in `Mathlib.FieldTheory.Normal.Basic`.

The declaration docstring carries all six proof steps with their DAG ids:
finite generation inside E_s; primitive element and its minimal-polynomial
degree; counting roots after algebraic closure and normality; surjectivity
from automorphisms to roots; maximal finite-subextension degree and basis
argument; and E_s = F₀. This preserves the supplied proof route.

Source check: read `literature/stacks-project/fields.tex`,
`lemma-separable-first` (030K), `lemma-separable-degree` (09HJ),
`lemma-lift-maps` (0BME), `lemma-normal-embeddings-differ-by-aut` (0BR4),
and `literature/stacks-project/pione.tex`,
`lemma-inertia-invariants-etale` (0BST), especially the second reduction
paragraph. The lifting and conjugacy results allow infinite algebraic normal
extensions; the finite-embedding count is only applied to finite intermediate
extensions. No source-based statement change is necessary.

Edge cases checked before writing:

- E = k: the automorphism group is a singleton, E_s = E, and the conclusion
  says the base field has dimension one over itself.
- Purely inseparable algebraic extensions, including infinite ones in
  positive characteristic: they are normal, have only the identity
  k-automorphism, and E_s is the base field. These are retained.
- Finite normal extensions with or without a purely inseparable part are
  retained; no perfectness or characteristic restriction is imposed.
- If E/k is separable as well as normal, E_s = E and the conclusion asserts
  finiteness of E/k, as the theorem should. Separability is not assumed.
- The identity automorphism exists for every field extension, so the finite
  group has cardinality at least one; the maximum-degree proof never takes a
  maximum of an empty family, since the base field is an intermediate field.
- Infinite separable subfields are exactly what the conclusion excludes,
  rather than being excluded by an extra hypothesis. Both fields can lie in
  different universes. The field axioms exclude the zero ring appropriately.

Searches for an exact existing statement:

1. `msearch.py ... leanfinder` with query
   “An algebraic normal field extension with finite automorphism group has
   finite dimensional relative separable closure”: 8 hits, including
   `separableClosure.isGalois`, `normalClosure.is_finiteDimensional`,
   `IsSepClosure.isGalois`, `FiniteGaloisIntermediateField.finiteDimensional`,
   and `separableClosure.isPurelyInseparable`. None states this implication:
   Galoisness alone is not finiteness, and finite normal closure requires a
   finite-dimensional starting extension.
2. `msearch.py ... loogle 'Normal, separableClosure, Module.Finite'`:
   successful search with zero hits.
3. `msearch.py ... leansearch` with the same natural-language query:
   8 hits for the relative separable closure, its separability/algebraicity,
   and separable closures. None has the finite-automorphism hypothesis or
   this finite-dimensionality conclusion.
4. `msearch.py ... grep` in `FieldTheory`, query
   `finiteDimensional.*separableClosure|finite.*separableClosure|algHomEquivAut|cardinal_eq_of_isSeparable`:
   7 hits. Inspected `Normal.algHomEquivAut` (an equivalence between embeddings
   and automorphisms under normality) and the embedding-cardinal formulas
   `Field.Emb.cardinal_eq_of_isSeparable` / `cardinal_eq` in
   `Mathlib.FieldTheory.CardinalEmb`; these are ingredients requiring an
   additional cardinal/rank argument, not an exact existing statement.
5. `rg` in project `lean/WeilConjectures` and `lean/Sheaf`, both for
   `separableClosure` and for the finite-dimensionality/finiteness/name
   patterns: the nearby theorem `finite_separable_closure` in
   `Sheaf.FieldTheory.FiniteSeparableClosure` assumes a finitely generated
   field extension and also concludes geometric irreducibility; it is not
   this theorem. The other finite-automorphism hit is a finite orbit-closure
   lemma about sheaf sections in `WeilConjectures.AlgebraicGeometry.Sites.SplitSheaf`,
   not a field-dimensionality statement. Direct grep for this item's id
   under `lean/WeilConjectures` found no declaration. Searching
   `dag/lean_names_upstream.json` for the proposed theorem name and the
   finite-normal-automorphism name fragments found no collision.

The four msearch invocations are recorded verbatim by the wrapper in the
sandbox's `searches.jsonl`. No exact statement was found, so a new theorem
statement is necessary; all notions are reused.

Validation: `scompile.py NG lem-dl-a1-normal-finite-aut-separable-subfield
<module>` compiled both the sandbox and library-module forms cleanly
(1.7 s and 1.8 s respectively), with no errors or warnings. Every variable
and universe is explicitly bound. Delivery preflight is run after this report.

## Second reading by NG

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
