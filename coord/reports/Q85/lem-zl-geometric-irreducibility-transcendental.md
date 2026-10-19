## Worker report

The delivery states `AlgebraicGeometry.geometricallyIrreducible_transcendental_extension`
in `Sheaf.FieldTheory.GeometricIrreducibilityTranscendental`. The single theorem has
`by sorry` as its whole proof. There are no new definitions or dependency repairs.
Only the item's `lean` field changes.

Read Stacks `literature/stacks-project/algebra.tex`, lines 11340–11374, Tag 0G31,
and the following Tag 0G32, as well as the node's complete eight-step proof. The
source states the one-variable equivalence. The node additionally spells out its
finite iteration, including the empty family; the Lean includes both clauses.

Hypothesis and clause correspondence:

- A field extension `K/k` is `{k K : Type u} [Field k] [Field K] [Algebra k K]`.
  Its structure map is `algebraMap k K`; its scheme is exactly
  `Spec.map (CommRingCat.ofHom (algebraMap k K))`.
- Geometric irreducibility is the recorded Mathlib
  `AlgebraicGeometry.GeometricallyIrreducible` on this morphism. In particular it
  is not geometric reducedness or integrality. Its base-change irreducibility
  includes nonemptiness.
- The forward assumption is the premise of the first conjunct. It does not
  appear on the converse conjunct.
- A family over `K` lives in an arbitrary common ambient field `Ω`, with
  `[Algebra k Ω] [Algebra K Ω] [IsScalarTower k K Ω]`. These bind the compatible
  embeddings needed to speak about the same elements over both fields. They do
  not assume anything about the ambient extension beyond containing the family.
  `Ω : Type (max u v)` permits an ambient field larger than either original
  field, without vacuous quantification in a smaller universe.
- Finiteness is `(r : ℕ) (t : Fin r → Ω)`; independence over `K` is exactly
  `AlgebraicIndependent K t`. There is no `0 < r` condition.
- The two resulting fields are Mathlib's
  `IntermediateField.adjoin k (Set.range t)` and
  `IntermediateField.adjoin K (Set.range t)`. The displayed ring map is
  `IntermediateField.inclusion`, using `adjoin_le_iff.mpr (subset_adjoin ...)`
  to include the first field in the scalar restriction of the second. Scalar
  restriction changes its base, not its elements or operations. Hence this is
  the canonical inclusion `k(t₁,…,tᵣ) → K(t₁,…,tᵣ)`, not an arbitrary homomorphism.
  Its induced spectrum map is asserted geometrically irreducible.
- This generated-field description renders exactly the node's successive
  rational-function fields. For an independent family, evaluation of
  multivariate polynomials is injective; its fraction field identifies with
  the generated intermediate field (`AlgebraicIndependent.aevalEquivField`,
  Mathlib/RingTheory/AlgebraicIndependent/Adjoin.lean:41). Adjoining one variable
  at a time gives the same field by `IntermediateField.adjoin_adjoin_left`.
  Each next variable is transcendental over the preceding generated field
  by clearing denominators. Thus the notation describes the same objects,
  including for families of actual elements in a larger field; it does not
  assert a statement only for formal variables.
- The second conjunct is the converse implication for one formal indeterminate.
  `RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap k K)) ...` is precisely
  `k(t) → K(t)`, applying the field embedding to numerator and denominator
  coefficients and fixing `t`. Its nonzero-divisor condition is the existing
  theorem `nonZeroDivisors_le_comap_nonZeroDivisors_of_injective` applied to
  `Polynomial.map_injective _ (algebraMap k K).injective`.
  The premise is geometric irreducibility of this spectrum map, and its
  conclusion is geometric irreducibility of the original extension.

Dependency declarations used (all source signatures and docstrings read):

- `def-pc-field-extension`: `Algebra`, module `Mathlib.Algebra.Algebra.Defs`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`, module
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-pc-geometrically-irreducible`: `AlgebraicGeometry.GeometricallyIrreducible`,
  imported through the recorded module `Mathlib.AlgebraicGeometry.Geometrically.Integral`;
  its definition is in `Mathlib.AlgebraicGeometry.Geometrically.Irreducible`.
  Also read `geometrically_iff_of_commRing` and the chosen-pullback variant.
- `def-kun-transcendence-degree`: the node's algebraic-independence clause is
  Mathlib `AlgebraicIndependent`; imported recorded module
  `Mathlib.RingTheory.AlgebraicIndependent.Basic` (also defining `Algebra.trdeg`).
  The statement needs independence, not a transcendence-degree bound.
- `def-weil-rational-function-field`: `RatFunc` and `RatFunc.mapRingHom`, module
  `Mathlib.FieldTheory.RatFunc.Basic`, following the node's `mathlib_match`.
  The structure itself is in `RatFunc.Defs`, with its fraction-ring instance in
  `RatFunc.Basic`.

The additional `public import` of
`Mathlib.FieldTheory.IntermediateField.Adjoin.Defs` supplies the existing generated
fields and their inclusion. Proof-only imports provide the recorded affine
pullback, localization, tensor exactness and nontriviality, minimal-prime and
dense-range tools. All proof dependencies are Mathlib leaves. No project-side
prerequisite declaration is omitted or duplicated.

Edge cases checked before writing:

- `r = 0`: `Fin 0` is empty, independence holds for the faithful field embedding,
  and both adjoins are bottom intermediate fields, canonically isomorphic to the
  original fields. The asserted morphism is the original field extension under
  those identifications.
- `r = 1`: gives the ascent of Tag 0G31 and the ambient-element use of Tag 0G32.
- `k = K`: no strictness of either field embedding is imposed; all conclusions
  remain valid.
- Finite base fields, positive characteristic, inseparability, and extensions
  not finitely generated are all included. No separability or perfectness occurs.
- Fields are nontrivial by `Field`; there is no spurious zero-ring or empty-spectrum
  case. Geometric irreducibility retains the nonempty clause.
- The converse premise is independent of the forward assumption, so descent is
  not made tautological by assuming its conclusion.

Searches for an existing declaration:

1. `msearch.py ... leanfinder "A field extension K/k is geometrically irreducible
   if and only if K(t)/k(t) is geometrically irreducible; finite algebraically
   independent families"`: 8 hits about polynomial irreducibility, geometric
   reducedness and formal smoothness; no matching theorem.
2. `msearch.py ... leansearch "Geometric irreducibility of field extensions is
   invariant under simultaneous purely transcendental extension"`: 8 hits about
   polynomial irreducibility, purely inseparable extensions and geometric
   reducedness; no matching theorem.
3. `msearch.py ... loogle "AlgebraicGeometry.GeometricallyIrreducible, RatFunc"`:
   0 hits.
4. `msearch.py ... grep "GeometricallyIrreducible|geometricallyIrreducible"
   FieldTheory`: 0 hits.
5. `rg` of `GeometricallyIrreducible|geometrically irreduc|AlgebraicIndependent|RatFunc`
   in the source repository and `lean/Sheaf`: found the shared independence,
   rational-function and geometric irreducibility APIs, but no simultaneous
   transcendental-extension theorem. Nearby `FieldExtensionGeometricallyIrreducible`
   proves an unrelated algebraic-closure criterion, not this assertion.
6. Blueprint-id searches in the source repository and `lean/Sheaf`, and the
   candidate name search including `dag/lean_names_upstream.json`, found no existing
   statement or duplicate declaration. DAG-id hits were the node and its two citers.
7. Read the exact definitions and full signatures of `IntermediateField.adjoin`,
   `inclusion`, `restrictScalars`, `AlgebraicIndependent.aevalEquivField`,
   `RatFunc.mapRingHom`, `Polynomial.map_injective`, and the nonzero-divisor map
   theorem. These already give the canonical constructions; no new helper notion
   is needed.

Validation: the prescribed `scompile.py` compiled this module separately, both
as a sandbox and at its library path, without errors or warnings. No statement
fault or disputed assertion was found.

## Second reading by Q85

This is the author's second reading, not an independent agent review: the
launch brief forbids starting another agent and reserves independent review to
the maintainer. Reopened the node and the complete final Lean signature. The
outer `And` preserves the independently conditional ascent and descent clauses.
The first premise is exactly the original spectrum-map geometric irreducibility;
its finite-family quantifier permits `r = 0`, uses independence over `K`, and
concludes on the inclusion of the same generated fields. The codomain scalar
restriction has exactly the underlying field `K(t₁,…,tᵣ)`, and `inclusion` fixes
the represented elements. The second implication uses the rational coefficient
extension fixing the single variable, and concludes on the original map.
Reviewed the compatible ambient-field tower as the data needed to give meaning
to adjoining one family to both fields; no mathematical extra hypothesis is
introduced. Expanded the ambient universe to `max u v` before final compilation
to permit arbitrarily larger ambient extensions. No node statement correction,
new definition, private duplicate, hidden `let`, unbound universe or missing
clause was found. The docstring follows all eight proof steps, including the
nonzero-localization and converse injectivity arguments.
