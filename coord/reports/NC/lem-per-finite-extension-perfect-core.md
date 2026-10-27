## Worker report

The delivery states `Field.isAlgebraic_of_mem_perfectCore_of_finiteDimensional`
in `Sheaf.FieldTheory.FiniteExtensionPerfectCore`. Its sole theorem proof is
`sorry`; no theorem is proved. It also supplies the genuine subfield construction
`Field.perfectCore` in `Sheaf.FieldTheory.PerfectCore` under the new definition node
`def-per-field-perfect-core`. The item's statement and proof are unchanged.

Hypothesis and clause correspondence:

- The prime integer is `(p : ℕ) [Fact p.Prime]`.
- The two fields are `(K : Type u) (L : Type v) [Field K] [Field L]`.
  Both universes are explicit and independent.
- The inclusion `K ⊆ L` is `[Algebra K L]`; its unital algebra map is necessarily
  injective since its domain is a field. This permits every field embedding.
- Characteristic `p` of both fields is `[CharP K p] [CharP L p]`.
- The existence of a finite spanning family is `[FiniteDimensional K L]`, Mathlib's
  abbreviation for `Module.Finite K L`, not a finite-set assumption on the fields.
- For either field `E`, `perfectCore E p` is the infimum over all `n : ℕ` of
  `(iterateFrobenius E p n).fieldRange`. `iterateFrobenius` is definitionally the
  homomorphism `y ↦ y ^ (p ^ n)`; `RingHom.fieldRange` has carrier `Set.range`.
  Thus this is exactly the stated intersection as an actual `Subfield E`.
- Every element of the upper perfect core is represented by `(x : L)` and
  `(hx : x ∈ perfectCore L p)`.
- Algebraicity is the explicit conclusion `∃ P : Polynomial (perfectCore K p),
  P ≠ 0 ∧ P.eval₂ ((algebraMap K L).comp (perfectCore K p).subtype) x = 0`.
  The coefficient homomorphism is the canonical composite of the subfield inclusion
  into `K` with the given inclusion into `L`, so the equation is evaluated in `L`.
- There is no separability hypothesis. The conclusion imposes no finite degree
  bound or separability on the annihilating polynomial.

Dependencies and signatures read:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`, extends
  `CommRing` and `DivisionRing`, exactly the recorded field notion.
- `def-per-field-perfect-core`: `Field.perfectCore` in the sibling module above.
- The proof-only import `WeilConjectures.Mathlib.FieldTheory.IsSepClosed` provides
  the recorded `IsSepClosure.exists_intermediateField_mem` for
  `def-pd-separable-closure`: under `[IsSepClosure k ks]`, each `x : ks` belongs
  to a finite separable intermediate field. Its public imports provide
  `separableClosure : IntermediateField F E` (membership `IsSeparable F x`)
  for `def-weil-pbc-relative-separable-closure`, and `IsSepClosed.lift : L →ₐ[K] M`
  under `[Algebra.IsSeparable K L] [IsSepClosed M]` for the embeddings node.
- `Mathlib.FieldTheory.PurelyInseparable.Exponent` is imported for the bounded
  exponent leaf `IsPurelyInseparable.hasExponent_of_finiteDimensional` and
  `IsPurelyInseparable.HasExponent.has_exponent`. Its transitive Basic import gives
  the recorded instance `separableClosure.isPurelyInseparable` under algebraicity,
  as required by the separable-first node.
- `lem-per-separable-closure-perfect-core` currently has no Lean record or
  Mathlib match; it is a proof dependency only, so there is no module to import.
  Its mathematical statement is reproduced in the proof plan, not restated as an
  additional Lean theorem. No absent notion needed by this statement is deferred.

Source checked directly: ILO Travaux de Gabber, PDF pp. 61–62, printed pp. 55–56,
Exposé IV §3.2.1, Lemma 3.2.2 and Proposition 3.2.3(ii), including its reduction
through the bounded-height purely inseparable extension. §3.2.1 defines the
maximal perfect subfield by precisely this intersection. The theorem docstring
contains all three proof steps and names their DAG dependencies.

Edge cases checked before writing: `n = 0` contributes the identity-image subfield,
so it imposes no additional condition; `x = 0` admits the nonzero polynomial `T`;
`x = 1` admits `T - 1`; `L = K` gives the linear polynomial with coefficient `x`;
perfect base fields and finite fields have full perfect core; purely inseparable
finite extensions remain included, with their bounded exponent placing the upper
core in the lower field. Fields are nontrivial by the `Field` structure. No
characteristic-zero case was silently included: the node assumes prime `p`.
The two modules compile cleanly with `scompile.py`, separately in dependency order.
No statement dispute or source fault was found.

Searches for existing declarations (all service searches made through `msearch.py`):

- LeanFinder: “In a finite field extension of characteristic p every element in
  the intersection of all Frobenius images is algebraic over the intersection of
  all Frobenius images of the base field”. Eight hits, including
  `perfectClosure.isAlgebraic`, `PerfectClosure.instPerfectField`, and
  `Algebra.IsAlgebraic.perfectField`; these concern adjoining roots or algebraic
  extensions of already-perfect fields, not this intersection statement.
- Loogle: `perfectClosure, Subfield, iterateFrobenius`: zero hits.
- Mathlib grep: `perfectCore|perfectSubfield|perfect.*[Cc]ore|frobenius.*range|range.*frobenius`
  restricted to FieldTheory: two unrelated uses of a Frobenius range in
  `SeparableDegree.lean`, neither defines the intersection.
- LeanSearch: “perfect core of a field intersection of iterated Frobenius image
  subfields”. Eight hits, including `PerfectField`, `PerfectClosure`,
  `perfectClosure`, `Perfection.perfectRing`; none is the embedded perfect core.
- Additional LeanFinder: “The subfield of a field of positive characteristic
  consisting of elements that admit p power roots of every order, the intersection
  of the images of iterates of Frobenius”. Eight hits on perfect closures, prime
  subfields, and perfectness, no existing intersection subfield.
- Full Mathlib grep: `perfectCore|perfectSubfield|perfect.core|iInf.*frobenius|frobenius.*iInf`:
  zero hits. Inspected the existing `Ring.Perfection` implementation as well;
  its sequence construction is not this subfield of the original field.
- Project `rg` over both `lean/WeilConjectures` and `lean/Sheaf`, and the upstream
  names index: no field-theoretic `perfectCore` or `perfectSubfield`, and no
  declaration tagged with this item. Matches on perfect complexes are unrelated.
- DAG search over definitions for “perfect core”, “perfect-core”, and “maximal
  perfect subfield”: no existing definition node. Other statements that mention
  the notion introduce their intersections inline. `tools/blueprint_refs.py search
  'perfect core'` reports zero blueprint nodes. The ancestor tool gives
  `lem-per-artin-gabber-affine-curve`.

## New nodes

`def-per-field-perfect-core` defines, for a characteristic-`p` field and prime `p`,
the subfield consisting of the elements with `p ^ n`th roots for every natural `n`.
Source: ILO Exposé IV §3.2.1, printed p. 55. The real data is the lattice infimum
of existing Frobenius-image subfields, so it requires neither a choice nor a
postponed closure proof. The LeanSearch, LeanFinder, Loogle, Mathlib and project
searches above found no declaration of this notion; the DAG and blueprint searches
found no definition node. The new node is added to the item's statement dependencies.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
