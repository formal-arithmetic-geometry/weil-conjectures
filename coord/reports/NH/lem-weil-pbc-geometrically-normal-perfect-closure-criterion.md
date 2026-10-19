## Worker report

The module `Sheaf.RingTheory.GeometricallyNormalPerfectClosureCriterion` states
`Algebra.normal_tensor_perfectClosure_iff`, with its proof deferred by `sorry`.
No definitions or dependency modules are added. The node is unchanged apart from `lean`.

Hypothesis and conclusion correspondence:

- The field k is `(k : Type u) [Field k]`.
- The arbitrary commutative k-algebra A is `(A : Type v) [CommRing A] [Algebra k A]`.
- The extension P/k is `(P : Type w) [Field P] [Algebra k P]`.
- The number q is `ringExpChar k`: Mathlib defines this as `max (ringChar k) 1`,
  hence 1 in characteristic zero and the characteristic prime in positive characteristic.
- Every x has a q-power in k is exactly `hpower`: for every `x : P`, there are `n : ℕ`
  and `a : k` such that `algebraMap k P a = x ^ (ringExpChar k ^ n)`.
  Membership in k means membership in this injective algebra map's image.
- Perfectness is `[PerfectField P]`. Its irreducible-polynomial definition is equivalent
  to Frobenius surjectivity: `PerfectField.toPerfectRing` gives bijective Frobenius;
  `PerfectRing.ofSurjective` and `PerfectRing.toPerfectField` give the converse.
  Characteristic-zero fields are automatically perfect (`PerfectField.ofCharZero`).
- Clause (1) is the left side of `↔`: all prime localizations of `P ⊗[k] A` are domains
  and integrally closed. Both properties are retained explicitly.
- Clause (2) is the right side: for every field `E` with a k-algebra structure, every
  prime localization of `E ⊗[k] A` is a domain and integrally closed.
  E lives in `Type (max u v w t)`: the test universe is at least the base, algebra and
  perfect closure universes, and t is arbitrary. Smaller extensions can be lifted;
  ring isomorphisms preserve the displayed condition. No test universe is below k.
- There is no finite-type, Noetherian, domain, or nonzero assumption on A.

Dependency declarations used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-pc-field-extension`: `Algebra`, Mathlib.Algebra.Algebra.Defs; the specified
  extension map is `algebraMap`.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`,
  Mathlib.LinearAlgebra.TensorProduct.Defs. Mathlib.RingTheory.TensorProduct.Basic
  supplies `Algebra.TensorProduct.instCommRing` and the canonical algebra structure.
- `def-weil-pbc-normal-ring`: the prescribed inline conjunction of `IsDomain`
  (Mathlib.Algebra.Ring.Defs), `Localization.AtPrime`
  (Mathlib.RingTheory.Localization.AtPrime.Basic), and `IsIntegrallyClosed`
  (Mathlib.RingTheory.IntegralClosure.IntegrallyClosed). This uses the recorded
  inline form, without introducing another normal-ring predicate.

Recorded proof dependencies with available project modules are imported without `public`:
`Sheaf.FieldTheory.MakeSeparable`
(`Algebra.exists_finite_purelyInseparable_separable_extension`),
`Sheaf.FieldTheory.SeparableExtensionFractionFieldOfSmoothAlgebra`
(`FieldTheory.exists_smooth_subalgebra_fraction_field`),
`Sheaf.RingTheory.SmoothNormalRing` (`RingHom.Smooth.isNormalRing`), and
`Sheaf.RingTheory.FilteredColimitNormalRing` (`CommRingCat.isNormal_of_filtered_colimit`).
Localization base change is `IsLocalization.tensor`, imported through
`Mathlib.RingTheory.Localization.BaseChange`; tensor pushout maps are in the public
TensorProduct.Basic import. Normal-ring-field-extension-descent has no recorded Lean module
in the base and therefore no import is available. Smooth base change/composition are already
reachable via the proof modules. No import cycle is introduced.

Source and edge checks: read algebra.tex, lemma-geometrically-normal (037Z), including
all four conditions and its proof, and lemma-perfection (046W). The source imposes no
finiteness or nonzero condition. If A is the zero ring, each tensor algebra is zero and
has no prime ideals, so both sides are vacuous. For characteristic zero, q = 1 and
hpower says the image of k is all P; perfectness is automatic. For positive characteristic,
n = 0 is allowed and Frobenius surjectivity supplies every iterated root. The tensor
order is P/E first and A second, exactly as in the statement. Separate universes for
k, A and P do not exclude larger algebras or perfect closures. No statement fault found.

Searches for reuse (performed with msearch.py, and direct source inspection):

- LeanSearch: “An algebra is geometrically normal if and only if its tensor product
  with a perfect closure is normal”: service unavailable (Internal Server Error).
- LeanFinder: “Normality of an algebra after tensoring with a perfect purely inseparable
  extension is equivalent to normality after every field extension”: eight results;
  these concern normal field extensions and geometrically reduced algebras, not normal rings.
- Loogle: `"IsIntegrallyClosed", "TensorProduct"`: zero hits.
- Mathlib grep: `GeometricallyNormal|IsIntegrallyClosed.*Perfect|Perfect.*IsIntegrallyClosed`:
  zero hits.
- Direct rg over WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for
  `GeometricallyNormal|geometrically_normal|perfect.*[Nn]ormal|[Nn]ormal.*perfect`
  and the item id: only unrelated normalized complexes, normalized curves, and
  geometric-integrality docstrings; no declaration of this criterion.
- Inspected the full definitions and docstrings of Field, Algebra, TensorProduct,
  IsIntegrallyClosed, Localization.AtPrime, PerfectField and ringExpChar in the pinned
  Mathlib sources; inspected the recorded proof-module declarations and docstrings.

Validation: server-only single-file scompile.py and deliver2.py --no-push (results recorded
by the tools). The sole intended sorry is the named theorem above. Second reading remains
for the independent reader.


## Second reading by NH

I independently read the item node, its eight proof steps, all four statement-dependency
records, the sandbox Lean module, and the pinned Mathlib declarations they name. I read
Stacks algebra.tex, lemma-geometrically-normal (037Z), including its section introduction,
all four conditions and the proof, and lemma-perfection (046W) with definition-perfection.
The section imposes no ambient Noetherian, finite-type, domain or nonzero hypothesis.
No new definition nodes, dependency modules, or statement correction are present.

Object/hypothesis/conclusion inventory and correspondence (each passes H3):

1. Ground field k: `(k : Type u) [Field k]`. Mathlib's `Field` extends the commutative
   ring and division-ring structures, including nontriviality. This is def-weil-field.
2. Arbitrary commutative k-algebra A: `(A : Type v) [CommRing A] [Algebra k A]`.
   No additional instance restricts A. Algebra's `algebraMap` and scalar compatibility
   supply exactly the given unital k-algebra structure.
3. Field extension P/k: `(P : Type w) [Field P] [Algebra k P]`. This is precisely the
   recorded def-pc-field-extension, not a finite or algebraic extension substituted for it.
4. Characteristic exponent q: `ringExpChar k`, defined as `max (ringChar k) 1`.
   Its `eq_one` and `eq` lemmas identify it with 1 in characteristic zero and p in
   characteristic p. There is no fixed or excluded prime characteristic.
5. Pure power hypothesis: `hpower : ∀ x : P, ∃ n : ℕ, ∃ a : k,
   algebraMap k P a = x ^ (ringExpChar k ^ n)`. The existential a expresses membership
   in the image of k; the field map is injective. The dependence n on x is retained.
6. Perfectness: `[PerfectField P]`. I checked its irreducible-polynomial definition,
   `PerfectField.toPerfectRing`, `PerfectRing.toPerfectField`, and `ofCharZero`.
   Thus it is equivalent to the source's Frobenius-surjectivity requirement in positive
   characteristic and imposes nothing extra in characteristic zero. Together with item 5
   this specifies the perfect closure characterized in 046W.
7. Condition (1): the left side quantifies `p : Ideal (P ⊗[k] A)` with `[p.IsPrime]`
   and asserts both `IsDomain (Localization.AtPrime p)` and
   `IsIntegrallyClosed (Localization.AtPrime p)`. I checked the actual tensor quotient,
   algebra tensor ring structure, prime-complement localization and fraction-ring integral
   closure definitions. This uses exactly the dependency's prescribed inline normal-ring
   form; neither domainhood nor integral closedness is silently omitted.
8. Condition (2): after `↔`, `∀ (E : Type (max u v w t)) [Field E] [Algebra k E]`,
   the identical normal-ring condition on `E ⊗[k] A`. The field structure and extension
   structure are quantified before its primes. Both implications are present. Universes
   u, v, w, t are explicitly declared; there are no unbound binders. Arbitrary t permits
   arbitrarily large test extensions. Smaller extensions, including P and k, lift into
   this universe, and ring equivalences transport the normal-localization condition.
   In particular the right-hand condition is not vacuous for universe-size reasons.

Edge cases: A may be the zero ring: tensors are zero, there are no prime ideals, and
both clauses hold vacuously. A need not itself be a domain. Fields are nonzero as in the
source; empty schemes and index sets are not objects quantified in this statement.
The exponent n = 0 is included by `ℕ`; q^0 = 1. In characteristic zero hpower forces
P to be the image of k. In positive characteristic the field map preserves characteristic,
and perfectness supplies the iterated Frobenius roots. Tensor order is P/E first, A second.
The independent universes for k, A, P and the unrestricted test universe exclude no case.

Independent reuse searches (2026-10-15), using different wording from the worker:

- LeanSearch via msearch.py: "Normality after tensoring with a perfect closure is equivalent
  to normality after every field extension". Service unavailable (Internal Server Error);
  this is not evidence of absence.
- LeanFinder via msearch.py: "Geometric normality can be tested after base change to a
  perfection of the ground field". Eight hits, concerning geometric reducedness,
  formally smooth extensions, and scheme normalization, not normality of all prime
  localizations of arbitrary algebras. In particular `isGeometricallyReduced_iff` asserts
  reducedness, and cannot replace this criterion.
- Loogle via msearch.py: `"Localization.AtPrime", "PerfectField"`: zero hits.
- Direct rg on pinned Mathlib, WeilConjectures, project lean/Sheaf and the upstream-name
  index for `geometricallyNormal|geometric_normal|normal_tensor|normal.*perfection|` and
  `perfection.*normal|IsIntegrallyClosed.*[Tt]ensor|[Tt]ensor.*IsIntegrallyClosed`:
  only an unrelated geometric-integrality docstring. No reusable criterion found.

H4/H5/H6/H8/H9: no replacement notion or hollow data is introduced; the sole new
statement has precisely a `by sorry` proof. Source and blueprint markers are present in
both docstrings. The theorem docstring follows all eight node proof steps, naming the
same descent, make-separable, smooth-fraction-field, smooth ascent, localization and
filtered-colimit tools. Recorded proof-module imports are consistent with that route.
There are no local definitions, notations, instances, hidden lets, or additional claims.
The node's lean.statement is verbatim the theorem signature before `:= by`.

Mismatches found: none. I preserved the Lean and node record unchanged and appended
this independent review only. Validation: scompile.py server-only single-file compile
passed (nice 19, two threads, 60-second per-file limit), with no diagnostic output.
