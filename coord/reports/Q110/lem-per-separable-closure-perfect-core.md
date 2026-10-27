## Worker report

The module `Sheaf.FieldTheory.SeparableClosurePerfectCore` states
`Field.separableClosure_perfect_core`, with its only proof `by sorry`. No definitions,
helper theorems, dependency repairs, new nodes, or statement corrections are needed.
Only the item's `lean` field changes. The statement is equality of subsets of `Ks`;
this is exactly the node's equality of the two subfields as subsets of the given closure.

Source read: ILO, Travaux de Gabber, Exposé IV, Lemma 3.2.2, printed pp. 55–56
(PDF pp. 61–62), including the definition in §3.2.1 and the full proof. The current
blueprint ancestor `lem-per-artin-gabber-affine-curve` and its proof were also read in
`literature/blueprint/latest/`; the item's field-theoretic statement is the ILO input
recorded by the existing DAG, not a change to that ancestor or unit.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A field `K`: `(K : Type u) [Field K]`.
- Characteristic `p > 0`: `(p : ℕ) [Fact p.Prime] [CharP K p]`. Positive characteristic
  of a field is prime, so this is precisely the node's range of characteristics.
- A separable closure of `K`: `(Ks : Type v) [Field Ks] [Algebra K Ks]
  [IsSepClosure K Ks]`. The algebra map of fields is injective. Mathlib's `IsSepClosure`
  gives both separable algebraicity over `K` and separable closedness. No finite degree,
  perfectness, or equality of field universes is assumed.
- The subfield `K_perf = intersection_n {a^(p^n) : a in K}` is the literal term
  `⨅ n : ℕ, (iterateFrobenius K p n).fieldRange`. The coercion of `fieldRange` to a set
  is `Set.range`; `iterateFrobenius K p n a` is definitionally `a ^ (p ^ n)`.
  The subfield intersection uses all natural numbers, including zero. Standard
  `Subfield` operations already construct this object, so no new notion is introduced.
- The inclusion of this subfield into `Ks` is exactly
  `((algebraMap K Ks).comp (⨅ n : ℕ,
  (iterateFrobenius K p n).fieldRange).subtype).toAlgebra`. The explicit `@separableClosure`
  argument uses this canonical composite; it does not quantify over another embedding
  or require an additional tower assumption.
- The subfield `S` of elements of `Ks` separable algebraic over that perfect core is
  Mathlib's `separableClosure` for that core and that canonical algebra structure.
  `mem_separableClosure_iff` identifies membership with `IsSeparable`; the latter
  includes algebraicity because the zero minimal polynomial is not separable.
- The conclusion `S = intersection_n {a^(p^n) : a in Ks}` is the displayed equality
  after coercing the relative separable closure to `Set Ks`, with right side
  `{x : Ks | ∀ n : ℕ, ∃ a : Ks, a ^ (p ^ n) = x}`. This is exactly membership in
  every indicated image. No extra conclusion is asserted.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs; the exact Mathlib match.
- `def-pd-separable-closure`: the recorded module
  `WeilConjectures.Mathlib.FieldTheory.IsSepClosed` is publicly imported. Its
  `IsSepClosure.exists_intermediateField_mem` and complete docstring were read; the
  docstring explicitly identifies the closure notion with Mathlib's `IsSepClosure`.
  The latter's fields and `isSepClosure_iff` were also read. The finiteness/colimit
  description is a property of this same closure, not extra input for this theorem.
- `def-weil-pbc-relative-separable-closure`: publicly imported
  `Mathlib.FieldTheory.SeparableClosure`, declaration `separableClosure` and
  `mem_separableClosure_iff`; this dependency has an exact Mathlib match, requiring
  no new Lean record or local copy.
- Standard constructions: `iterateFrobenius` from
  `Mathlib.Algebra.CharP.Frobenius`, and `RingHom.fieldRange`, `Subfield` intersections,
  and `Subfield.subtype` from Mathlib.Algebra.Field.Subfield.Basic.
- Proof dependencies with available modules are ordinary imports:
  `WeilConjectures.Mathlib.Algebra.CharP.Lemmas` (`iterateFrobeniusOfPrime`,
  def-weil-ring-frobenius), `Mathlib.FieldTheory.Perfect`
  (`Algebra.IsAlgebraic.perfectField`, lem-per-algebraic-extension-perfect),
  `Mathlib.FieldTheory.PurelyInseparable.PerfectClosure`
  (`minpoly.iterateFrobenius_of_isSeparable`, lem-per-minpoly-iterated-frobenius),
  and `Mathlib.FieldTheory.Separable` (`Polynomial.Separable`, `IsSeparable`,
  `Algebra.IsSeparable`, def-pc-separable-polynomial and
  def-weil-pbc-separable-algebraic-extension). The declaration docstring gives all
  four DAG proof steps, with their dependency ids. Already publicly imported proof
  dependencies are not duplicated as ordinary imports.

Edge cases checked before writing:

- `n = 0`: the iterated Frobenius is the identity, so its image is the whole field;
  the right-side root requirement is likewise automatic with `a = x`.
- `0` and `1`: both belong to every image and to the relative separable closure.
- `p = 2`: no odd-characteristic assumption occurs. Characteristic zero, `p = 0`,
  and `p = 1` are excluded exactly by the original positive-characteristic hypothesis.
- Perfect `K`, including a finite prime field: the core is all of `K`; its separable
  closure is perfect, so both sides are all of `Ks`, as expected.
- Imperfect `K`, for example a rational-function field over a finite field: the
  core is not silently replaced by the purely inseparable extension `perfectClosure`.
  No Frobenius-surjectivity hypothesis is imposed on `K` or `Ks`.
- A separably closed base is allowed with `Ks = K`; the assertion specializes to
  the same two descriptions of its perfect core.
- Field universes `u` and `v` are explicitly bound and independent; the core lives
  in the base universe and its embedding into `Ks` is written explicitly.

Searches, all run for this item through the prescribed tools:

- LeanFinder: "separable closure of the perfect core equals the intersection of
  iterated Frobenius images in a separable closure": 8 results, including
  `separableClosure_inf_perfectClosure`, `perfectClosure`,
  `perfectField_of_isSeparable_of_perfectField_top`, `perfectClosure.perfectRing`,
  `PerfectClosure.iterate_frobenius_mk`, `mem_perfectClosure_iff`,
  `perfectClosure.perfectField`, `separableClosure_le`; none states this equality.
  The `perfectClosure` results concern purely inseparable extensions, not the
  intersection of Frobenius images. Search digest `b840bb2da72fda84`.
- Loogle: `separableClosure, iterateFrobenius`: no results.
  Search digest `4f53cda18c2baa0c`.
- Mathlib grep, FieldTheory:
  `perfectCore|perfect_core|iInf.*[Ff]robenius|[Ff]robenius.*iInf`: no results.
  Search digest `4f53cda18c2baa0c`.
- LeanSearch: "In a separable closure the perfect core is the separable closure
  of the base field perfect core": 8 results, `IsSepClosure.recOn`,
  `separableClosure`, `PerfectClosure`, `IsSepClosure.isAlgClosure_of_perfectField`,
  `IsSepClosure.self_of_isSepClosed`, `IsSepClosure.of_isAlgClosure_of_perfectField`,
  `IsSepClosure.mk`, `SeparableClosure`; none is the theorem.
  Search digest `f9410fe450374131`.
- `rg` in project `WeilConjectures` and `Sheaf` for
  `perfectCore|perfect_core|separable.*[Cc]ore|[Cc]ore.*separable` found only unrelated
  core-named lemmas, not this statement. Broader field-theory perfectness searches
  found other perfectness results and the standard algebraic-extension theorem.
- `grep -rn 'lem-per-separable-closure-perfect-core'` in `WeilConjectures`: no hits.
- `rg 'separableClosure_perfect_core'` across Mathlib, `WeilConjectures`, `Sheaf`,
  and `dag/lean_names_upstream.json`: no prior declaration with this name.

No statement dispute, node fault, or dependency-interface defect was found. The prescribed
`scompile.py` check of the new theorem succeeded in both sandbox and library module modes
with no errors or warnings (1.4 s and 1.6 s). The delivery dry run checks the final imports
and metadata again. All files were written only in the assigned sandbox; no live Lean
sources or repository Git state were directly modified.

## Second reading by Q110

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
