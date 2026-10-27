## Worker report

The module `Sheaf.FieldTheory.FinitelyGeneratedResiduePerfectCore` states
`isSeparable_of_fg_of_forall_exists_pow_eq`, with its entire proof `sorry`.
There are no new definitions or auxiliary theorems. The node changes only in `lean`;
its accepted statement, split and dependency lists are preserved.

### Exact correspondence with the statement

- A prime `p`: `(p : ℕ) [Fact p.Prime]`.
- Fields `k ⊆ L`: `{k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]`.
  The inclusion is the injective `algebraMap k L`, exactly the field-extension
  dependency's recorded encoding. The field universes `u` and `v` are independent.
- Both fields have characteristic `p`: `[CharP k p] [CharP L p]`.
- Surjectivity of `a ↦ a^p` on the base: the explicit hypothesis
  `hperfect : Function.Surjective (fun a : k ↦ a ^ p)`.
- Finite generation as a field: `hfg : (⊤ : IntermediateField k L).FG`.
  Mathlib defines this as a finite set whose intermediate-field adjunction is top;
  it allows the empty set. No algebra-finite-type assumption is imposed.
- The stated intersection `L_perf = ⋂ n ≥ 0, {y^(p^n) : y ∈ L}` is expressed
  pointwise by `(x : L) (hx : ∀ n : ℕ, ∃ y : L, y ^ (p ^ n) = x)`.
  Membership in an intersection means membership for every natural `n`, and
  membership in each image means exactly the existential displayed. A new
  subfield construction is unnecessary to state this elementwise conclusion.
- Every such element is separable algebraic over `k`: `IsSeparable k x`.
  This is precisely the elementwise definition recorded on
  `def-weil-pbc-separable-algebraic-extension`. Its algebraic clause is built in:
  `IsSeparable` is separability of `minpoly k x`; nonintegral elements have zero
  minimal polynomial, which is not separable. See `IsSeparable.isIntegral` in
  the same Mathlib file (and its consequence `IsIntegral.isAlgebraic`). Thus no
  algebraicity clause is omitted or replaced by a hypothesis about all of `L`.
- Algebraic `L/k` and an empty field-generating set are included: there is no
  positive transcendence-degree or nonempty-generating-set binder.

### Dependency declarations read and used

Statement dependencies:

- `def-weil-field`: `Field` in `Mathlib.Algebra.Field.Defs`, read with its docstring.
- `def-pc-field-extension`: `Algebra` and `algebraMap` in
  `Mathlib.Algebra.Algebra.Defs`, reached through the public field imports.
- `def-weil-pbc-separable-algebraic-extension`: `IsSeparable` and
  `Algebra.IsSeparable` in `Mathlib.FieldTheory.Separable`. The node itself
  concerns individual elements, so its documented elementwise predicate
  `IsSeparable k x` is used, rather than asserting that all of `L/k` is algebraic.

Additional statement encodings are Mathlib's `CharP` in
`Mathlib.Algebra.CharP.Defs` and `IntermediateField.FG` in
`Mathlib.FieldTheory.IntermediateField.Adjoin.Defs` (both read in the source).

Every recorded proof dependency was inspected. Their existing declaration modules
are imported privately: `exists_finset_isTranscendenceBasis` in
`Mathlib.FieldTheory.FinTrdeg`; `IntermediateField.finiteDimensional_adjoin` in
`Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`; `IsTranscendenceBasis` in
`Mathlib.RingTheory.AlgebraicIndependent.Defs`; `LaurentSeries` in
`Mathlib.RingTheory.LaurentSeries`; `HahnSeries.ofPowerSeries` and
`HahnSeries.ofPowerSeries_injective` in `Mathlib.RingTheory.HahnSeries.PowerSeries`;
`HahnSeries.instField` in `Mathlib.RingTheory.HahnSeries.Summable`; and
`MvPowerSeries.map_frobenius_expand` in `Mathlib.RingTheory.MvPowerSeries.Expand`.
The separability dependency already has its public import.
`lem-per-finite-extension-perfect-core` currently has no Lean record, Mathlib
match, or closed upstream declaration; it is used only by the future proof and
is named in the docstring. There is no absent object required to type this item,
so no prerequisite module is needed in this statement delivery.

The theorem docstring carries all six accepted proof steps, including the Laurent
shift, the support divisibility argument, the embedding into iterated Laurent
series, the finite-extension core theorem and the perfect-base minimal-polynomial
argument. Read the source PDF directly at PDF pp. 61--62 (printed pp. 55--56):
ILO Expose IV 3.2.1 defines the exact separable-algebraic Epp condition;
Proposition 3.2.3(ii),(iii) supplies the finite-extension and Laurent-series
inputs. The node's finite-transcendence-basis reduction supplies its finitely
generated extension case. No source-based correction is needed.

### Edge cases checked before writing

- `n = 0`: `p^0 = 1`, so every `x` has the required zeroth root `x`.
- `x = 0`: all roots can be zero; its minimal polynomial is linear and separable.
  No binder excludes zero, one, or elements in the image of `k`.
- `L = k` with an empty generating set: adjoining the empty set gives the base
  intermediate field, which is top for the identity extension. Repeated base
  Frobenius surjectivity supplies the roots, and each base element is separable.
- Algebraic finitely generated extensions: these are finite and separable over
  the perfect base; no transcendence or nonempty-basis assumption excludes them.
- `L = k(t)`: the support calculation places its perfect core in `k`.
  A finite inseparable extension of a rational subfield is also permitted;
  separability of `L/k(t)` is not an assumption.
- `p = 2` is included, while `p = 0` and `p = 1` are correctly excluded by
  primality. No characteristic-zero case is claimed.
- Independent field universes and the unrestricted natural root index avoid
  any size restriction or bounded-root condition.

### Searches for an existing statement

The prescribed `msearch.py` calls were made under Q43 and this item. Full raw
results are retained in the sandbox's `searches.jsonl`.

- `leanfinder` query `Every element with p power roots of every order in a finitely generated field extension of a perfect field is separable algebraic`: 8 hits. The algebraic-perfect-field separability results assume the algebraicity this node must establish; perfect-closure results concern a different subfield. No exact match.
- `loogle` query `PerfectField, IntermediateField.FG`: 0 hits. No match.
- `grep` query `perfectCore|perfect.*subfield|iInf.*frobenius|frobenius.*iInf` in `FieldTheory`: 0 hits. No match.
- `leansearch` query `An element having p power roots of all orders in a finitely generated field extension of a perfect field is algebraic over the base field`: 8 hits. Power-algebraicity and purely inseparable/perfect-closure results do not establish this perfect-core bound. No exact match.

Direct `rg` searches for `perfectCore|perfect_core|finitely-generated-residue-perfect-core`
in `lean/WeilConjectures` and `lean/Sheaf` found only unrelated perfect-complex
results. The exact node-id search in `lean/WeilConjectures` had no hits.
A focused search in Mathlib FieldTheory and both project FieldTheory directories
for `perfect.core|perfectCore|perfect_core|frobenius.*(range|iInf)|iInf.*frobenius`
found unrelated Frobenius-range polynomial lemmas and `SeparableRootPthPower`,
which does not state this finitely generated extension theorem. The proposed
new declaration name was searched in `dag/lean_names_upstream.json` and both
project libraries with no hit.

### Validation

`scompile.py Q43 lem-sfb-finitely-generated-residue-perfect-core` compiled the
single delivered module both as a sandbox module (5.8 s) and with its library
module name (6.7 s), each under the required 60-second limit. There were no
errors or warnings. Every variable and universe is bound explicitly. The only
postponed proof is the named theorem's whole `sorry` proof.

No statement dispute, dependency-interface fault, new node, or correction was
identified. Delivery preflight and its fresh per-file compilation are run before
pushing; their printed outcome is the authoritative delivery validation.

## Second reading by Q43

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
