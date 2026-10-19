## Worker report

The module `Sheaf.RingTheory.NormalAlgebraSeparableScalarExtension` states
`Algebra.isNormal_tensorProduct_of_separableExtension`, with `sorry` as its sole proof.
The node is unchanged except for its `lean` record. There are no new nodes, dependency modules,
or statement corrections.

Read the item's complete node and every statement dependency, including their recorded Lean
signatures and docstrings. Read Stacks `varieties.tex`, lemma-base-change-normal-by-separable
(Tag 0C3M), and `algebra.tex`, lemma-separable-field-extension-geometrically-normal (0C30)
and lemma-geometrically-normal-tensor-normal (06DF). These give exactly this affine statement.

Hypothesis and clause correspondence:

- The field `k` is `(k : Type u) [Field k]`.
- The commutative `k`-algebra `B` is `(B : Type v) [CommRing B] [Algebra k B]`.
- The field extension `K/k` is `(K : Type w) [Field K] [Algebra k K]`.
- Separability in the finitely-generated-subextension sense is
  `(hK : Algebra.IsSeparableExtension k K)`. The definition quantifies over intermediate
  fields `F` with `F.FG` and asks for `Algebra.IsSeparablyGenerated k F`.
  It does not require `Algebra.IsSeparable k K`, which would restrict to algebraic separability.
- Normality of `B` is `hB : ∀ (p : Ideal B) [p.IsPrime],
  IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)`.
  This is the exact inline form required by def-weil-pbc-normal-ring's record.
- The scalar extension is `B ⊗[k] K`, with the commutative ring structure provided by
  `Algebra.TensorProduct.instCommRing`. `Algebra.TensorProduct.tmul_mul_tmul` and
  `Algebra.TensorProduct.one_def` give exactly the multiplication and unit in the node.
  These describe the object, and are not extra conjuncts in the conclusion.
- The conclusion quantifies over all `q : Ideal (B ⊗[k] K)` with `[q.IsPrime]`, requiring
  both `IsDomain (Localization.AtPrime q)` and
  `IsIntegrallyClosed (Localization.AtPrime q)`.
- There are no algebraicity, finite-generation, Noetherian, domain, or nontriviality
  hypotheses on `B`, and no algebraicity or finite-generation hypothesis on `K/k`.

Dependency declarations used:

- def-weil-field: `Field`, `Mathlib.Algebra.Field.Defs` (available through the field imports).
- def-pc-field-extension: `Algebra`, `Mathlib.Algebra.Algebra.Defs`, under the two field
  structures; its structure map is `algebraMap k K`.
- def-weil-pbc-separable-field-extension: `Algebra.IsSeparableExtension` and
  `Algebra.IsSeparablyGenerated`, `Sheaf.FieldTheory.SeparableExtension`, read in full.
- def-weil-pbc-normal-ring: `IsIntegrallyClosed`,
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, with `IsDomain` and
  `Localization.AtPrime` (`Mathlib.RingTheory.Localization.AtPrime.Basic`), as the
  dependency's record explicitly prescribes. No replacement normality predicate is defined.
- def-weil-pbc-module-tensor-product: `TensorProduct`,
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, with the algebra multiplication from
  `Mathlib.RingTheory.TensorProduct.Basic`. Read the quotient definition and the algebra
  unit, multiplication, and commutative-ring instance.
- The stated proof dependency `Algebra.isNormal_tensorProduct_of_geometricallyNormal`,
  `Sheaf.RingTheory.GeometricallyNormalTensorNormal`, is imported without `public`.
  Its signature and docstring were read. The other substantive proof dependency,
  lem-weil-pbc-separable-field-geometrically-normal, has no recorded Lean module on this
  base; there is no module to import for it. Both appear in the natural-language proof.

Edge cases: the zero algebra has no primes, so `hB` and the conclusion correctly permit it.
A disconnected normal algebra (for example a product of fields) is not required to be a
single domain; normality is asserted only after prime localization. The identity extension,
transcendental separable extensions, and all characteristics are included. Independent
universes `u v w` cover fields and algebras of arbitrary sizes. There is no quantification
across a test-extension universe in this theorem, hence no small-test-universe restriction.
No false statement or node fault was found.

Searches (2026-10-15):

- `msearch.py ... leanfinder "A normal commutative algebra remains normal after tensoring
  with an arbitrary separable field extension"`: eight hits, concerning geometrically
  reduced tensor products, field tensor products, linear disjointness, and algebraicity;
  none asserts normality at every prime localization.
- `msearch.py ... loogle "IsIntegrallyClosed, TensorProduct"`: zero hits.
- `msearch.py ... grep
  "IsIntegrallyClosed.*[Tt]ensor|[Tt]ensor.*IsIntegrallyClosed|[Gg]eometricallyNormal"`:
  zero Mathlib hits.
- `msearch.py ... leansearch "A normal commutative algebra remains normal after tensoring
  with a separable field extension"`: unavailable, Internal Server Error.
- `rg` in the upstream `WeilConjectures` and project `lean/Sheaf` for
  `normal.*separable|separable.*normal|isNormal_tensorProduct` and the item's exact id:
  no exact statement. The general geometrically-normal tensor theorem is the stated
  proof dependency, not a duplicate: its premise is geometric normality of an arbitrary
  algebra rather than separability of a field extension. Other hits concern normal
  field extensions and normalization residue fields.
- `rg` of `dag/lean_names_upstream.json` for normal/separable combinations and the chosen
  module/declaration names: no match. The new declaration's full name is absent from
  the Mathlib and upstream searches.

Validation: server-only `scompile.py` checks the delivered module with the prescribed
60-second per-file limit. The delivery dry run supplies the final compile and preflight
result; the independent second reader will add their own reading and deliver.

## Second reading by NO

Independent second reader, 2026-10-15. I read the complete item node, its five statement
dependency nodes and both substantive proof nodes, the delivered module, and the actual
`Sheaf.FieldTheory.SeparableExtension` and
`Sheaf.RingTheory.GeometricallyNormalTensorNormal` declarations and docstrings.
I read Stacks varieties.tex, lemma-base-change-normal-by-separable (0C3M), together with
its immediately preceding fibre-product lemma, and algebra.tex,
lemma-separable-field-extension-geometrically-normal (0C30),
lemma-geometrically-normal-tensor-normal (06DF), and
definition-separable-field-extension (030O). These places impose no ambient finite-type,
Noetherian, algebraic-extension, or nonzero-algebra assumption on this result.

Node inventory and clause-by-clause correspondence:

1. Base field k: `(k : Type u) [Field k]`. Exact; Mathlib's `Field` extends
   `CommRing` and `DivisionRing`, including nontriviality. This is def-weil-field.
2. Commutative k-algebra B: `(B : Type v) [CommRing B] [Algebra k B]`. Exact;
   `Algebra` supplies the unital ring map and its scalar action, without injectivity
   or nontriviality imposed on B. I read its fields in Algebra/Algebra/Defs.lean.
3. Extension K/k: `(K : Type w) [Field K] [Algebra k K]`. Exact;
   this is def-pc-field-extension's recorded Algebra encoding, with structure map
   `algebraMap k K`. A ring map out of the field is automatically injective.
4. Separability: `(hK : IsSeparableExtension k K)`. Exact; opening the dependency
   gives `∀ F : IntermediateField k K, F.FG → IsSeparablyGenerated k F`.
   I read `IntermediateField.FG`: existence of a finite set generating the intermediate
   field, not finite generation as an algebra. `IsSeparablyGenerated` is existence of
   a set forming a transcendence basis and `Algebra.IsSeparable` over its generated
   intermediate field. Thus algebraic separability is required only after choosing the
   transcendence basis, exactly as Stacks 030O; K/k need not be algebraic.
5. Normal B: `hB : ∀ (p : Ideal B) [p.IsPrime],
   IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)`.
   Exact inline form prescribed by def-weil-pbc-normal-ring; no global-domain
   hypothesis replaces local normality. I read `IsIntegrallyClosed`, which is integral
   closedness in `FractionRing`, paired here with the necessary domain clause.
6. Scalar-extension object: `B ⊗[k] K`. Exact use of the existing module tensor
   product, whose quotient construction I read in LinearAlgebra/TensorProduct/Defs.lean,
   equipped with `Algebra.TensorProduct.instCommRing`. The multiplication is precisely
   `tmul_mul_tmul`, `(b ⊗ c)(b' ⊗ c') = bb' ⊗ cc'`; the unit is `one_def`,
   `1 = 1 ⊗ 1`, in RingTheory/TensorProduct/Basic.lean. These specify the object;
   they are not additional hypotheses or conclusion clauses.
7. Normality conclusion: `∀ (q : Ideal (B ⊗[k] K)) [q.IsPrime],
   IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)`.
   Exact: every prime, both domain and integral closedness, in the same order of
   quantification as the node. Nothing is omitted or strengthened.
8. Absence of restrictions: the entire binder list contains no finite generation,
   Noetherian, global-domain, or nonzero assumption on B and no algebraicity or
   finite-generation assumption on K/k. Exact.

Edge cases: B may be zero, in which case B and its tensor product have no primes and
normality is vacuous. Products of normal domains are covered prime by prime, without
requiring B to be a domain. The identity extension and transcendental separable
extensions are included in every characteristic. Empty transcendence bases are allowed
by the dependency's `Set K` encoding, and finite subextensions generated by zero
elements are allowed by `Finset`. There is no index family, integer n, or scheme binder
in this affine statement; the empty affine scheme is precisely the zero-algebra case.
Independent `u v w` are all explicitly bound and restrict none of the three carriers.
There is no quantification over a separately small universe of test extensions here.

Independent duplicate searches, with different search wording from the worker:

- `msearch.py NO lem-weil-pbc-normal-algebra-separable-scalar-extension leanfinder
  "Localization at primes of tensor product of normal algebra and separable extension
  is integrally closed"`: eight hits, concerning tensor maps to integral closures and
  localization of integral closures, including `TensorProduct.toIntegralClosure` and
  `IsIntegralClosure.isLocalization_of_isSeparable`. None states this normality result.
- `msearch.py ... loogle "IsIntegrallyClosed, Localization.AtPrime"`: two hits,
  `IsIntegrallyClosed.of_localization` and `.of_localization_maximal`; both infer global
  integral closedness of an already given domain and concern no scalar extension.
- Independent `rg` over Mathlib, upstream WeilConjectures, project lean/Sheaf, and
  dag/lean_names_upstream.json for `isNormal_tensorProduct`, integral-closed/tensor
  combinations and `geometricallyNormal`, followed by normal/separable and
  scalar/normal combinations: the only relevant statement is the project's recorded
  geometrically-normal tensor theorem, which takes geometric normality of an arbitrary
  algebra, rather than separability of the scalar-extension field. Other hits concern
  normal field extensions, normalization or unrelated normalized scalar constructions.
  No exact duplicate, conflicting full name, or alternative existing normality notion.

The three proof steps in the docstring match the node: separability implies geometric
normality; the general tensor theorem gives normality with factors reversed; the tensor
swap transports the prime-localization domain and integral-closedness conclusions.
The available general tensor theorem is imported non-publicly. The other substantive
proof node still has no Lean record, so there is no module to import for it. All statement
notions use their dependency encodings. There are no new definition nodes or dependency
modules to review, and no statement correction or citer verdicts to recheck.

No mismatch found; Lean and node left unchanged. The sole theorem has exactly a `sorry`
proof; there are no definitions, hollow data, private copies, local instances, or
file-local notation. Source and blueprint docstrings are present; all lines fit the
100-character convention. I compared `lean.statement` programmatically with the exact
source signature before `:= by`: verbatim equal, with all variables/universes bound.
Validation uses the required server-only scompile.py and deliver2.py preflight below.

Second-reader validation: scompile.py passed with no diagnostics (item 1.0 s;
side-only dependency 1.5 s; nice 19, two threads, 60 seconds per file).
deliver2.py --no-push printed OK: preflight and server compilation passed.
