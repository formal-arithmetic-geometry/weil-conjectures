## Worker report

The module `Sheaf.RingTheory.GeometricallyNormalTensorNormal` states
`Algebra.isNormal_tensorProduct_of_geometricallyNormal`, with `sorry` as its whole proof.
Its module and declaration docstrings cite Stacks Tag 06DF. The declaration docstring
contains all eleven proof steps from the node, including their dependency references.
No definition, new node, dependency module, or statement correction is needed.

Hypothesis and clause correspondence:

- A field k: `(k : Type u) [Field k]`, the Mathlib declaration of `def-weil-field`.
- Commutative k-algebras A and B: `(A : Type v) (B : Type w)`, `[CommRing A]`,
  `[CommRing B]`, `[Algebra k A]`, `[Algebra k B]`.
- Every field extension E/k: `∀ (E : Type (max u v w)) [Field E] [Algebra k E]`
  inside `hA`, using `def-pc-field-extension`'s recorded `Algebra` declaration.
- Geometric normality: `hA` says that for every such E and every prime p of
  `A ⊗[k] E`, `Localization.AtPrime p` satisfies both `IsDomain` and
  `IsIntegrallyClosed`. This is exactly the recorded INLINE FORM of
  `def-weil-pbc-normal-ring`, not a replacement notion.
- Normality of B: `hB` quantifies over every ideal q with `[q.IsPrime]` and asserts
  the same conjunction for `Localization.AtPrime q`.
- Conclusion: every prime ideal r of `A ⊗[k] B` has localization satisfying
  `IsDomain (Localization.AtPrime r) ∧ IsIntegrallyClosed (Localization.AtPrime r)`.
- The tensor product is the dependency's Mathlib `TensorProduct`, with its standard
  commutative algebra structure from `Mathlib.RingTheory.TensorProduct.Basic`.
  `Algebra.TensorProduct.tmul_mul_tmul` supplies the node's multiplication formula;
  its `One` instance is the tensor `1 ⊗ₜ 1`. These describe the object, so are not
  additional conjuncts in the theorem.
- No finite-type, Noetherian, domain, or nonzero binder is imposed on A or B.

Universe and edge-case checks (mathematical inspection): k, A, and B have independent
universes u, v, and w. Test fields occupy their maximum, never a possibly smaller
independent universe. This includes lifted k and the fraction fields needed for
localizations of either algebra. As usual, testing fields in a common universe
expresses geometric normality: failure after any larger field extension is witnessed
by finitely many field coefficients, hence descends to a subextension small enough
for this maximum universe. No cardinal bound is imposed on A or B themselves.
If A or B is the zero algebra, its tensor product is zero and has no prime ideals,
so the conclusion is vacuous; neither is excluded. A normal algebra with several
components is permitted: global `IsDomain` is deliberately absent. Taking E=k
(up to universe lift) tests normality of A. Characteristic zero and positive
characteristic are both allowed. Infinite-dimensional and non-Noetherian algebras
are permitted. No index type or choice of tensor bases enters the statement.

Statement dependency declarations, read at their sources with signatures/docstrings:

- `def-weil-field`: `Mathlib.Algebra.Field.Defs`, `Field` (line 180), extending
  `CommRing` and `DivisionRing`.
- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra` (line 95),
  including the central ring homomorphism `algebraMap`.
- `def-weil-pbc-normal-ring`: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
  `IsIntegrallyClosed` (line 74), integrality inside `FractionRing`;
  `Mathlib.Algebra.Ring.Defs`, `IsDomain` (line 439); and
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime` (line 57),
  the localization at the prime complement. The node explicitly mandates the inline
  conjunction, so there is no missing named normal-ring predicate.
- `def-weil-pbc-module-tensor-product`: `Mathlib.LinearAlgebra.TensorProduct.Defs`,
  `TensorProduct` (line 81), its quotient construction and tensor notation; algebra
  multiplication read in `Mathlib.RingTheory.TensorProduct.Basic` (line 155).

All proof dependencies with recorded modules are imported without `public` unless
already public statement inputs. Additional Mathlib leaf modules are imported for
the proof plan. The dependency/module/declaration records used are:

- `def-weil-pbc-normal-ring`: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, `IsIntegrallyClosed`.
- `def-weil-pbc-module-localization`: `Mathlib.Algebra.Module.LocalizedModule.Basic`, `LocalizedModule`.
- `def-weil-pbc-localization-at-prime`: `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`.
- `lem-fin-normalization-extension-finite`: `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`, `AlgebraicGeometry.Scheme.isFinite_fromNormalizationIn`.
- `def-fin-normalization-extension`: `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`, `AlgebraicGeometry.Scheme.normalizationIn`.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `AlgebraicGeometry.IsFinite`.
- `lem-weil-pbc-normal-ring-integrally-closed-total`: `Sheaf.RingTheory.NormalRingIntegrallyClosedTotal`, `integral_totalFraction_mem_range_of_normal`.
- `def-weil-pbc-finite-type-algebra`: `Mathlib.RingTheory.FiniteType`, `Algebra.FiniteType`.
- `def-weil-pbc-flat-ring-map`: `Mathlib.RingTheory.RingHom.Flat`, `RingHom.Flat`.
- `def-weil-pbc-category-colimit`: `Mathlib.CategoryTheory.Limits.HasLimits`, `CategoryTheory.Limits.colimit`.
- `lem-weil-pbc-filtered-colimit-normal-ring`: `Sheaf.RingTheory.FilteredColimitNormalRing`, `CommRingCat.isNormal_of_filtered_colimit`.
- `lem-weil-pbc-geometrically-reduced-extension-separable`: `Sheaf.FieldTheory.GeometricallyReducedExtensionSeparable`, `Algebra.isSeparableExtension_of_forall_isReduced_tensorProduct`.
- `def-weil-pbc-separable-field-extension`: `Sheaf.FieldTheory.SeparableExtension`, `Algebra.IsSeparableExtension`.
- `lem-weil-pbc-separable-extension-fraction-field-of-smooth-algebra`: `Sheaf.FieldTheory.SeparableExtensionFractionFieldOfSmoothAlgebra`, `FieldTheory.exists_smooth_subalgebra_fraction_field`.
- `lem-weil-pbc-smooth-over-normal-ring-normal`: `Sheaf.RingTheory.SmoothNormalRing`, `RingHom.Smooth.isNormalRing`.
- `lem-weil-pbc-noetherian-finitely-many-minimal-primes`: `Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian`, `minimalPrimes.finite_of_isNoetherianRing`.
- `lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions`: `Sheaf.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions`, `reduced_normal_iff_integrallyClosed_totalFractions`.

Searches for an existing statement (no exact match):

- `msearch.py ... leanfinder "tensor product of a geometrically normal algebra and a
  normal algebra is normal"`: eight hits, concerning geometric reducedness, integral
  tensor products, and smooth/unramified base change. None states normality here.
- `msearch.py ... loogle "IsIntegrallyClosed, TensorProduct"`: zero hits.
- `msearch.py ... grep
  "GeometricallyNormal|IsIntegrallyClosed.*TensorProduct|TensorProduct.*IsIntegrallyClosed"`:
  zero hits in Mathlib.
- `msearch.py ... leansearch` with the same plain-language query: unavailable,
  service Internal Server Error. No conclusion drawn from this unavailable service.
- `rg -n` in `WeilConjectures/`, `lean/Sheaf/`, and `dag/lean_names_upstream.json`
  for `GeometricallyNormal|geometrically_normal|geometricallyNormal`, the node id,
  and both integral-closure/tensor-product orders: no matches.
- Read the complete Stacks `lemma-geometrically-normal-tensor-normal` proof in
  `literature/stacks-project/algebra.tex`. It agrees with the node's statement;
  the known `A ⊗_K L` typo in the source proof is already corrected in the DAG proof.

No statement dispute or node fault was found. All writes are in the designated sandbox;
validation uses only the mandated server compile and delivery dry run.

## Second reading by NA

Independent second reader, 2026-10-15. Read the node and module together against
`literature/stacks-project/algebra.tex`, Tag 06DF,
`lemma-geometrically-normal-tensor-normal`, and the surrounding section. The section
imposes no standing Noetherian or finite-type hypothesis. Its preceding geometric
normality lemma explicitly includes all field extensions, equivalently finitely
generated field extensions. Also read `definition-ring-normal` (00GV).

Object, hypothesis and conclusion checklist (each verdict: exact):

1. The base is a field k: `(k : Type u) [Field k]`. Read `Field` in
   `Mathlib.Algebra.Field.Defs`: it extends `CommRing` and `DivisionRing`, so the
   nontriviality required by the node is present.
2. A and B are arbitrary commutative k-algebras: `(A : Type v) (B : Type w)`,
   `[CommRing A] [CommRing B] [Algebra k A] [Algebra k B]`. Read the recorded
   `Algebra` declaration in `Mathlib.Algebra.Algebra.Defs`: its central unital
   ring map is precisely the structure map, without an injectivity requirement
   that would wrongly exclude the zero algebra.
3. Every extension E/k: `∀ (E : Type (max u v w)) [Field E] [Algebra k E]`
   in `hA`. This uses `def-pc-field-extension`'s declaration, with every choice
   of algebra structure quantified. There is no algebraicity, characteristic,
   finite-generation or separability condition.
4. Geometric normality of A: the rest of `hA` quantifies over every prime ideal
   `p : Ideal (A ⊗[k] E)` and asserts
   `IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)`.
   Opened `def-weil-pbc-normal-ring`: its recorded INLINE FORM is exactly this
   conjunction, not a global domain assumption. Read `Localization.AtPrime`
   (localization at the prime complement), `IsDomain` (including nontriviality),
   and `IsIntegrallyClosed` (integral closure in `FractionRing`) in their actual
   Mathlib modules. Thus this is normality in the source's sense.
5. Normality of B: `hB : ∀ (q : Ideal B) [q.IsPrime], ...` with the same
   conjunction. This permits disconnected normal rings and is neither a domain
   specialization nor mere integral closure in the total fraction ring.
6. The tensor algebra: `A ⊗[k] B` is Mathlib's `TensorProduct`, recorded by
   `def-weil-pbc-module-tensor-product`. Read its quotient construction and the
   algebra structure in `Mathlib.RingTheory.TensorProduct.Basic`, including
   `Algebra.TensorProduct.tmul_mul_tmul`. Multiplication is exactly
   `(a ⊗ b)(a' ⊗ b') = aa' ⊗ bb'`, and the unit is `1 ⊗ 1`.
   These specify the object and need no extra theorem conjunct.
7. Conclusion: `∀ (r : Ideal (A ⊗[k] B)) [r.IsPrime], ...` asserts that every
   prime localization is an integrally closed domain. No conclusion clause is
   absent, and no stronger global-domain conclusion is asserted.
8. Absence of extra hypotheses: inspected the complete binder list. There is
   no Noetherian, finite-type, domain or nonzero instance on A or B, and no
   additional flatness or finiteness premise. The quantifier order matches
   geometric normality followed by the conclusion for all primes.

Edge cases: A or B may be the zero algebra; the tensor algebra is then zero and
has no prime ideals, so its normality clause is vacuous. Rings with multiple
components remain covered. Both characteristic zero and positive characteristic
are allowed. There are no index sets, schemes or natural-number parameters whose
empty or zero cases might be excluded. The independent universes u, v, w allow
arbitrarily sized k, A and B. Test fields lie in their maximum, so lifted copies of
k and fraction fields of A and B are available. This is an adequate universe for
geometric normality: the source's equivalent finitely generated extension test
uses fields of cardinality at most max(|k|, aleph_0), and arbitrary extensions are
directed unions of these. Thus no larger-universe geometric case is lost. All
universe names and variables in the signature are explicitly bound.

Independent searches (not merely the first worker's names):

- LeanFinder, via `msearch.py`: "normality of tensor products over a field with
  geometrically normal factor and normal factor". Eight hits: geometric
  reducedness, integral tensor products, unramified base change and linear
  disjointness. None states this lemma or defines geometric normality.
- Loogle: `IsIntegrallyClosed (TensorProduct ?k ?A ?B)`: zero hits.
- LeanSearch: "If A is geometrically normal over a field k and B is normal, then
  A tensor k B is normal": service unavailable (Internal Server Error); no
  mathematical verdict inferred from the unavailable search.
- Case-insensitive `rg` over Mathlib, `WeilConjectures`, project `lean/Sheaf`
  and `dag/lean_names_upstream.json`, using geometric-normal variants and both
  orders of normality/integral-closure and tensor-product keywords. No exact
  match. Opened the substantive upstream hit
  `Algebra.WeaklyEtale.isIntegrallyClosedIn_tensorProduct`: it assumes a weakly
  etale algebra and an algebraic extension and concludes relative integral
  closure, so it is not this statement. Other hits were orthonormal bases,
  incidental proof variables, or a geometric-normality comment.

No new definition nodes, dependency modules, or statement correction are present
or needed. All four statement dependency records have been checked against their
actual declarations; none requires replacement. Checked the recorded proof
modules against the import list: they are imported, and the eleven-step docstring
tracks the node's localization, finite-type/filtered-colimit reductions,
separability and smoothness argument, minimal primes, total fractions,
intersection, and final reversal of reductions. The source's `A tensor_K L` typo
is already corrected to `A tensor_k L` in the node and docstring.

No mismatch was found; left the Lean module and node unchanged. No hollow data
or private definition is introduced; the sole theorem proof is `sorry`. Both
docstrings cite 06DF and the exact blueprint id. Programmatically checked that
`lean.statement` is verbatim the module's signature before `:= by`.

Validation: mandated `scompile.py NA
lem-weil-pbc-geometrically-normal-tensor-normal
lean/Sheaf/RingTheory/GeometricallyNormalTensorNormal.lean` passed on the server
in 1.4 seconds, nice 19, two threads, 60-second limit, with no diagnostics.
