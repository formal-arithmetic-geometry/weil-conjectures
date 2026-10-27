## Worker report

The module `Sheaf.FieldTheory.GaloisGradedWildKernel` states the single theorem
`ValuationSubring.galois_graded_wild_kernel`. Its entire proof is `sorry`.
No definition, instance, auxiliary theorem, or arbitrary residue embedding is introduced.
The source is Temkin, *Stable modification of relative curves*, §2.1, Lemma 2.1.5,
and the structural input specified by the node, Gabber–Ramero §6.2.8–6.2.18,
Proposition 6.2.12 and Corollary 6.2.14. I opened the primary source
https://arxiv.org/html/0707.3953v3#S2.SS2 and read the definitions and Lemma 2.1.5.
The detailed seven-step proof of the DAG node is reproduced in the theorem's docstring.

The node's statement, proof, proof dependencies, source and other metadata are unchanged.
Its statement dependencies gain the already landed `def-trf-valuation-comap-residue`,
as permitted by brief-stage2 §5 for an existing notion with a usable Lean record.
This supplies the canonical residue algebra structure used in the statement.

Hypotheses and clauses, in the order of the node:

| Node text | Lean rendering and interpretation |
| --- | --- |
| K is a field | `[NontriviallyNormedField K]` includes Mathlib's `Field K`, the recorded match of `def-weil-field`. |
| Real absolute value, zero iff zero, multiplicative, one maps to one | The norm in `NormedField K` is real-valued, positive definite and multiplicative, with `norm_one`. The metric is the norm metric, not an independently chosen topology. |
| Strong triangle inequality | `[IsUltrametricDist K]` gives `‖x + y‖ ≤ max ‖x‖ ‖y‖`, as used by `NormedField.valuation`. |
| The absolute value is nontrivial | `NontriviallyNormedField.non_trivial` supplies a norm greater than one. This is equivalent to a nonzero norm different from one: invert the element if its norm is less than one. |
| Completeness | `[CompleteSpace K]` for that norm metric. |
| All finite extensions carry an extending absolute value | The explicit `hext` binder quantifies over fields F, their K-algebra structures and `[FiniteDimensional K F]`, and asks for `a : AbsoluteValue F ℝ` satisfying the displayed restriction equation. No extra property of the chosen extension norm is assumed there. |
| Finite separable L/K | The first conjunct universally quantifies over L with `[Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]`. Mathlib's separability is separability of every element's minimal polynomial. |
| L is contained in finite Galois N/K | That conjunct gives a field M, its K-algebra structure, finite dimension, `IsGalois K M`, and `Nonempty (L →ₐ[K] M)`. A homomorphism between fields is injective, so this is containment after identifying L with its image. `IsGalois` means separable and normal, with normality the splitting of every minimal polynomial. |
| Any finite Galois N/K, with extending absolute value | The second conjunct universally quantifies over N, a `NormedField N`, `IsUltrametricDist N`, K-algebra structure, finite dimension and `IsGalois K N`, then assumes the norm restriction equation `∀ x : K, ‖algebraMap K N x‖ = ‖x‖`. This is the node's valued finite Galois extension. An extending absolute value over this complete nonarchimedean base is nonarchimedean by uniqueness, so the normed-ultrametric encoding excludes no extending absolute value. N is not required to be discrete or to have perfect residue field. |
| F° and its maximal ideal | `O = (NormedField.valuation (K := N)).valuationSubring` fixes O to `‖x‖ ≤ 1`. Its maximal ideal is the nonunits, equivalently `‖x‖ < 1`. The lower ring is `O.comap (algebraMap K N)`; the fixed-field ring is `B = O.comap (algebraMap T N)`. Thus these are exactly the restricted valuation rings of the node. The record of `def-trf-valuation-ring` is used through Mathlib's `ValuationSubring` and its `ValuationRing` instance, rather than replaced by a private valuation-ring predicate. |
| Residue fields | Every occurrence of `IsLocalRing.ResidueField` is the quotient by the canonical maximal ideal. All extension maps are the actual restriction-induced maps `comapResidueFieldMap`. |
| G = Aut_K(N) | `N ≃ₐ[K] N`, with its usual group structure. |
| P is precisely the displayed kernel | `P : Subgroup (N ≃ₐ[K] N)` and the biconditional `σ ∈ P ↔ ∀ x : N, x ≠ 0 → ‖σ x - x‖ < ‖x‖`. Nonzero field elements are equivalent to the node's units. Existence of the subgroup with this carrier is part of the theorem, not an assumed subgroup-closure result. |
| T is precisely N^P | `T : IntermediateField K N` with `T = IntermediateField.fixedField P`; Mathlib's membership lemma says `∀ σ ∈ P, σ x = x`. |
| P is normal | `P.Normal`. |
| p is the residue characteristic of K | `p = ringChar (IsLocalRing.ResidueField (O.comap (algebraMap K N)))`. The norm restriction equation identifies this comap with K's closed unit ball. |
| e(T/K) and e(N/T) | The equalities specifying `e` and `e₁` use `.range.index` for the image of the lower field's units in the upper units modulo the upper valuation ring's unit group. The norm homomorphism on field units has kernel exactly that unit group, so this is `[Γ_upper : Γ_lower]`. The image of the lower field units equals the image of its value group. |
| f(T/K) and f(N/T) | The equalities specifying `f` and `f₁` use `@Module.finrank` of the indicated residue fields, with the module structure of `comapResidueAlgebra`. The first is formed using B and K→T; the second using O and T→N. Their base rings are the restrictions, not arbitrary isomorphic fields with unspecified embeddings. |
| T/K has separable residue extension | The explicit `@Algebra.IsSeparable` clause on B's residue extension uses the same `B.comapResidueAlgebra` as f. |
| [T:K] = e(T/K)f(T/K) | `Module.finrank K T = e * f`. |
| For p > 0, P has p-power order | `0 < p → ... (∃ a : ℕ, Nat.card P = p ^ a) ...`. |
| For p > 0, e(T/K) is prime to p | `Nat.Coprime e p` in the same branch. |
| For p > 0, N/T has purely inseparable residue extension | For every `z : IsLocalRing.ResidueField O`, the statement gives `a : ℕ` with `z ^ (p ^ a)` in the range of the canonical residue map for T→N. This is exactly the node's explicit power-membership definition and includes zero. |
| For p > 0, e(N/T), f(N/T) are p-powers | The two further existentials `e₁ = p ^ a` and `f₁ = p ^ a`. Exponents are independent and may be zero. |
| For p = 0, P is trivial | `p = 0 → P = ⊥ ∧ ...`. The bottom subgroup is the identity subgroup. |
| For p = 0, the residue fields of N/T are equal | `Function.Surjective (O.comapResidueFieldMap (algebraMap T N))`. This map between fields is injective, so surjectivity expresses equality under the specified residue embedding, not mere existence of some isomorphism. |
| For p = 0, e(N/T) = f(N/T) = 1 | `e₁ = 1 ∧ f₁ = 1` in the zero-characteristic branch. |
| No discreteness or perfection | There is no discrete-valuation, rank-discreteness, finite-residue-field or perfect-field assumption. |

The existentially bound O, B, T and p,e,f,e₁,f₁ are constrained by the displayed
canonical equalities. They are ordinary binders, not `let`, `have`, private aliases,
new definitions, choices from a bare existence theorem, or additional hypotheses.
They give the theorem's long formula readable names without changing its content.
The lower base residue rings appearing through B and O agree after their equations:
`comap_comap` identifies successive restriction along K→T→N with restriction along K→N.

Universes u, v, w are all explicit and independent. The Galois envelope lives in
`Type (max u v)`. The test fields for `hext` live in `Type (max u v w)`, which is
at least the universe of K and of both extension families. This avoids the small
independent test-universe problem; smaller relevant finite fields can be lifted.
The theorem does not force K and its extensions to have equal universes.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`; its full class
  signature and docstring were read. Included by the normed-field and Galois imports.
- `def-trf-valuation-ring`: Mathlib `ValuationRing` and `ValuationRing.TFAE`, in
  `Mathlib.RingTheory.Valuation.ValuationRing`; read the class and the five equivalent
  conditions, including the fraction-field alternative. The canonical
  `Valuation.valuationSubring` uses precisely this notion.
- `def-trf-valuation-comap-residue`: `ValuationSubring.comapResidueAlgebra`, module
  `Sheaf.RingTheory.ValuationComapResidue`, public import. Read its source and
  docstring and the underlying `comapInclusion`, `comapInclusion_isLocalHom` and
  `comapResidueFieldMap` in `Sheaf.FieldTheory.AbhyankarInequality`. Its `.toModule`
  is supplied explicitly to finrank; its algebra is supplied explicitly to separability.
- `NormedField.valuation`, `Valuation.valuationSubring`, `ValuationSubring.comap`,
  `ValuationSubring.unitGroup`, `Subgroup.index`, `IntermediateField.fixedField`
  and `IntermediateField.mem_fixedField_iff` are the existing Mathlib constructions.
  Their definitions were opened before writing the signature.

Already stated proof dependencies are imported with ordinary imports:

- `WeilConjectures.FieldTheory.FiniteGaloisReceivingSeparableExtensions`, declaration
  `finite_galois_receiving_separable_extensions` (signature and docstring read).
- `WeilConjectures.FieldTheory.PurelyInseparablePthRootTower`, declaration
  `IsPurelyInseparable.exists_pth_root_tower` (source, statement and docstring read).
- Mathlib `spectralNorm_unique_field_norm_ext` in
  `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`, including its complete,
  nontrivially normed, ultrametric base and algebraicity hypotheses.
- Mathlib `exists_prime_orderOf_dvd_card'` in
  `Mathlib.GroupTheory.Perm.Cycle.Type`, and `IsPGroup.iff_card` in
  `Mathlib.GroupTheory.PGroup` (both signatures and docstrings read).
- The public Galois import also supplies `IsGalois.card_aut_eq_finrank`,
  `IsGalois.mem_range_algebraMap_iff_fixed`,
  `IsGalois.of_fixedField_normal_subgroup`, `IsGalois.normalAutEquivQuotient`
  and its normalization lemma; their sources were opened.
- `lem-trf-valued-extension-degree-bound` and
  `lem-trf-valued-initial-form-automorphism-bound` have no Lean records in the read
  repository, so there are no recorded modules to import for these proof-only inputs.
  Their natural-language proof roles remain explicit in the docstring. They are not
  prerequisites for typing this statement and are not restated here.

Edge cases checked before writing and again against the signature:

- N=K and the trivial Galois group: P is bottom, T is top, all relative degrees
  and indices are one, and the power exponents can be zero.
- Residue characteristic zero: the separate implication gives trivial P and equality
  of residue fields through the canonical map; no use of powers of zero is required.
- Positive residue characteristic: all p-power exponents permit zero, so tame or
  unramified examples with trivial wild subgroup remain included.
- Unramified extensions: P is bottom, T=N, and the upper invariants are one.
- Purely wild immediate extensions: T=K is permitted, e=f=1 for the lower extension,
  and no defectless equality is imposed on N/T.
- Imperfect residue fields and nondiscrete real value groups: the power-membership
  statement permits nontrivial purely inseparable residue extensions; no discrete
  ramification-index formula or perfection assumption was imported into the signature.
- The zero residue element is included in `∀ z`; for it the power-membership statement
  is satisfied by the zero image. The kernel inequality is only for nonzero field
  elements, so it does not ask for the impossible strict inequality 0<0 at zero.
- Although Mathlib index and finrank use zero for infinite cases, this cannot produce
  a spurious witness: the equality `[T:K]=e*f` has positive finite left side, and both
  upper invariants are forced to be prime powers or one. The underlying relative
  groups and residue extensions are finite for finite valued extensions in any case.

Searches made with the prescribed wrapper:

- LeanFinder: `Finite Galois complete nonarchimedean valued field wild inertia kernel
  is p group and fixed field is tame`: eight hits, headed by
  `ValuationSubring.inertiaSubgroup`, Dedekind ramification/inertia results and general
  Galois definitions. None states the general nondiscrete wild-kernel theorem.
- Loogle: `Valuation, IsGalois`: zero hits.
- Mathlib grep: `wildInertia|wild_inertia|initialForm|initial_form`: zero hits.
- LeanSearch: `Finite Galois extension of complete nonarchimedean field wild inertia
  p group tame fixed field`: eight hits including fixed-field facts, `IsGalois.tfae`
  and Dedekind inertia degrees; none matches this statement.
- Direct `rg` in `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
  for the new declaration name and wild-inertia names found no duplicate. Searching
  `lean/WeilConjectures` for this blueprint id also found none.
- Direct source searches found only the discrete-DVR wild-kernel arguments in
  `Sheaf.FieldTheory.FiniteDVRTameInertia`, `FiniteRadicalRestriction` and
  `FiniteTameCharacterTower`. These use discrete valuation assumptions and are not
  this node. Searches for valuation/restriction/residue helpers found the already
  landed `ValuationComapResidue` and `AbhyankarInequality`, which are reused.

No statement correction or dispute was needed. No new node or dependency repair was needed.
The only `sorry` is the entire proof of the theorem belonging to this DAG node.
`scompile.py Q46 lem-trf-galois-graded-wild-kernel <module>` passed for both its
sandbox module and its intended library module, with no errors or unexpected warnings.

## Second reading by Q46

I made a separate second pass with the original node, the completed signature and the
canonical residue-map source open. The dispatch instruction forbids starting another
agent; this section records that second pass, not an assertion of an independent agent
review. The maintainer's independent review remains the delivery review.

I compared every hypothesis and clause in the table above with the actual signature.
In particular, the envelope is a separate conjunct, normality is a conclusion rather
than a hypothesis, the membership condition defines all of P, and the fixed field is
constrained by equality rather than left as an arbitrary intermediate field. The two
finranks use the correct, different canonical residue algebras for T/K and N/T.
The characteristic p is taken at K, not N; repeated restriction along K→T→N gives
the same base valuation ring. The kernel condition excludes only zero, while the
purely inseparable residue clause includes every residue element. The p=0 branch
states both upper indices equal one and surjectivity of the canonical residue map.
The positive branch states all three separate p-power claims and coprimality only for
the lower e. There is no degree equality for the upper extension that would silently
exclude defect. The existential numeric equalities prevent choosing arbitrary tame
invariants. All universes are declared, and the field structures in the envelope are
bound explicitly without auto-implicit variables or `let` binders.

This pass found no mismatch requiring a change. The delivered statement retains the
node's full scope, including nondiscrete valuations and imperfect residue fields.
