## Worker report

The module `Sheaf.Paper.CoefficientFieldGenericDifferentialBasis` states
`WeilConjectures.coefficient_field_generic_differential_basis`, with proof `sorry`.
Its only other declaration, `WeilConjectures.CoefficientSectionGenericDifferentialBasis`,
is a full definition of this theorem's exact generic-basis conclusion for a supplied
section and tuple. It introduces no independent mathematical notion and contains no
postponed data or proof. Both declarations carry the item's blueprint tag and source.
No node field changes except `lean`; no new node, dependency repair, or statement
correction is needed.

The natural-language node and its eleven proof steps were read in full, together with
every statement dependency and its recorded Mathlib declaration and docstring.
Read the source PDF, Exposé IV §§2.1.3–2.1.12, printed pp.50–53. The theorem docstring
records all eleven DAG proof steps, including the correction already present in the
node's proof to the source's displayed coefficient-field formula in §2.1.11. This
existing proof repair does not change the statement. No new STATEMENT-DISPUTED finding.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| A commutative local ring `(B,n)` | `(B : Type u) [CommRing B] [IsLocalRing B]`, with `n = IsLocalRing.maximalIdeal B` throughout |
| Reduced | `[IsReduced B]` |
| Noetherian | `[IsNoetherianRing B]` |
| Complete for the maximal ideal, including separatedness | `[IsAdicComplete (IsLocalRing.maximalIdeal B) B]` |
| Characteristic `p > 0` | `(p : ℕ) [Fact p.Prime] [CharP B p]`; a field quotient and prime characteristic exclude the degenerate cases |
| Finite common component dimension `e ≥ 1` | `(e : ℕ) (he : 1 ≤ e)` and `hequidim : ∀ q, IsMinimalPrime q → ringKrullDim (B ⧸ q) = (e : WithBot ℕ∞)`; this is exactly the node's parenthetical definition of equidimensionality, and implies dimension B = e for a Noetherian local ring |
| Residue field `k` and residue map | Mathlib's `IsLocalRing.ResidueField B = B ⧸ maximalIdeal B` and `IsLocalRing.residue B` |
| Optionally fix a perfect subfield | `(K₀ : Type v) [Field K₀] (constants : Option (K₀ →+* B))`, with `hperfect` requiring bijectivity of `x ↦ x^p` precisely when `constants = some ι` |
| No fixed subfield case | `constants = none`; then `hperfect` has no conditions and the last conclusion is vacuous. K₀ may be any dummy field, for example the rational numbers. Thus this case does not require a perfect field or a field inclusion |
| A field section `s : k ↪ B` | The existential ring homomorphism `s : IsLocalRing.ResidueField B →+* B`, and `(IsLocalRing.residue B).comp s = RingHom.id ...`. This also gives injectivity; field homomorphisms into the nontrivial local ring are embeddings |
| Elements `a₁,…,a_e` in the maximal ideal | One existential tuple `a : Fin e → B` with `∀ i, a i ∈ IsLocalRing.maximalIdeal B` |
| The `k`-algebra structure is the section `s` | The helper definition uses `letI : Algebra (IsLocalRing.ResidueField B) B := s.toAlgebra` before forming differentials. This is a local instance in a definition, not an opaque let-binder in the theorem |
| Completed Kähler differentials | `AdicCompletion (IsLocalRing.maximalIdeal B) (KaehlerDifferential (IsLocalRing.ResidueField B) B)`, literally the inverse limit of the quotients by `n^m • ⊤` |
| Every minimal prime | `∀ (q : Ideal B) [q.IsPrime], IsMinimalPrime q → ...`; the prime instance only supplies structure already implied by minimality |
| Tensor with `Frac(B/q)` | `TensorProduct B q.ResidueField ...` with Mathlib's canonical B-algebra structure. `Mathlib.RingTheory.LocalRing.ResidueField.Ideal` gives `IsFractionRing (B ⧸ q) q.ResidueField`; there is no arbitrarily supplied field or scalar action. The tensor factors are commuted from the node's written order, with the same canonical scalar extension |
| The displayed differentials form a basis | An existential `Module.Basis (Fin e) q.ResidueField ...` whose value at EVERY `i` is explicitly `TensorProduct.tmul B 1 (AdicCompletion.of ... (KaehlerDifferential.D ... (a i)))` |
| Same section and tuple on all components | Existentials for `s,a` precede the universal quantifier over minimal primes |
| Perfect-subfield compatibility | For the specified `ι`, `∀ x : K₀, s (IsLocalRing.residue B (ι x)) = ι x`; this identifies K₀ with its residue image exactly as in the node |

The optional field lives in an independent explicit universe `v`, and B and its canonical
residue and generic fields live in `u`. There is no equality of unrelated universes,
no bound on the cardinality of the residue field or its p-basis, and no choice of data
from an unproved mere existence assertion. The helper spells out the construction
from `s` directly, using canonical Mathlib data.

Statement dependencies actually used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`.
- `def-weil-pbc-adically-complete-ring`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `IsAdicComplete`, `AdicCompletion`, `AdicCompletion.of`. Read the class and inverse-limit
  definition, canonical map, and `of_bijective_iff`.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`, `ringKrullDim`.
- `def-weil-pbc-kahler-differentials`: `Mathlib.RingTheory.Kaehler.Basic`, `KaehlerDifferential`,
  `KaehlerDifferential.D`; read also `linearMapEquivDerivation`.

Additional canonical Mathlib interfaces: local residue field and quotient map from
`Mathlib.RingTheory.LocalRing.ResidueField.Basic`, generic residue field and its
fraction-ring instance from `.ResidueField.Ideal`, and `IsMinimalPrime` from
`Mathlib.RingTheory.Ideal.MinimalPrime.Basic`.

Available proof dependencies are imported without `public`:
`WeilConjectures.FieldTheory.ExistsPBasis` (`Field.exists_p_basis`),
`WeilConjectures.RingTheory.FiniteModuleComplete`
(`finite_module_complete_over_complete_noetherian`),
`Sheaf.RingTheory.PBasisComplementMonomialBasis`
(`RingTheory.pBasisComplementMonomialBasis`), and
`Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian`
(`Ideal.finite_minimalPrimes_of_isNoetherianRing`). Read their signatures and docstrings;
the first two sources were retrieved with `scompile.py --source` because the old
checkout lacks those newly published modules. The three proof-only prerequisite nodes
`lem-per-prescribed-pbasis-coefficient-section`,
`lem-per-cofinite-pbasis-completed-generic-rank`, and
`lem-per-completed-differential-finite-conormal` have no recorded Lean declarations yet.
They are not needed to TYPE this statement, so no placeholder import or duplicate
statement is supplied. Their proof roles remain in the docstring and DAG.

Edge cases checked mathematically:

- The zero ring is excluded by the local-ring/residue-field setup; characteristic zero
  and composite characteristic are excluded by prime p and CharP.
- e = 0 is expressly excluded by the node and by `he`; e = 1 works. The theorem does
  not demand a system of parameters or a finite presentation not present in the node.
- For a domain there is one minimal component, and the conclusion gives the ordinary
  common generic-basis assertion for its fraction field.
- For `k[[x,y]]/(xy)` there are two one-dimensional minimal components: the same `a`
  must work on both, as the quantifier order enforces. This checks that the statement
  was not weakened to componentwise independent choices of lifts.
- `k[[t]]`, including imperfect k, is admitted; the coefficient field may change.
  In inseparable examples such as `k[[x,y]]/(y^p-u*x^p)`, choosing the coefficient
  section is essential; it is existential and is never assumed in a hypothesis.
- Optional constants: both none and some are covered; an inclusion into B gives
  an injective residue inclusion since nonzero field elements are units. For perfect
  constants, adic separatedness forces the final equality as in proof step 11.
- Completion is the module completion, not just the ordinary Kähler module or the
  module modulo the maximal ideal; basis values use its canonical map before tensoring.

Searches for reuse:

- `msearch.py leanfinder`, query `complete reduced equidimensional local ring coefficient
  field common basis completed Kahler differentials`: eight hits, including
  `Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential`, `of_basis_kaehlerDifferential`,
  `Algebra.SubmersivePresentation.basisKaehler`, and the standard-smooth free-differentials
  theorem. Read the standard-smooth candidate: it assumes finite presentation and supplies
  ordinary differentials, not a choice of coefficient section or completed generic bases.
- `msearch.py loogle`, query `KaehlerDifferential, AdicCompletion`: zero hits.
- `msearch.py grep`, query `coefficient.*[Ff]ield|[Cc]ompleted.*[Dd]ifferential`,
  subdirectory `RingTheory`: one unrelated Laurent-series completeness hit.
- `msearch.py leansearch`, query `complete local ring coefficient field basis completed
  Kahler differentials at every minimal prime`: eight hits, involving ordinary localized
  differentials, polynomial bases, and cotangent-space dimensions; none states this result.
- `rg` of the upstream `WeilConjectures` tree and `lean/Sheaf` for coefficient fields,
  generic differential bases, and completed differentials: only unrelated arithmetic
  coefficient-field and smooth/ordinary differential material. A literal grep for this
  node id upstream finds nothing. The proposed two declaration names also have no hits.
- Searched `dag/lean_names_upstream.json` for these notions: no match.
- `tools/blueprint_refs.py search coefficient differential basis`: two unrelated matches
  (strict coefficient packages and a supertrace lemma), neither states this assertion.
- The node already has the Mathlib notions it needs; the helper is just the exact
  conclusion written as a predicate, expressly allowed as an owning-node helper.

Validation: the required `scompile.py NH lem-per-coefficient-field-generic-differential-basis`
wrapper compiled the sandbox and actual module form cleanly, including all available
proof imports, in about 2–3 seconds each. No warnings, unbound variables, or extra
postponed declarations. Every theorem proof is exactly `by sorry`; definitions have real data.

## Second reading by NH

No independent worker reading was performed: this dispatch explicitly forbids starting
other agents and requires direct delivery. The maintainer's independent review will read
this delivery. As an author self-check, I reread the node and final module clause by clause.
The final file uses the actual maximal ideal and canonical residue map, adds the required
component-dimension hypothesis, uses the canonical fraction field of each quotient,
binds the Kähler algebra structure to the existential section, and requires each basis
vector to be precisely the image of the corresponding differential. I removed the
preliminary scratch structure and its vacuous compatibility field. The table above
records all hypotheses and clauses, including both optional-constants cases. No claim
of an independent second reader is made.
