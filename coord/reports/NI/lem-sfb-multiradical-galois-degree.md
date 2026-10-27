## Worker report

The module `Sheaf.FieldTheory.MultiradicalGaloisDegree` states
`IntermediateField.multiradical_galois_degree` with one `sorry` proof and no new
definitions. The original node statement, proof, dependencies, and metadata are
unchanged; only its `lean` record is supplied.

The source was read in `literature/stacks-project/fields.tex`, section-Kummer
(Tag 09I6), opening paragraph, lines 3218–3230. This states the single-root
Kummer character and its injectivity and degree divisibility. The node explicitly
asks for its finite-list product-character version, including n = 1 and r = 0.
The complete nine-step argument from the node is in the theorem docstring.

Hypotheses and objects, clause by clause:

- F is a field: `(F : Type u) [Field F]`.
- Ω is the chosen algebraic closure over F:
  `(Ω : Type v) [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]`.
  These universes are independently explicit; no equality of universes is imposed.
- The positive integer n: `(n : ℕ) (hn : 1 ≤ n)`. Natural-number encoding includes
  exactly the integers n ≥ 1 in the node.
- n invertible in F: `(hnF : IsUnit (n : F))`.
- X^n - 1 splits over F:
  `(hsplit : (Polynomial.X ^ n - 1 : Polynomial F).Splits)`.
- The finite list has length r ≥ 0: `(r : ℕ)`, indexed by `Fin r`.
- Each a_j is a nonzero element of F: `(a : Fin r → Fˣ)`.
- The chosen radicals in Ω: `(α : Fin r → Ω)` with
  `hα : ∀ j : Fin r, α j ^ n = algebraMap F Ω (a j : F)`.
- L = F(α_1,...,α_r) is used literally as
  `IntermediateField.adjoin F (Set.range α)`, the existing smallest intermediate
  field containing all the chosen radicals. No arbitrary extension is substituted.

Conclusions, clause by clause:

- Finite dimensionality is
  `FiniteDimensional F (adjoin F (Set.range α))`.
- Normality and separable algebraicity together are
  `IsGalois F (adjoin F (Set.range α))`. The source of `IsGalois` was read:
  its fields are exactly `Algebra.IsSeparable` and `Normal`. The recorded separable
  extension definition includes algebraicity. `Normal` means that every minimal
  polynomial splits, equivalently the irreducible-polynomial formulation of the node.
- μ_n(F) is the existing `rootsOfUnity n F`, the subgroup of units with n-th power 1.
  Its r-fold product is `Fin r → rootsOfUnity n F`, with pointwise multiplication.
- Gal(L/F) is `L ≃ₐ[F] L`, using this literal adjoin for both occurrences of L.
- The group homomorphism is quantified as `∃ χ : (L ≃ₐ[F] L) →* ...`, and its
  required coordinate formula is imposed for every σ and j. The j-th generator
  as an element of L is the actual subtype
  `⟨α j, subset_adjoin F (Set.range α) (Set.mem_range_self j)⟩`.
  Thus the formula is precisely the equality in Ω of the image of `(χ σ j).val`
  and `σ(α_j)/α_j`. The algebra map is injective and the inclusion of the subgroup
  of units into F is injective, so this formula specifies χ uniquely; the
  existential supplies the stated map rather than an unconstrained embedding.
- Injectivity is `Function.Injective χ`.
- Degree divisibility is
  `Module.finrank F (adjoin F (Set.range α)) ∣ n ^ r`.

Dependency interfaces read and used:

| Node | Module and declarations |
| --- | --- |
| def-weil-field | `Mathlib.Algebra.Field.Defs`: `Field` |
| def-weil-algebraic-closure | `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosure`; the recorded match explicitly permits this predicate on a chosen Ω as well as the canonical `AlgebraicClosure` type |
| def-pc-field-extension | `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `algebraMap` |
| def-weil-vector-space-dimension | `Mathlib.LinearAlgebra.Dimension.Finrank`: `Module.finrank` |
| def-weil-pbc-separable-algebraic-extension | `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable`, the separability field of `IsGalois` |
| def-weil-polynomial-ring | `Mathlib.Algebra.Polynomial.Basic`: `Polynomial` |

All statement interfaces are available through the three public imports. The
proof-dependency interfaces are supplied by those imports and the plain proof
import `Mathlib.FieldTheory.PurelyInseparable.Basic`: `Polynomial.Separable`,
`separableClosure`, `separableClosure.isSeparable`,
`separableClosure.isPurelyInseparable`, `Polynomial.card_rootSet_eq_natDegree`,
`Polynomial.IsSplittingField.finiteDimensional`, `Normal.of_isSplittingField`,
`IsGalois.card_aut_eq_finrank`, and `IsGalois.mem_range_algebraMap_iff_fixed`.
These are the recorded Mathlib matches; there are no project dependency modules
that need to be restated or repaired. The proof-only imports are retained for
stage 3. Existing Mathlib notions `IntermediateField.adjoin`, `rootsOfUnity`,
and `Polynomial.Splits` are used directly.

Edge cases checked mathematically before writing:

- r = 0: `Set.range α` is empty; its adjoin is the bottom intermediate field,
  canonically F. `Fin 0 → rootsOfUnity n F` has one element. The character formula
  quantifies over an empty type, the automorphism group is trivial, and the
  degree is 1 dividing n^0 = 1. These clauses are consequences of the actual
  objects used in the signature, with no nonempty-list assumption.
- n = 1: the radicals already lie in the image of F, rootsOfUnity 1 F is trivial,
  and the degree is 1. Both positivity and invertibility hold.
- Repeated radicals and reducible binomials: no irreducibility or distinctness
  assumption appears. For Q, n = 2, and two copies of sqrt(2), the degree is 2
  dividing 4. The proof uses normality of the product splitting field and does
  not incorrectly assert separability of that product.
- All a_j already n-th powers: degree 1 is allowed, and χ need only be injective,
  not surjective. This also explains why the irreducible single-binomial
  equivalence in Mathlib is not the complete statement.
- Positive characteristic is allowed whenever n is invertible. Cases with
  characteristic dividing n are excluded by exactly the stated hypothesis.
  Zero radicals are excluded by the units a_j and hα, not by a new assumption.

Searches performed using the prescribed msearch wrapper (raw outcomes remain in
`searches.jsonl` in the sandbox):

- LeanFinder: “Adjoining finitely many nth roots over a field containing all nth
  roots of unity gives a finite Galois extension with injective character and
  degree dividing n to the number of generators”. Eight hits, including
  `IsCyclotomicExtension.isGalois`, `exists_root_adjoin_eq_top_of_isCyclic`, and
  `autAdjoinRootXPowSubCEquiv`; none states the finite-list result. Cyclotomic
  extensions concern radicals of 1, and the single-binomial equivalence assumes
  irreducibility.
- Loogle: `IsGalois, rootsOfUnity`. No hits.
- Mathlib grep in FieldTheory:
  `autEquivRootsOfUnity|finrank_of_isSplittingField_X_pow_sub_C|multiradical`.
  Five hits, all in `KummerExtension.lean`. Read its declarations around lines
  389–456: the degree-equals-n and character-equivalence results use irreducibility
  of one binomial, hence cannot replace this theorem.
- LeanSearch: “A finite extension generated by finitely many nth roots admits an
  injective Kummer character into a product of groups of roots of unity”. Eight
  hits, including cyclotomic-character maps, `rootsOfUnity.coe_injective`, and
  single-binomial equivalences; no complete match.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for `multiradical|autEquivRootsOfUnity|finrank_of_isSplittingField_X_pow_sub_C`:
  only a proof use of the existing single-binomial theorem in TameRootExtension
  and a docstring reference to this item in TameRadicalNormalization; no
  declaration of this finite-list result or proposed declaration name.
- Required `grep -rn` for this item id in `lean/WeilConjectures`: no matches.

No statement correction, disputed statement, new nodes, dependency repairs, or
hollow definitions. All variables and universes are explicitly bound, and
`autoImplicit` is disabled. There is exactly one postponed theorem, matched to
this DAG node and carrying the complete natural-language proof in its docstring.

Validation: scompile.py compiled the file both as a sandbox module and at its
library module path against the live published build, 1.6 seconds each, exit 0,
without errors or warnings. The delivery dry run and final push follow below in
the tool transcript.

## Second reading by NI

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
