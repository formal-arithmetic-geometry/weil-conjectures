## Worker report

States `WeilConjectures.separable_valued_completion_factors` in
`Sheaf.FieldTheory.SeparableValuedCompletionFactors`. The single theorem has a
`sorry` proof. There are no new definitions, new nodes, dependency repairs, or
statement corrections. Only the item's `lean` field changes.

Source checked: Temkin, *Stable modification of relative curves*, section 2.1
and Proposition 2.2.1, proof, printed pp. 11--12, especially the semilocal
normalization and completed-factor paragraphs:
https://arxiv.org/html/0707.3953v3#S2.SS2. The theorem docstring includes all
eleven steps of the DAG's proof, including their named dependencies.

The statement dependencies and their declarations were read before writing:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs; the inherited field
  structure in `NontriviallyNormedField F`, and `[Field E]`.
- `def-trf-valuation-ring`: `ValuationRing` and `ValuationRing.TFAE`,
  Mathlib.RingTheory.Valuation.ValuationRing. We use the existing bundled
  `ValuationSubring`; its existing `ValuationRing`, `IsLocalRing`, and field
  inclusion instances provide the dependency's notion, with no private copy.
- `def-weil-pbc-separable-algebraic-extension`: `Algebra.IsSeparable`,
  Mathlib.FieldTheory.Separable, publicly imported through Field.WithAbs.
  Its definition includes algebraicity, since a zero minpoly is not separable.
- `def-weil-pbc-integral-closure`: `integralClosure` and `IsIntegral`,
  Mathlib.RingTheory.IntegralClosure.Algebra.Basic. We use `integralClosure A E`
  itself throughout, and the existing `IsIntegral` for completed extensions.
- `def-weil-pbc-henselian-terminology`:
  WeilConjectures.Mathlib.RingTheory.Henselian, publicly importing Mathlib's
  `HenselianLocalRing` and `HenselianRing`. The record's note identifies these
  as its henselian notions. No strictly henselian hypothesis is imposed.

Hypotheses and clauses, in full:

| Node text | Lean rendering |
| --- | --- |
| Field F with a nontrivial real multiplicative absolute value | `F : Type u`, `[NontriviallyNormedField F]`; the absolute value is `‖·‖`. Any given real absolute value supplies precisely this normed-field structure. |
| Nonarchimedean inequality | `[IsUltrametricDist F]`, equivalent to `‖x+y‖ ≤ max ‖x‖ ‖y‖`. |
| A is its valuation ring, elements of absolute value at most one | `A : ValuationSubring F`, `hA : ∀ a : F, a ∈ A ↔ ‖a‖ ≤ 1`. This characterizes the specified ring; it does not choose another valuation or impose an additional restriction on F. |
| Finite separable E/F | `[Field E] [Algebra F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]`. |
| Integral closure C | Literally `integralClosure A E`, whose carrier is `IsIntegral A`. |
| Metric completion of F | `UniformSpace.Completion F` with Mathlib's completed norm and field structure. |
| Valuation ring Â of the completed field is henselian | Existential `Â : ValuationSubring (Completion F)`, the exact unit-ball membership equivalence, and `HenselianLocalRing Â`. Â is characterized as a subring, so there is no arbitrary choice of a valued field. |
| In every finite extension, its integral closure is the unique extending valuation ring | Universal `H : Type (max u w)`, field and completed-base algebra instances, finite dimensionality; an extending `W` whose membership is equivalent to `IsIntegral Â`, with uniqueness among all extending valuation subrings. No separability is required of H. |
| Finitely many distinct maximal ideals, all maximal ideals, nonempty list | `r : ℕ`, `0 < r`, `m : Fin r ≃ MaximalSpectrum (integralClosure A E)`. The equivalence is both injective and exhaustive. The zero-based indices are just a relabeling of 1,...,r. |
| C localized at m_i | `W : Fin r → ValuationSubring E`, with membership precisely `∃ c s : integralClosure A E, s ∉ (m i).asIdeal ∧ z = (c:E)/(s:E)`. The denominator condition excludes zero since m_i is proper. Thus this is the actual subring C_m inside E, not an abstract isomorphic ring. |
| Exactly the valuation rings extending A | `V.comap (algebraMap F E) = A ↔ ∃ i, V = W i`, for every valuation subring V of E. |
| Residue fields C/m_i | `Nonempty (IsLocalRing.ResidueField (W i) ≃+* (C ⧸ (m i).asIdeal))`. This states an isomorphism of the actual residue fields. |
| Unique inducing absolute value extending the base one | `b : Fin r → AbsoluteValue E ℝ`; restriction to F is its norm; each b_i satisfies the nonarchimedean inequality and has unit ball W_i. Every absolute value with the same restriction and unit ball equals b_i. |
| Valued fields E_i and their dense metric completions | `(b i).Completion` is the existing abbreviation `UniformSpace.Completion (WithAbs (b i))`; its norm and dense canonical embedding are Mathlib's, not an arbitrary complete field. The coercion `(x : (b i).Completion)` is the constant-element map. |
| Canonical completed-base inclusions | Ring homomorphisms `j i` are required, at every completed element a, to equal `Completion.map` of `(WithAbs.equiv (b i)).symm.toRingHom.comp (algebraMap F E)`. The restriction equality makes the original map isometric, hence uniformly continuous, so this is precisely its canonical continuous extension. |
| Integral closure in Ehat_i is its closed unit ball | The explicit `@IsIntegral` uses the composite of the canonical `j i` with `Â.subtype`, and is equivalent to `‖z‖ ≤ 1`. |
| Canonical completed tensor-product algebra isomorphism | `Φ` is an actual `@AlgEquiv` over `Completion F`. The source uses existing `Algebra.TensorProduct.rightAlgebra`; the target uses `(RingHom.pi j).toAlgebra`. Its equation on every `x ⊗ₜ[F] a` is `(x : (b i).Completion) * j i a`, coordinate by coordinate. |
| Integral primitive x | `x ∈ integralClosure A E` and `IntermediateField.adjoin F {x} = ⊤`. |
| Monic minimal polynomial f over A | `f : Polynomial A`, `f.Monic`, and `f.map (algebraMap A F) = minpoly F x`. |
| Factorization f = product f_i over the completed base | `g : Fin r → Polynomial Â`, all monic, and equality between the coefficientwise image of `minpoly F x` and `∏ i, (g i).map (algebraMap Â (Completion F))`. |
| Each f_i is the minimal polynomial of x_i | Each mapped `g i` equals the existing `@minpoly` over `Completion F` at the canonical image of x, with scalar algebra `(j i).toAlgebra`. |
| Degree is the completed extension degree | `(g i).natDegree = @Module.finrank ... (j i).toAlgebra.toModule`, using exactly the same canonical scalar map. Finiteness of each factor follows from the displayed algebra isomorphism from a finite-dimensional tensor algebra; it is not an extra assumption. |
| All roots have absolute value b_i(x) | For every algebraic closure Ω of the completed base, and every real absolute value c extending its norm, `Polynomial.aeval β` of the mapped factor equal to zero implies `c β = b i x`. |

The independent universes `u`, `v`, `w` are explicit. Test extensions and
algebraic closures range over `Type (max u w)`, never a universe below the base.
No site universe equality, characteristic restriction, completeness of F,
Noetherian condition, discrete valuation, or finiteness of C over A is assumed.
The explicit instance arguments avoid any file-local instance or notation and
ensure that every minpoly, degree, and integral-closure condition uses the same
completed-base scalar inclusion. There are no `let` expressions in the signature.

Proof imports follow the existing records: `ValuationValueGroupTorsion`,
`FiniteSeparableTensorFieldReduced`, the upstream
`ReducedNoetherianTotalRingFractions`, `HenselianLocalRootLifting`, and
`ValuationRingNormal`, together with Mathlib's tensor bases/finite base change,
spectral norm/uniqueness, finite-dimensional completeness, integrally closed
minpoly descent, and `IntermediateField.adjoinRootEquivAdjoin`. The last module
is public because `IntermediateField.adjoin` occurs in the statement. The two
proof-only nodes `lem-trf-valuation-normalization-localizations` and
`lem-zl-finite-separable-tensor-primitive-presentation` have no recorded Lean
module in the read clone; they introduce no missing statement notion here, so
there is no invented import or unnecessary dependency restatement.

Edge cases checked before writing and again against the final signature:

- E=F: there is one factor. The completed-base henselianity clause is retained,
  including when this identity extension is used by downstream consumers.
- E=F and x=0: the primitive condition holds, the minimal polynomial is T,
  and the root-norm conclusion includes 0=0. No nonzero-x condition appears.
- x a scalar in the identity extension, including x=1: monic degree-one
  polynomials and the single-factor product are allowed.
- Multiple places: m enumerates all distinct maximal ideals, with a separate
  absolute value and completion for each, not just a prescribed valuation.
- r=0 is excluded exactly by the node's r≥1, not by a hidden index instance.
- Purely inseparable finite H over the completed base is included in the
  universal integral-closure/unique-valuation clause; only E/F is separable.
- Positive characteristic, nondiscrete rank-one absolute values, incomplete F,
  and non-Noetherian A are all permitted. Finite normalization is not assumed.

Searches (2026-10-24):

- `msearch.py ... leanfinder "Finite separable field extension tensor product
  completion is product of completions at extensions of a nonarchimedean
  absolute value"`: eight hits. Number-field completions/adeles are special
  cases; `AbsoluteValue.Completion.extensionEmbedding_of_comp` is only an
  embedding interface, not the theorem. The pinned source read locally and
  with `scompile.py --source Mathlib.Analysis.Normed.Field.WithAbs` supplies
  `AbsoluteValue.Completion` but not that search-index embedding declaration.
  The final statement uses the pinned `Completion.map` directly.
- `msearch.py ... loogle "AbsoluteValue, UniformSpace.Completion,
  ValuationSubring"`: zero hits.
- `msearch.py ... grep "Completion.*tensor|tensor.*Completion|def.*valuationSubring|def.*toNormedField"`:
  21 hits, including absolute-value normed-field construction, valuation
  subrings, and adic tensor-completion results; none state this theorem.
- `msearch.py ... leansearch "finite separable valued field tensor product
  with completion decomposes as a finite product of completions"`: eight
  hits on algebraic tensor products, separable degrees, and étale algebras.
  `Algebra.Etale.iff_exists_algEquiv_prod` decomposes finite étale algebras
  abstractly, without the specified completions, valuation rings, or root norms.
- `rg` of `separable.*completion|completion.*separable|Completion.*tensor|
  tensor.*Completion|separable_valued_completion_factors` in both
  `lean/WeilConjectures` and `lean/Sheaf`: no exact valued-field theorem;
  hits concern unrelated adic, nodal, or categorical completions.
- `rg` of the exact blueprint id in `lean/WeilConjectures`: no match.
- `tools/lean_names_upstream.py show lem-trf-separable-valued-completion-factors`:
  no declaration binding for this item. No repair note exists for this item.

Compilation: `scompile.py Q42 lem-trf-separable-valued-completion-factors
<file>` passed in module mode both as `Sheaf.Stage2.Sandbox0` (16.1 seconds)
and as `Sheaf.FieldTheory.SeparableValuedCompletionFactors` (7.4 seconds),
without errors or unexpected warnings. Initial elaboration identified public
imports needed for `IsUltrametricDist` and the completion's normed-field
instances; those imports were added, without changing any hypotheses.
The dry-run and final delivery additionally compile the delivered file.

No mathematical dispute or node fault was found.

## Second reading by Q42

This is the worker's separate second pass; the dispatcher explicitly prohibits
starting another agent, and the maintainer supplies the independent review.
I reopened the node and the final module and checked each clause in the table.
The formerly easy-to-miss clauses are present: exhaustive distinct maximal
ideals, the actual localization subrings and their residue fields, uniqueness
of normalized absolute values, henselianity, all finite completed-base extensions
including inseparable ones, and all conjugate roots including x=0.

I also traced the canonical scalar maps through the actual `@AlgEquiv`,
`@minpoly`, `@Module.finrank`, and `@IsIntegral` arguments. All use the same
j_i, which is fixed pointwise to `Completion.map` of the original inclusion.
Thus the product isomorphism is the specified completed-base algebra map,
and no abstract map or choice of unrelated complete fields substitutes for it.
The typecheck confirms the statement has no unbound implicit variables.
No semantic correction was needed. Only the two missing public-instance imports
were repaired during compilation. The final docstring retains the complete
original proof plan with its TeX, rather than stripping mathematical commands.
