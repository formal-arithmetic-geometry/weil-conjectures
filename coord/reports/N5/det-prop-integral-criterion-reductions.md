## Worker report

The module `Sheaf.Paper.IntegralCriterionReductions` states
`AlgebraicGeometry.ProEtale.integral_reductions_constructible_iff` and the final integral-category interpretation
`AlgebraicGeometry.ProEtale.continuousIntegralConstructible_iff_first_reduction`.
Every theorem has exactly `by sorry` as its proof. The main proof docstring gives the eight
steps of the node's proof, including the quotient-ring actions in the induction triangles.
The mathematical statement is unchanged. Two new definition-node records expose the existing
coefficient presentations and finite-projection normalization. Both use `existing: true`; no
coefficient construction is copied. The unused pullback theorem is removed from `stmt_deps`.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| A prime ell | `(l : ℕ) [Fact l.Prime]` |
| Finite field extension E / Q_ell | `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]` |
| Its valuation ring, chosen uniformizer and quotients | The existing `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, `coefficientExtensionRing`; `DerivedNakayama.integerRing` and `quotientRing` use their continuous condensed coefficient sheaves. There is no arbitrary coefficient datum. |
| X Noetherian | `(X : Scheme.{u}) [IsNoetherian X]` |
| Small pro-etale site and pulled-back coefficients | `AdicCompletion.Modules l E X` is internal modules over `condensedRingObj (DerivedNakayama.integerRing l E) X` on `Scheme.ProEt.topology X`. |
| K in the unbounded integral derived category | `(K : DerivedCategory (AdicCompletion.Modules l E X))`; there is no boundedness assumption on K. |
| K derived pi-complete | `(_hK : IsDerivedComplete l E X K)` retains the recorded canonical augmented Roos completeness condition. Its underscore only suppresses unused-variable diagnostics; the hypothesis is present. |
| K_n is derived extension to the finite quotient | `(AdicCompletion.derivedReduction l E X n).obj K` denotes the source's K_(n+1). This is the existing derived extension along the actual quotient morphism. |
| Clause (1), K_1 bounded constructible | `constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X ((AdicCompletion.derivedReduction l E X 0).obj K)` |
| Clause (2), all n >= 1 bounded constructible | `∀ n : ℕ, constantModelBoundedConstructible (DerivedNakayama.quotientRing l E (n + 1)) X ((AdicCompletion.derivedReduction l E X n).obj K)` |
| One interval independent of n | `∃ r s : ℤ, r ≤ s ∧ ∀ (n : ℕ) (q : ℤ), q < r ∨ s < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj ((AdicCompletion.derivedReduction l E X n).obj K))` |
| Equivalence of (1) and (2) | The first theorem's `↔` has precisely the first-reduction predicate and the conjunction of all-reduction constructibility and the common interval. |
| Final integral-category interpretation | The second theorem identifies `continuousIntegralConstructible l E X K` with the first-reduction predicate under the same hypotheses. The predicate and subcategory are helpers owned by this item. The comparison theorem identifies this predicate with the unchanged landed `sfIntegralConstructible` through the specified section-action derived equivalence. |

Here `constantModelBoundedConstructible` is the recorded declaration of
`sk-def-sfb-constructible`, not upstream's broader locally finitely presented predicate.
For the positive finite quotient rings its finite constant scalar models agree with
finite local module models and the finite geometric-stalk convention of
`def-weil-proetale-constructible-sheaf`. Indeed a finitely presented module over a finite
ring is finite, and a finite module has a finite presentation: choose finite generators,
then the kernel of the resulting finite free surjection is finite. On a Noetherian scheme
the global finite stratification convention applies. This is step 2 of the DAG proof.
No Tor-amplitude clause or invertibility of ell on X is assumed or asserted.

Statement dependencies read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`, importing the existing integer ring, uniformizer and quotient constructions.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `AlgebraicGeometry.ProEtale.coefficientRing`, `condensedRingObj`, `upperStarFromPoint` and their monoidal structure. Read from the specified shared framework and its framework manifest.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt` and `ProEt.topology`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`; the internal-module presentation is the published one in `AdicCompletion.Modules`, rather than a second sectionwise module construction.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.SixFunctors.ProEtale.DerivedCompletion`: `AlgebraicGeometry.ProEtale.IsDerivedComplete`, `AdicCompletion.Modules`, `finiteRing`, `quotient`, `FiniteDerived`, `derivedReduction` and the actual Roos augmentation.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`: `SheafOfModules.DerivedChangeOfRingsCochainModel` and `nonempty_derivedChangeOfRingsCochainModel`, the general K-flat derived-extension interface. The specialization used in the signatures is the already-published internal `AdicCompletion.derivedReduction`.
- `Sheaf.Paper.CondensedConstantConstructibility`: `HasFiniteConstantLocalModel`, `IsConstantModelConstructible`, `constantModelBoundedConstructible`.
- `Sheaf.Paper.ProEtaleConstructibleSheaf`: `AlgebraicGeometry.Scheme.IsConstructibleProEtaleModuleSheaf`, for the finite-stalk convention and proof.
- `Sheaf.Paper.SfIntegralConstructible`: the unchanged recorded dependency
  `WeilConjectures.sfIntegralConstructible` and `sfIntegralConstructibleCategory`.
- `Sheaf.CategoryTheory.InternalSectionTensorComparison`: the existing
  `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence` and additive
  section-action comparison.
- `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`:
  `sfb_integral_coefficient_limit`, its unique comparison with all finite projections.
- `Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback`:
  `SfbIntegralComparison`, precisely the existing monoid/adjunction-mate/finite-projection
  normalization, now cited through its dedicated definition node.

The new definition records are `def-sfb-integral-comparison-coefficients` (the existing
integral-limit module and its nine supporting definitions) and
`def-sfb-integral-comparison-normalization` (the existing pullback module and
`SfbIntegralComparison`). Their records do not assert either theorem. The integral-limit
theorem remains a proof dependency; the pullback theorem is unused.

All recorded statement-dependency modules and all available recorded proof-dependency
modules are imported, using non-public imports for proof-only modules. The proof node
`det-prop-integral-criterion-constant-coefficients` has no recorded Lean module, so no
import can yet be added for it. No import cycle is introduced by these new modules.

Edge cases checked: empty X and the zero complex are allowed; a degenerate interval
r=s is allowed, as are negative endpoints; there is no requirement of nonzero
cohomology anywhere in the interval. Index 0 denotes exponent 1, so all and only positive
exponents are quantified; the zero exponent quotient is not accidentally included.
All primes, including ell=2 and residue-characteristic ell schemes, are admitted.
Nothing assumes ell differs from a characteristic of X. The final interpretation applies
in particular in the original global l != p setting; the intrinsic predicate has no p
parameter, as in its previous recorded interface. Object and morphism universes of the
small site are inherited from the published continuous-coefficient API and are not forced
to coincide. The finite extension and X use the ambient scheme universe, permitting the
usual common enlargement. No additional `Finite`, comparison-map or normalization
hypothesis is imposed on the user.

Searches, with the prescribed msearch wrapper (also recorded in searches.jsonl):

- LeanFinder: “The first derived reduction modulo a uniformizer has bounded constructible cohomology if and only if all reductions do with one uniform interval”. Eight unrelated PreTilt, Witt-vector and p-adic results; no constructibility-reduction criterion.
- Loogle: `"constructible"`. Twelve results about constructible subsets, not this theorem or the continuous integral predicate.
- Mathlib grep: `constructible.*reduction|reduction.*constructible`. No results.
- LeanSearch: “derived complete integral complexes with constructible reductions in a uniform cohomological interval”. Eight general derived-category boundedness/localization results; no integral constructible category or criterion.
- Project/source `rg`: `IsDerivedComplete l E|AdicCompletion.derivedReduction|AdicCompletion.Modules|sfIntegralConstructible|integralConstructible`; the current internal completeness module exists, while `sfIntegralConstructible` and its consumers use the other ambient module presentation. No continuous integral constructibility predicate or exact theorem was found.
- Upstream item-id search in `WeilConjectures`: no declaration tagged `det-prop-integral-criterion-reductions`.
- Exact-name searches in Mathlib, upstream `WeilConjectures`, project `lean/Sheaf` and `dag/lean_names_upstream.json`: none of the four proposed declaration names exists.

## Repair of immutable head 6b489a2b3917

1. **H5/H3, the impossible heterogeneous pin.** The old `HEq` compared a natural
   transformation valued in `CommRingCat` with one valued in `Ab`. It is removed.
   `integralSectionAbIdentifications` states the equality of the source and target
   abelian sheaves obtained by forgetting their reconstructed commutative ring
   structures. The proof plan checks the identical continuous-function sections and
   restrictions, the spectral topology, and the unchanged additive data in the
   completed ring. The pin in `integralSectionRingIso_existsUnique` is now an ordinary
   equality of abelian-sheaf morphisms: forget the ring map along
   `CommRingCat -> RingCat -> Ab`, and equate it with the existing normalized comparison,
   composed with `eqToHom` of those endpoint equalities. The equality proofs carry no
   choice of a map. Faithfulness of forgetting ring maps to additive maps then fixes
   the unique ring lift. Thus the selected ring isomorphism, actual section functor,
   derived equivalence and both comparisons with `sfIntegralConstructible` retain
   their specified underlying map. The new equality theorem is recorded in
   `lean.declarations`, with its source, blueprint tag and full proof docstring.
2. **The definition/theorem statement dependency.** The item's added theorem dependency
   `det-prop-sfb-qlbar-colimit-x-pullback` is dropped. The coefficient definitions and
   the normalization predicate get the definition-node records described below,
   referencing their exact existing published modules and declarations. This uses
   the brief's `existing: true` alternative: introducing another module containing
   copies of the definitions would violate one definition per notion. The new records
   contain no theorem declarations. The integral-limit theorem, which supplies the
   existence proof, stays only in the original `proof_deps` and is imported for that
   proof. All original dependency node records, including the N3 integral predicate,
   remain byte-identical to the shared repository. The main theorem and corollaries
   retain their previously accepted signatures.

## New nodes

`def-sfb-integral-comparison-coefficients` records the already published definitions
in `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`. Its main declaration
is `AlgebraicGeometry.ProEtale.sfbCondensedIntegers`, and its declaration list includes
`sfbCompletedIntegersAb`, the finite-label functors, the positive finite quotient
and profinite tower, the profinite integer object, the point adjunction and the
finite-representation comparison. Its statement explicitly defines these coefficient
presentations and support data, and asserts no integral-limit theorem. Source:
main-20261015 integral-limit proof, Steps 1--4, used in this item's step 8. The
continuous integer-ring construction is the existing specialization of continuous
condensed rings; the completed object is the underlying abelian sheaf of the actual
completed ring. Both are real existing data. The generic continuous-ring and
completed-ring nodes are cited, not duplicated.

`def-sfb-integral-comparison-normalization` records the existing predicate
`AlgebraicGeometry.ProEtale.SfbIntegralComparison` in
`Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback`. Its statement lists
both monoid-homomorphism conditions, the natural finite-label representation, the
limiting profinite cone, the exact quotient equations for its identification with
integers, and the adjunction-mate equation for every profinite S, continuous g and
positive quotient. It asserts no existence or inverse-image theorem. It cites the
preceding coefficient-data definition, and the item cites both new records. Source:
the same integral-limit proof, Steps 3--4. This is precisely the predicate already
used in the module, with no new comparison definition or arbitrary isomorphism.

For both nodes, fresh prescribed searches are copied verbatim from `searches.jsonl`
into `mathlib_searches`: LeanSearch on continuous condensed integers/inverse limits
returned eight general profinite-limit results; LeanFinder on the adjunction-mate
normalization returned eight unrelated integral-norm results; Mathlib grep on the
three exact helper names returned zero. Direct upstream `rg` returned zero; project
`rg` located the exact existing declarations above. The DAG-name search located only
helper entries in the two theorem nodes, with no independent definition node.
`blueprint_refs.py search 'integral comparison'` found two unrelated blueprint nodes;
`search 'projection-normalized'` found none. The exact existing project definitions
are therefore reused with `existing: true` records rather than stated twice.

## Second reading by N5

The dispatcher forbids starting another agent; this is my second reading, with the
maintainer's independent review still required. I reopened the original node,
main-20261015 statement/proof, the saved module, both helper-definition source modules,
and each new node. The main theorem retains finite E, Noetherian X, unrestricted K,
derived completeness, exponent n+1, all positive reductions, and r,s quantified before
n. It adds no Tor condition or invertibility assumption. The zero complex, empty X,
ell=2, negative endpoints and a one-degree interval remain included. Its recorded
signature is verbatim from the final file. The original N3 dependency record and
statement are unchanged; continuousIntegralConstructible stays owned by the item.

The return's pin mismatch was found again in the saved packet even though its dry
run passed. It is corrected by a same-category equality after explicit endpoint
transport. Reading the equality theorem against the source confirms that it identifies
additive data only: reconstructed sections keep the same abelian groups, the two
continuous coefficient constructions use the same spectral topology, and the completed
commutative structure keeps the existing ring data. The resulting pin determines every
component of the additive comparison, hence every ring-map component. No `HEq` remains.

I checked every clause of both new definition statements against its recorded existing
declarations. The first uses the actual continuous integer ring and the completed
finite quotient tower; the second has all of the existing normalization's quantifiers
and equations. Their `lean.statement` fields are the exact existing signatures.
Neither new statement asserts the theorem of the module housing those definitions.
Only `lean` and the additions of these definition nodes to `stmt_deps` change the item.
No statement correction, statement dispute, dependency module or new assumption occurs.

## Validation

The saved pre-repair packet passed the initial required dry run (81001f3c62), confirming
that mechanical preflight alone does not resolve the two returned semantic issues.
The repaired module compiled with the prescribed scompile.py in sandbox mode (11.8 s)
and library mode (5.9 s), with no compiler messages. Final delivery preflight and
per-file validation are run again after the new definition records and this report.
