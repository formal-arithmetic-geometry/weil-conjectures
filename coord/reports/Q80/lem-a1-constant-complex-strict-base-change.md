## Worker report

The delivery states the strict constant-complex comparison and its normalized auxiliary objects. `ConstantComplexQuotientModel.lean` owns the new definition node `def-a1-constant-complex-quotient-model`: `Quotient` renders A_n=R/I^(n+1), `coefficientTower` and `completed` render the inverse-limit coefficient sheaf, `constantModules` and `finiteComplex` render constant A_n tensor_R constant P with the original differential, and `FiniteTower` renders consecutive quotient maps. `ReductionData` renders balanced finite reductions, inverse and quotient-unit formulas, compatibility with scalar chain maps and differentials, and maps to the completed coefficients. `RoosAugmentation` renders the product map killed by 1-s, the strict mapping-cocone map, zero shifted component, and naturality. `FiniteComparison` renders levelwise inverse-image/tensor comparison and strict tower isomorphism; `FiniteComparison.derived` is the exact-functor factorization in the ambient derived categories. `GeometricReduction` renders the projection-defined completed coefficient map, completed pullback, normalized tensor comparison, and reduction square; it contains no inverse for that map.

The item theorem `strict_constant_complex_base_change` has the following clauses.

* `R`, `[CommRing R]`, `I`, and `hfinite : forall n, Finite (Quotient R I n)` are explicit ring, ideal, and finiteness hypotheses; `T`, `T'`, and `g : T' ⟶ T` are explicit.
* `dT` and `dT'` are source and target quotient towers; their `IsNormalized` clauses state semilinear quotient transitions on local tensor generators.
* `eT` and `eT'` are completed-limit reduction data; their `IsNormalized` clauses state the balanced map `(b tensor p) tensor a ↦ a * pr_n(b) tensor p`, its inverse/unit, consecutive transitions, scalar differentials, and chain-map naturality.
* `f : FiniteComparison g I dT dT'` is the levelwise inverse-image/tensor comparison. `f.IsNormalized` states the constant-section formula `a tensor p ↦ a tensor p`, differential and quotient-transition squares, scalar chain-map naturality, and strict tower component formula. `FiniteComparison.derived` uses the recorded exact pullback factorization, so no boundedness or K-flatness is added to the finite comparison.
* The two existential `RoosAugmentation` clauses state the strict signed cone with zero shifted-product component, product map, annihilation by `1-s`, and scalar-chain-map naturality. The existential `GeometricReduction` clause states the projection-defined completed coefficient map and normalized geometric reduction square; no `g^-1 B_T ≅ B_T'` is assumed.
* The final `forall n` clause records additivity, finite-limit preservation, and finite-colimit preservation of each exact constant-coefficient pullback.

The dependency declarations used are `AlgebraicGeometry.Scheme.ProEt`, `AlgebraicGeometry.Scheme.proEtaleSheafInverseImage`, `CategoryTheory.constantSheaf`, `CategoryTheory.Limits.limit` and `limit.π`, `SheafOfModules.restrictScalars`, `AlgebraicGeometry.Scheme.proEtaleConstantRingPullback`, `DerivedCategory`, `DerivedCategory.IsPerfectRingComplex`, `CategoryTheory.Functor.ofOpSequence`, and `WeilConjectures.integralOperationsRoosFunctor`. The landed constant realization used is `CategoryTheory.commutativeSiteConstantModuleFunctor` from `Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor`.

Edge cases checked: indexing starts at exponent n+1, so the first level is R/I; zero complexes and zero scalar chain maps are admitted; identity and arbitrary morphism cases use the same normalized constant-section formulas; no finite-free splitting, inverse-limit preservation by inverse image, or inverse of the completed coefficient map is assumed; the scheme morphism has no finiteness hypothesis. The `Finite` hypothesis is retained exactly as supplied by the item even where exactness itself does not use it.

Searches made: `msearch.py leanfinder` for the strict quotient/reduction notion (eight hits, all unrelated adic-completion/tensor declarations); `msearch.py loogle` for `CategoryTheory.constantSheaf, SheafOfModules.restrictScalars` (zero hits); `msearch.py grep` for `constant.*[Rr]eduction|[Rr]eduction.*constant` in Mathlib CategoryTheory (zero hits); repository `rg` searches found no exact strict constant-complex node or declaration. The searches are recorded in `searches.jsonl`.

## New nodes

`def-a1-constant-complex-quotient-model` supplies the missing quotient-complex, normalized reduction, strict Roos, and projection-defined geometric comparison notion. Its module is `Sheaf.Paper.ConstantComplexQuotientModel`; it is added to the item's `stmt_deps`.

## Dependency modules

None. Recorded dependency interfaces are used directly. The landed commutative-site constant module functor is added to `stmt_deps` because it is the existing canonical constant-module realization needed at the small pro-etale site.

## Second reading by Q80

I reread the item statement, source lemma, and both delivered modules. Every hypothesis and displayed clause is represented in the theorem or explicitly cited new quotient-model definitions. The arbitrary unbounded scalar complex is not restricted in the finite comparison, the bounded finite-projective condition occurs only in completed reduction clauses, original differentials and quotient transitions are retained, and the geometric completed coefficient map is only a map. The theorem is postponed with `sorry`; all definition data is constructed without `sorry`.
