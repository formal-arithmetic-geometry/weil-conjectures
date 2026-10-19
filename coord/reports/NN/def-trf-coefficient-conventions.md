## Worker report

The module `Sheaf.Paper.TraceFormulaCoefficientConventions` implements the current blueprint convention paragraph (main-20261015, `sec-six-functors-basics/sk-def-sf-admissible/def-trf-coefficient-conventions.md`). Its primary declaration is `WeilConjectures.TraceFormulaCoefficientConventions`. Every definition has actual data; there are no new postponed theorems or `sorry`s. Only the item's `lean` record is changed; no statement correction or new dependency node is needed.

The source hypotheses and clauses correspond as follows.

- The field `datum : FiniteFieldDatum` supplies `p,a,q,k₀,k`, primality, the positive exponent and `q=p^a`, and the finite base field and its algebraic closure.
- `coefficients : datum.CoefficientDatum` supplies the prime `ℓ`, `ℓ ≠ p`, and a fixed algebraic closure of `ℚ_ℓ` with its algebra structure.
- `extension : Padic.FiniteCoefficientFields ...` is a finite intermediate field of that fixed closure. `coefficientField` is the existing `AlgebraicallyClosedCoefficients.Coefficient` model, canonically algebra-equivalent to that field by `Shrink.algEquiv`. This is the same field with transported scalar structure, not an arbitrary replacement extension.
- `level : ℕ` and `level_pos : 1 ≤ level` render exactly `n ≥ 1`. `coefficientRing` uses `Padic.coefficientExtensionRing` on that finite field and exponent, hence the existing valuation ring, uniformizer and quotient `O_E/ϖ_E^n`.
- `X₀ : Over (Spec k₀)` and the `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` instance fields render a separated finite-type base scheme. `geometricBaseChange` and `structureMap` are the actual recorded `FiniteFieldDatum.geometricFiber` and its structure map. The three geometric instances merely apply Mathlib's pullback instances to the given properties.
- The ambient `proEtaleDerivedCategory` uses the intrinsic modules over the constant ring on `Scheme.ProEt.topology`, the small pro-etale site. `boundedConstructible` reuses `intrinsicFiniteTorsionConstructible`; its full subcategory is `D^b_c(X,A)`. `boundedConstructibleFiniteTor` reuses `finiteTorConstructible`, retaining the additional finite-Tor condition.
- `derivedPullback`, `derivedTensor`, and `derivedInternalHom` specialize the recorded finite operations. The dependency numbers positive levels as `m+1`; `Nat.sub_add_cancel level_pos` identifies `m=n-1` without restricting the source's `n`. Internal Hom has contravariant first input and is ambient, so no unwarranted closure condition is asserted.
- `cohomologySheaf T i` is `DerivedCategory.homologyFunctor` of the actual pro-etale module-sheaf category, for every integer `i`.
- `pointFibre` is precisely `pointFiniteFibre`, whose domain is `D^b_c(s,A)` and codomain is the full subcategory `DerivedCategory.pointFiniteCohomology (ULift A)`, the recorded `D^b_fin(A)`. The `ULift` is the dependency's coefficient and module universe transport.
- For every `K : T.boundedConstructible.FullSubcategory`, `compactSupportComplex` is the second component of `finiteConstructibleSections`: literally `pointFiniteFibre` applied to the actual `sfIntrinsicCompactSupport` image, with the recorded preservation proof. Its codomain retains boundedness and finite cohomology. An explicit compactification supplies the dependency's representative of `Ra_X!`; it is an argument to that representative helper, not an extra field or assumption on the convention datum or on `K`.
- For every `i : ℤ`, `compactSupportCohomology` applies `DerivedCategory.coefficientFiniteCohomology _ i` to that exact complex. Thus the displayed formulas are `RΓ_c=Fib_s(Ra_X! K)` and `H_c^i=H^i(RΓ_c)` with no arbitrary replacement map.

Dependency declarations read and reused: `Sheaf.Paper.FiniteFieldFiber` (`FiniteFieldDatum`, `CoefficientDatum`, `geometricFiber`); `Sheaf.Paper.FiniteCoefficientPoint` (`pointFiniteFibre`); `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility` (`intrinsicFiniteTorsionConstructible`); `Sheaf.Paper.FiniteTorAmplitude` (`finiteTorConstructible`); `Sheaf.Paper.DerivedPullbackTensorHom` (`finiteDerivedPullback`, `finiteIntrinsicDerivedTensor`, `finiteIntrinsicDerivedInternalHom`); `Sheaf.Paper.OrdinaryCompactCohomology` (`finiteConstructibleSections`, `finiteConstructibleImages`); `Sheaf.Paper.CoefficientCohomologyModules` (`DerivedCategory.coefficientFiniteCohomology`); `Sheaf.Paper.AlgebraicallyClosedCoefficients` (`Coefficient`). The recorded cohomology dependency imports the general Mathlib `DerivedCategory.homologyFunctor`, which is used on finite-coefficient sheaves. Mathlib's `Scheme.ProEt.topology` and the existing scheme morphism property classes supply the remaining conventions; there is no duplicate site or coefficient category.

Edge cases checked: exponent one is included (the operation index becomes zero); exponent zero is excluded exactly as in the source. Zero complexes and empty schemes are allowed; connectedness, nonemptiness, smoothness and properness are not assumed. Negative and arbitrary positive cohomology degrees remain available. `D^b_ctf` is not conflated with all of `D^b_c`, and the compact-support input requires only the latter. The extension may equal the base coefficient field. No extra coefficient flatness or equality of site object and morphism universes is imposed.

Searches made: `msearch.py leanfinder "finite field coefficient conventions bounded constructible finite Tor pro-etale compact support cohomology"` returned eight unrelated declarations; `loogle "FiniteFieldDatum, CoefficientDatum, finiteTorConstructible, ordinaryCompactCohomology"` rejected unknown project names, so it was followed by the valid query `loogle '"constructible"'`, which returned twelve topological constructible-set lemmas, none of this notion. `msearch.py grep "coefficient.*convention|TraceFormulaCoefficient|trfCoefficient"` returned one unrelated meromorphic coefficient convention. `rg` searches in upstream `WeilConjectures/` and shared `lean/Sheaf/`, and `grep -rn` for the item id upstream found no complete equivalent. `TraceFormulaCoefficientSetup` was read: it bundles additional compactification, triangulated-structure and preservation data and is not this convention paragraph. These searches confirm that the existing component notions can be reused, but there is no exact existing declaration for the bundle and displayed formulas.

No `STATEMENT-DISPUTED` issue was found. All variables and universes are explicit. Validation uses only the prescribed `scompile.py` single-file wrapper and `deliver2.py` preflight/compile workflow.

## Second reading by NN

(Replaced by the maintainer's independent reviewer under H11; the original four-sentence
section did not match the node's clauses with the Lean. No Lean, node or record change.)

Source place: `literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-admissible/def-trf-coefficient-conventions.md`
(order 1511), textually identical to `main-20261015/.../sec-six-functors-basics/sk-def-sf-admissible/`
(order 1870) cited in the module docstring. The node statement adds only citations and binds `K`, `i`, `s`.

Node clauses and their Lean (`Sheaf.Paper.TraceFormulaCoefficientConventions`):

1. Global finite-field datum `p,a,q,k₀,k` [def-weil-finite-field-fiber]: field `datum : FiniteFieldDatum.{u}`
   (the recorded structure). Correct.
2. Prime `ℓ ≠ p` and fixed algebraic closure `Q̄_ℓ`: `coefficients : datum.CoefficientDatum`
   (`l`, `Fact l.Prime`, `different : l ≠ D.p`, `Qbar` with `IsAlgClosure (Padic l) Qbar`). Correct.
3. Finite `E/Q_ℓ` inside `Q̄_ℓ`: `extension : Padic.FiniteCoefficientFields l Qbar`; `coefficientField`
   is the recorded small model `AlgebraicallyClosedCoefficients.Coefficient l Qbar E`, exactly what
   `finiteConstructibleSections` (def-weil-ordinary-compact-cohomology) consumes. Correct.
4. `n ∈ Z_{≥1}`, `A = O_E/ϖ_E^n`: `level : ℕ`, `level_pos : 1 ≤ level`;
   `coefficientRing = Padic.coefficientExtensionRing l E n`, the ring of every finite dependency. Correct.
5. `X₀` separated finite-type over `k₀` [def-weil-scheme-morphism-properties: finite type =
   `LocallyOfFiniteType` + `QuasiCompact`]: `X₀ : Over (Spec k₀)` with the three instance fields.
   Nothing stronger. Correct.
6. `X = X₀ ×_{k₀} k`, `a_X : X → Spec k`: `geometricBaseChange`, `structureMap` are the recorded
   `FiniteFieldDatum.geometricFiber` and its `hom`. The three geometric instances are derived by
   Mathlib pullback instances (not assumed). Correct.
7. Small pro-etale site: every category is `proEtaleDerivedCategory X A` over `Scheme.ProEt.topology`
   (the record of def-weil-pbc-proetale-site). Correct.
8. `D^b_c(X,A)`: `boundedConstructible = intrinsicFiniteTorsionConstructible …` (recorded declaration).
   Correct.
9. `D^b_ctf(X,A)`: `boundedConstructibleFiniteTor = finiteTorConstructible …` (recorded; kept distinct
   from item 8). Correct.
10. Derived pullback, tensor, internal Hom: `finiteDerivedPullback`, `finiteIntrinsicDerivedTensor`,
    `finiteIntrinsicDerivedInternalHom` at index `n-1`, transported along `n-1+1 = n` (an equality cast,
    not a choice). Internal Hom contravariant in the first argument. Correct.
11. Cohomology sheaves: `DerivedCategory.homologyFunctor _ i`, the Mathlib match of
    def-weil-derived-cohomology-sheaves (publicly re-exported by its recorded module). Correct.
12. `Fib_s : D^b_c(s,A) → D^b_fin(A)`: `pointFibre = pointFiniteFibre …` (recorded; codomain
    `pointFiniteCohomology (ULift A)`, the dependency's own universe transport). Correct.
13. `RΓ_c(X,K) = Fib_s(Ra_{X!}K)` for `K ∈ D^b_c(X,A)`: `compactSupportComplex c K` is the second
    component of the recorded `finiteConstructibleSections`, i.e. `pointFiniteFibre` of the
    `sfIntrinsicCompactSupport c` image. The compactification `c` is the argument that the recorded
    dependency takes (`Compactification (Y ↘ Spec k)`, Nagata). It is data, not a hypothesis on `X₀` or `K`.
    Correct.
14. `H^i_c(X,K) = H^i(RΓ_c(X,K))` for every `i : ℤ`: `DerivedCategory.coefficientFiniteCohomology _ i`,
    which the recorded `finiteConstructibleCohomology` uses too. Correct.

Edge cases: `n = 1` is allowed (the operations use index 0), and `n = 0` is excluded as in the source.
Empty `X₀`, zero complexes and all integer degrees are allowed. `E = Q_ℓ` is allowed. No ℓ-invertibility,
smoothness, properness, connectedness or flatness assumption is added. The universes are the dependencies'
(`Qbar : Type u` from `CoefficientDatum`), so no new universe equality is imposed.

Searches: `TraceFormulaCoefficientSetup` (record of sk-d-setup) is a different package (geometric
`k`-schemes with chosen compactifications, triangulated/preservation data), so it is not a duplicate.
No node records `TraceFormulaCoefficientConventions`. Grepping the side `lean/Sheaf` and the upstream
`WeilConjectures` for `CoefficientConvention` found no other bundle. The worker's Mathlib searches are recorded above.

Compile: `nt_compile.py` of the module exits 0 with no diagnostics (about 6 s). The module has no `sorry`
and no theorem. Every declaration has real data and a docstring with `(blueprint: def-trf-coefficient-conventions)`.
The node differs from the base only in `lean`. `lean.statement` is verbatim and `lean.declarations` lists all 17 declarations.
