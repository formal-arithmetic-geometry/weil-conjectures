## Worker report

Group Q97, stage 2, item lem-sf-native-weil-open-closed-triangle, 2026-10-24 UTC.

This delivery records the exact existing statement
`AlgebraicGeometry.WeilComplex.exists_distTriang_openClosed` in
`WeilConjectures.WeilSheaf.LowerShriekFunctoriality`, lines 171–183.
The node already names this source theorem. No Lean module is introduced: the
one-definition-per-notion rule requires reusing it. Only the item's `lean` field
changes; its statement, dependencies and accepted proof split are untouched.
The source theorem's proof remains `sorry`; this is a statement attachment, not
a claim that the theorem is proved.

I read the entire source theorem and its docstring, its module's ambient variable
blocks (lines 59–60 and 143–146), and the actual definitions of the three functors.
`scompile.py --source WeilConjectures.WeilSheaf.LowerShriekFunctoriality` confirmed
the same theorem in the current server source. The Lean record's `statement` is
verbatim from `theorem` through the conclusion, stopping before `:=`; section
variables below are part of its elaborated type.

### Every hypothesis and conclusion

| Node text | Lean rendering |
| --- | --- |
| Finite field k₀ | `{k₀ : Type u} [Field k₀] [Finite k₀]` in the section |
| Prime ℓ distinct from the characteristic | `{l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]` in the section |
| Ω is the algebraic closure of the ℓ-adic numbers | The recorded framework uses `PadicAlgCl l` through `WeilCoefficients`, `ProEtale.AdicSheaf` and `ProEtaleWeilSheaf`; no arbitrary coefficient category is substituted |
| X, U, Z are k₀-schemes | `{X Y Z U : Scheme.{u}}` and each relevant `[W.Over (Spec (CommRingCat.of k₀))]`; the unused Y and its structure do not enter this theorem's elaborated type |
| X locally of finite type | `[LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]` |
| X quasi-compact | `[QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]`; since the base is affine, this is exactly quasi-compactness of X |
| X quasi-separated | `[QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]`; over a field this is the same as absolute quasi-separatedness, since the base is separated |
| Quasi-compact open immersion j:U→X | `(j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]` |
| j over k₀ | `[j.IsOver (Spec (CommRingCat.of k₀))]` |
| Closed immersion i:Z→X | `(i : Z ⟶ X) [IsClosedImmersion i]` |
| i over k₀ | `[i.IsOver (Spec (CommRingCat.of k₀))]` |
| Complementary images | `(hij : IsCompl (Set.range j.base) (Set.range i.base))`; disjointness and union equal to the whole space |
| Every K in WCᵈᵉʳ(X) | `(K : WeilComplex k₀ l X)` |
| A distinguished triangle S in the native category | `∃ T ∈ distTriang (WeilComplex k₀ l X), …` |
| S₁ ≅ Rj₀!j* K | `Nonempty (T.obj₁ ≅ (derivedLowerShriek k₀ l j).obj ((upperStar j).obj K))` |
| S₂ ≅ K | `Nonempty (T.obj₂ ≅ K)` |
| S₃ ≅ Ri*i* K | `Nonempty (T.obj₃ ≅ (derivedLowerStar i).obj ((upperStar i).obj K))` |
| Only vertex isomorphisms, no prescribed arrows or uniqueness | The three conjuncts say only `Nonempty` of isomorphism types; there are no equalities on `mor₁`, `mor₂`, `mor₃`, and no unique-existence quantifier |

In particular, the source docstring's warning that this is weaker than
`prop-sf-open-closed-triangle-all-stages` is consistent with this node, whose last
sentence deliberately asserts only the weaker vertex-existence statement. It is
not a mismatch with the assigned item. No statement correction or dispute is needed.

### Dependency declarations read and used

* `def-sf-native-weil-derived-framework` records
  `WeilConjectures.WeilSheaf.LowerShriek` and
  `AlgebraicGeometry.WeilComplex.derivedLowerShriek` as its public entry point.
  I read its definition (lines 145–160): it restricts the actual
  `ProEtaleWeilSheaf.rightDerivedLowerShriek` (lines 82–93), defined as termwise
  extension by zero followed by right-derived direct image, using
  `HasCompactification.compactification`. Thus the first vertex is the actual
  chosen-compactification functor of the framework.
* `WeilConjectures.WeilSheaf.Category` defines
  `WeilSheaf.frobeniusPullback`, `ProEtaleWeilSheaf`,
  `WeilSheaf.objectProperty`, `WeilComplex.objectProperty`, `WeilComplex`,
  `ProEtaleWeilSheaf.upperStar`, and `WeilComplex.upperStar`. I read their full
  signatures and docstrings. The category is the full subcategory of
  `DerivedCategory (ProEtaleWeilSheaf k₀ l X)` with bounded constructible
  cohomology. The underlying abelian category is `IsoAlgebra` for Frobenius
  pullback on adic sheaves, not fixed pairs in a different derived category.
  Pullback is the functor induced by exact termwise inverse image. Its shifts
  and pretriangulated structure are inherited from this full subcategory.
* `WeilConjectures.WeilSheaf.LowerStar`, `ProEtaleWeilSheaf.lowerStar`
  (lines 71–79) and `WeilComplex.derivedLowerStar` (lines 173–184), use the
  actual Frobenius-equivariant direct image and its total right derivation,
  then restrict to the bounded constructible full subcategory. The immersion
  instances supply its finite-type, quasi-compact and quasi-separated inputs.
* `WeilConjectures.WeilSheaf.OpenImmersion`,
  `ProEtaleWeilSheaf.extensionByZero` (lines 46–54), is the equivariant lift of
  geometric extension by zero, with the Frobenius comparison specified by the
  recorded framework.
* The framework's coefficient and constructibility declarations were also read:
  `ProEtale.AdicSheaf` in `SixFunctors.ProEtale.Adic.Module`,
  `ProEtale.adicConstantSheaf` and `PadicAlgCl.locallyFiniteFunctions` in
  `SixFunctors.ProEtale.Adic.ConstantSheaf`, and
  `ProEtale.IsAdicLisseSheaf`, `IsAdicStratifiedLisseSheaf`,
  `IsAdicConstructibleSheaf` in `SixFunctors.ProEtale.Adic.Constructible`.
  These are module objects over the locally finite continuous coefficient
  functions on the whole underlying space. The finite rank is existential
  separately for each covering member, as the framework requires.
* `def-weil-open-immersion`:
  `Mathlib.AlgebraicGeometry.OpenImmersion`, `AlgebraicGeometry.IsOpenImmersion`
  (lines 35–39), the locally ringed space open-immersion property.
* `def-weil-closed-immersion`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion` (lines 42–46), closed embedding plus
  surjectivity on stalks.
* `def-weil-quasi-separated-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`,
  `AlgebraicGeometry.QuasiSeparated` (lines 48–52), quasi-compact diagonal.
* `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType` (lines 39–46), and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`,
  `AlgebraicGeometry.QuasiCompact` (lines 38–46).

No dependency record requires repair. Because this is an existing declaration,
no new file or proof-plan imports are delivered. The existing accepted DAG proof
remains the seven-step plan: heart localization termwise; factorization comparisons
using a representative isomorphism; bounded constructible cohomology; the SES
triangle in the native category; verification of the actual compactification
hypotheses; the proper/open interchange comparison for the first vertex; and
exact closed direct-image comparison for the third vertex. The current blueprint
`prop-functor-package.proof.md`, clause (3), was read as well.

### Edge cases

* K=0 is included without a nonzero hypothesis; the zero triangle gives the
  expected vertex-existence assertion.
* U empty and Z=X are allowed; the first vertex is zero and the other two
  identify with K. Z empty and U=X likewise permit the third vertex zero.
* X empty is allowed: all category and scheme parameters remain meaningful;
  no point or nonempty-space assumption appears.
* Z may be nonreduced. The complement condition concerns images only and does
  not impose a reduced closed-complement scheme structure.
* X need not be separated over k₀. The theorem adds no absolute separatedness;
  only the open immersion's automatic separatedness is used by compactification.
* No uniform local rank, chosen amplitude interval, positive cohomological degree,
  or bounded-complex representative is imposed on K.
* The only characteristic exclusion is ℓ=char(k₀), exactly as requested.
* The explicit universe u is shared by the field and schemes, as in the recorded
  native framework. No site-object/morphism universe equality is added.

### Searches for an existing statement

All wrapper searches used Q97 and this item's id and are logged by `msearch.py`.

* LeanFinder query: `open closed localization distinguished triangle of Weil
  complexes extension by zero inverse image closed direct image`.
  Result: eight general triangulated-category results, including
  `DerivedCategory.triangleOfSESIso`; no specialized native Weil theorem.
* Loogle query:
  `AlgebraicGeometry.WeilComplex.exists_distTriang_openClosed`.
  Result: zero hits / unknown identifier (the service indexes Mathlib, not this
  project's existing upstream statement).
* Mathlib grep query `exists_distTriang_openClosed|WeilComplex|openClosed`,
  subdirectory `AlgebraicGeometry`: zero hits.
* LeanSearch query `open closed distinguished triangle Weil complexes compact
  support`: eight general SES and triangulated-subcategory results, including
  `DerivedCategory.triangleOfSES_distinguished`; no specialized Weil statement.
* `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` found the exact theorem in
  `WeilConjectures/WeilSheaf/LowerShriekFunctoriality.lean:171` and its upstream
  name-index entry. The separate etale and finite-coefficient localization
  declarations have different categories and do not replace this native theorem.
  No Sheaf module carries a duplicate of this exact theorem.
* Searching the exact item id in the project Lean sources found no existing
  item-specific implementation; the matching theorem is identified by its
  actual declaration name and signature above.

### Validation

A module-mode scratch probe imports
`WeilConjectures.WeilSheaf.LowerShriekFunctoriality`, sets `autoImplicit false`,
and checks `@AlgebraicGeometry.WeilComplex.exists_distTriang_openClosed` through
`scompile.py`. The probe is not a delivered module. The prescribed dry run and
final delivery also compile their generated existing-declaration check on the
server. No live source, artifact, or git state was edited directly.

## Second reading by Q97

No independent worker reading is claimed: the dispatcher brief requires direct
worker delivery and the maintainer performs the independent review.
