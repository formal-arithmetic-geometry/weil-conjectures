## Worker report

The module `Sheaf.Paper.FiniteCoefficientDirectImage` states
`lem-coef-finite-direct-image`, with the original statement unchanged. Its primary
declaration is
`AlgebraicGeometry.Etale.finiteCoefficientDirectImageMap_isIso`; the pro-etale
assertion is
`AlgebraicGeometry.ProEtale.finiteCoefficientDirectImageMap_etaleOrigin_isIso`.
The other recorded declarations specify the actual comparison morphisms and their
coherences. Every theorem is postponed with `sorry` and has its source and a full
proof plan in its docstring. Definitions contain real data. In particular the
comparison morphism is chosen from an existence-and-uniqueness theorem specifying
that morphism, not from an unconstrained existence assertion.

Hypotheses and objects:

| Node text | Lean rendering |
| --- | --- |
| Global finite-field datum, algebraic closure k in characteristic p | `D : WeilConjectures.FiniteFieldDatum.{u}`; the schemes are over `Spec (CommRingCat.of D.k)` |
| Prime l distinct from p | `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)` |
| Finite extension E/Q_l | `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]` |
| Integer n at least one | `(n : ℕ) (hn : 1 ≤ n)` |
| A = O_E/varpi^n, with its actual coefficient construction | `ULift.{u + 1} (Padic.coefficientExtensionRing l E n)`; this is the established etale coefficient universe convention, not a different ring |
| B commutative, finite as A-module | `(B : Type (u + 1)) [CommRing B] [Algebra A B] [Module.Finite A B]`, with ring map `algebraMap A B`; no flatness assumption |
| Finite-type k-schemes T and X | Bundled `T X : Over (Spec (CommRingCat.of D.k))`, with `LocallyOfFiniteType` and `QuasiCompact` on their structure morphisms |
| Separated finite-type map over k | `(f : T ⟶ X)` in `Over`, with `IsSeparated f.left`, `LocallyOfFiniteType f.left`, and `QuasiCompact f.left` |
| Etale A-complex K | `K : Etale.DerivedCategoryModule A T.left`, equivalently the unbounded derived category of sheaves valued in `ModuleCat A` |
| Bounded constructible K | The recorded `Etale.DerivedCategory.isBoundedConstructible A T.left K`, using the explicit finite-ring proof from `Padic.finite_coefficientExtensionRing`; this is not upstream's different constructibility predicate |
| Finite Tor interval a <= b against all degree-zero sheaves | `_hTor : ∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn A T.left a b K`, exactly the etale convention recorded with `lem-sf-flat-model` |
| Ordinary uncompleted coefficient extension K_B | `ProEtale.pbcFixedScalarExtension T.smallEtaleTopology φ`, the published left adjoint to actual exact derived restriction; the same functor is applied at X to Rf_* K |

Clauses and maps:

| Node clause | Lean rendering |
| --- | --- |
| Comparison is a B-linear morphism in D(X_et,B) | `Etale.finiteCoefficientDirectImageMap φ f K`; its codomain is `R(lowerStar (ModuleCat B) f)` of scalar extension of K |
| Canonical map is the extended A-counit's B-geometric transpose | `Etale.IsFiniteCoefficientDirectImageMap φ f K c` is the explicit scalar-unit/counit equation: pull back the scalar unit at Rf_A K, apply the recorded exact restriction/pullback comparison, then restrict the B-geometric transpose of c. This equals the A-counit followed by the input scalar unit. The scalar and geometric adjunction bijections identify this equation with extending the A-counit after the canonical scalar/pullback identification. `finiteCoefficientDirectImageMap_existsUnique` fixes the actual B-map by that equation. |
| Restriction is the projection mate followed by the canonical restriction/direct-image comparison | `Etale.finiteCoefficientDirectImageMap_restriction_projection` writes its scalar-unit form explicitly: `η_X ≫ Res(c) ≫ β = Rf_A(η_T)`. Here β is `finiteCoefficientRestrictionDirectImageMap`, constructed as the actual mate of the restriction/pullback isomorphism. The defining scalar-unit equation and this identity use exactly the counit normalization, rather than an arbitrary identification of the two endpoints. On K-flat tensor models η is x ↦ x tensor 1, and this is the projection formula's unit/counit mate identity under the canonical underlying-tensor comparisons; its docstring explains that equivalence. This avoids supposing that derived restriction is faithful on morphisms. |
| The etale comparison is an isomorphism | `Etale.finiteCoefficientDirectImageMap_isIso` with precisely the finite coefficient, geometric, constructibility and Tor assumptions above |
| Natural in K | `Etale.finiteCoefficientDirectImageMap_naturality`, an equality of B-linear morphisms using the actual functor maps |
| Geometric composition | `Etale.finiteCoefficientDirectImageMap_comp`, with the canonical `rightDerivedLowerStarComp` identifications inserted on both sides and `Rg_B.map (c_f)` in the displayed order |
| Finite coefficient chain A -> B -> C | `Etale.finiteCoefficientDirectImageMap_coefficientChain`; it uses ring homomorphisms φ and ψ, ψ.comp φ, and the published `pbcFixedScalarExtensionComp` on source and target. The intermediate construction has arbitrary commutative B, not another A_E,m. |
| Exact comparison pullback nu_T^* | `(ProEtale.comparisonUpperStar (ModuleCat A) T).mapDerivedCategory` |
| Pro-etale target is specifically nu_T^*(K_B) | The pro-etale isomorphism theorem postcomposes `c_pro` by `Rf_pro,B.map ((pbcComparisonReduction T φ).hom.app K)`, so its target is literally the B-direct image of the comparison pullback of K_B |
| Pro-etale map uses the analogous counit transpose | `ProEtale.IsFiniteCoefficientDirectImageMap`, `ProEtale.finiteCoefficientDirectImageMap_existsUnique` and `ProEtale.finiteCoefficientDirectImageMap`, now with the actual pro-etale inverse/direct image adjunction |
| Pro-etale isomorphism on the prescribed etale-origin inputs | `ProEtale.finiteCoefficientDirectImageMap_etaleOrigin_isIso`, with the same hypotheses and actual uncompleted direct images |
| Pro-etale naturality and both coherences | `ProEtale.finiteCoefficientDirectImageMap_naturality`, `_comp`, and `_coefficientChain`. The composition theorem uses the recorded `finiteDirectImageComposition`; the canonical scalar/comparison isomorphism identifies these formulas with those on nu_T^*(K_B). |

The construction and its formal naturality/coherence identities are stated for
arbitrary coefficient maps and inputs, since the node explicitly uses the same
counit construction over B and on Rf_A K. The two isomorphism assertions retain all
the node's hypotheses. No isomorphism for arbitrary unbounded or non-etale-origin
pro-etale inputs is asserted.

Dependency interfaces read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the existing
  `Padic.coefficientExtensionRing` construction.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`,
  through the fixed-ring coefficient presentations and scalar-extension interfaces.
- The morphism-property convention uses Mathlib `LocallyOfFiniteType`,
  `QuasiCompact`, `IsSeparated`, and `CategoryTheory.Over`.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible`.
- `Sheaf.Paper.FiniteCoefficientFlatModel` and the public derived-category
  imports: `Etale.DerivedCategory.hasTorAmplitudeIn` and the finite-Tor bounded
  flat constructible model interface in the proof plans.
- `Sheaf.Algebra.Homology.DerivedTensor`: `Scheme.derivedTensor` is the intrinsic
  K-flat model of the ordinary pro-etale tensor. Fixed-scalar realizations use the
  published canonical equivalence and adjunction, not a second tensor definition.
- Mathlib `SheafOfModules.restrictScalars` and the existing fixed-ring
  `Sheaf.derivedRestrictScalars` presentation.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.lowerStar`;
  its unbounded right derived functor and `derivedUpperStarLowerStarAdjunction`
  are the already supplied derived interfaces. The bounded inputs agree with
  the recorded bounded-below direct image.
- `Sheaf.Paper.FiniteDirectImageComposition`:
  `ProEtale.finiteDirectImageComposition`; etale composition uses the existing
  `Etale.rightDerivedLowerStarComp` in the reversed orientation.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparisonModules` and the existing
  `ProEtale.comparisonUpperStar` adjunction.
- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`:
  `ProEtale.siteComparisonDerivedPullbackPlus`, reexporting the exact unbounded
  comparison interface used here as `comparisonUpperStar.mapDerivedCategory`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations`:
  the published finite fixed/intrinsic identifications and the actual pro-etale
  operations. No completed scalar-extension functor is used in the statements.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`:
  `Etale.derivedTensor`; the scalar functor is its coefficient-category realization.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`:
  `Etale.rightDerivedLowerStarProjectionMap` and its normalized counit formula.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`:
  `SheafOfModules.derivedChangeOfRingsIndependentCoefficients`, the K-flat
  universal scalar-extension construction underlying the published adjoint.
- `Sheaf.Paper.PbcActualScalarPullback` reexports
  `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`, the general
  representative-normalized scalar/pullback identification used in the proof.
- `Sheaf.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons`:
  `Etale.upperStarRestrictScalarsIsoSheaf` and the canonical bounded-below
  `derivedLowerStarRestrictScalarsMap`/iso. Its exact unbounded inverse-image
  square is obtained with `Functor.mapDerivedCategorySquareIso` and
  `Etale.leftDerivedUpperStarIsoMapDerivedCategory`, without changing universes.
- `WeilConjectures.SixFunctors.ProEtale.Derived.RestrictScalars`:
  `ProEtale.leftDerivedUpperStarRestrictScalarsIso`.
- Already landed `Sheaf.Paper.WitnessCompatibility`:
  `ProEtale.pbcRestriction_isRightAdjoint`, `pbcFixedScalarExtension`,
  `pbcFixedScalarExtensionComp`, and `pbcComparisonReduction`. Its owning node
  `def-weil-pbc-witness-compatibility` is added to stmt_deps under the rule
  allowing already landed dependencies. This reuses the canonical scalar
  adjoint and coherence rather than defining another one. Its node and the
  full signatures/docstrings were read. No other DAG node is stated or edited.

Every stated proof dependency's recorded module is also imported, privately
unless already needed publicly for the statement. The theorem docstrings follow
the node's four proof steps: finite-ring and uniform cohomological bounds;
finite-constant projection and restriction/counit compatibility; adjunction
pasting for both coherences; and exact etale/pro-etale comparison with the
canonical direct-image counit normalization.

Edge cases checked before writing:

- The empty source is permitted; the proof takes d=0 there and all sheaves vanish.
  No nonempty or dimension-positivity hypothesis is added.
- K=0, identity geometric morphisms, identity coefficient maps and zero B are
  included. `CommRing B` does not impose `Nontrivial B`.
- n=0 is excluded exactly by the source's hn. n=1 is included.
- l=p is excluded exactly once by _hl; no extra field or torsion assumption is
  imposed on B. Nonflat finite algebras and further finite coefficient chains
  are included.
- The Tor interval permits a=b. Bounded constructibility uses the recorded finite
  coefficient predicate, not the upstream predicate with finitely generated stalks.
- The small pro-etale site retains object universe u+1 and morphism universe u.
  The explicit named etale size instance proves essential smallness at u+1 from
  existing size facts; it adds no hypothesis or equality of universes.
- Coherence is an equality of B- or C-linear derived morphisms, not merely an
  equality after forgetting coefficients, so no faithfulness assumption is used.

Searches for an existing exact statement:

- `msearch.py ... leanfinder`, query “finite change of coefficients commutes with
  ordinary derived direct image of constructible etale sheaves”: eight unrelated
  scheme/ring results; no exact statement.
- `msearch.py ... loogle`, query `"projection", "tensor"`: zero results.
- `msearch.py ... grep`, query
  `coefficient.*[Dd]irect|[Dd]irect.*coefficient` in Mathlib AlgebraicGeometry:
  zero results.
- `msearch.py ... leansearch`, query “Finite derived coefficient change commutes
  with ordinary direct image for constructible etale complexes”: eight results,
  comprising exact-functor factorization/shift instances, etale Kaehler
  differential base change and stability of etale/finite morphisms; none is this
  ordinary direct-image statement.
- `rg` in the upstream WeilConjectures source for coefficient/direct image,
  derived restriction, scalar extension, tensor and projection declarations, and
  the item's id: no exact lemma. Upstream proper direct-image projection and
  compact-support formulas require different geometric hypotheses or functors.
- `rg` in project `lean/Sheaf` for the same patterns found the existing
  finite-constant projection theorem, canonical restriction comparisons,
  `CompactSupportCoefficientChange.directImageCoefficientComparison` on finite
  coefficient tensor presentations, and the fixed scalar functor/coherences in
  `WitnessCompatibility`. Their signatures and docstrings were read. The
  compact-support module does not state the present finite-type ordinary
  direct-image theorem or the etale-origin pro-etale assertion; its map is a
  finite-coefficient presentation specialization of the same counit construction.

No statement fault or disputed statement was found. There are no new definition
nodes and no dependency-node replacements. The item's mathematical statement,
proof and proof_deps are unchanged.

Validation: the full module compiled cleanly through `scompile.py` in both its
sandbox and library names after repairing an explicitly diagnosed etale
essential-smallness instance and making the exact-square import explicit.
The final delivery dry run is performed after this report and the node record
are written; its result is reported by the worker's final status line.


## Second reading by Q61

I read the item JSON and the complete delivered module independently, together with
its blueprint source at order 2130, its unit's setting, all statement-dependency
records and the declarations used from their modules. There is no statement_change,
new definition node, or replacement dependency module. The mathematical statement
agrees with the source and needs no correction.

The following is my initial list of objects, hypotheses and conclusions, matched
against the final Lean. `S_W` below denotes the published
`ProEtale.pbcFixedScalarExtension` on W's indicated site; it is explanatory shorthand,
not file-local Lean notation.

| Object, hypothesis, or clause | Actual Lean and second-reader verdict |
| --- | --- |
| Global datum, k an algebraic closure of the finite field of characteristic p | `D : WeilConjectures.FiniteFieldDatum.{u}`. I opened `FiniteFieldFiber`: the tuple has p prime, a positive, q = p^a, finite k₀ of cardinality q, and `[IsAlgClosure D.k₀ D.k]`. Pass. |
| Prime l different from p | `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`. Pass; no extra characteristic hypothesis. |
| Finite field extension E/Q_l | `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. Pass; no norm or topology is independently chosen. |
| Positive level and the actual coefficient ring | `(n : ℕ) (hn : 1 ≤ n)` and `ULift.{u + 1} (Padic.coefficientExtensionRing l E n)`. I read the coefficient definitions and finiteness theorem: this is the quotient of the recorded valuation ring by the recorded uniformizer power, lifted only for the module-size convention. Pass. |
| Commutative finite A-algebra B and its structural map | `(B : Type (u + 1)) [CommRing B] [Algebra A B] [Module.Finite A B]` and `algebraMap A B`. Pass; neither flatness, locality, nontriviality, nor another quotient-ring presentation is imposed. |
| Finite-type k-schemes T and X | `T X : Over (Spec (CommRingCat.of D.k))`, each structure map having `LocallyOfFiniteType` and `QuasiCompact`. These are precisely finite type; the bundled arrows also enforce being over k. Pass. |
| Separated finite-type map f | `f : T ⟶ X` and `[IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]`. Pass; no properness or separatedness of the structure maps is added. |
| Bounded constructible etale A-complex K | `K : Etale.DerivedCategoryModule A T.left` and `_hK : @Etale.DerivedCategory.isBoundedConstructible ...`. I opened `BoundedConstructibleComplexes` and `DerivedCategories`: this uses all constructible cohomology sheaves and an actual bounded vanishing interval in the recorded module-valued derived category. The explicit finite-ring proof is a theorem, not an added hypothesis. Pass. |
| Finite Tor amplitude tested on all degree-zero sheaves | `_hTor : ∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn A T.left a b K`. The actual definition in `Etale.Derived.Coefficients` quantifies over every module sheaf F and every degree outside [a,b], using `singleFunctor _ 0`. Pass. |
| Ordinary uncompleted K_B and scalar extension of Rf_A K | `S_T.obj K` and `S_X.obj ((R(lowerStar (ModuleCat A) f)).obj K)`. I opened `WitnessCompatibility`, `DerivedBaseChange`, and the independent-coefficient change-of-rings interface. `S_W` is the left adjoint to actual exact derived restriction, uniquely representing derived extension of scalars. It does not complete the tensor product. Pass. |
| Specified B-linear coefficient projection | `Etale.IsFiniteCoefficientDirectImageMap`, its `existsUnique` theorem and the chosen `Etale.finiteCoefficientDirectImageMap`. The defining equation uses the pulled-back scalar unit, canonical restriction/pullback square and the B geometric counit, with right side the A counit followed by the input scalar unit. By the scalar and geometric Hom bijections this is exactly extending the A counit after canonical pullback/scalar extension. Pass; it does not choose an arbitrary map with the required endpoints. |
| Restriction is the actual projection mate with the canonical direct-image comparison | `Etale.finiteCoefficientDirectImageMap_restriction_projection` states `η_X ≫ Res(c) ≫ β = Rf_A(η_T)` with β defined by `mateEquiv` from the exact pullback/restriction square. I also opened `rightDerivedLowerStarProjectionMap`, whose transpose is tensor comparison followed by ε tensor 1, and the recorded bounded-below restriction comparison. On the canonical K-flat tensor realization η is x ↦ x tensor 1; the displayed equality is precisely its scalar-adjunction normalization. Together with the B-transpose specification it fixes the projection mate, without claiming derived restriction is faithful. Pass. |
| Etale isomorphism in D(X_et,B) | `Etale.finiteCoefficientDirectImageMap_isIso` asserts `IsIso` of that very B-linear map, with all preceding hypotheses. Pass. |
| Naturality in K | `Etale.finiteCoefficientDirectImageMap_naturality` compares the actual scalar-extension map of Rf(h) followed by c with c followed by Rf of scalar-extension(h). Pass; equality is in D(B). |
| Geometric composition | `Etale.finiteCoefficientDirectImageMap_comp` inserts the source A `rightDerivedLowerStarComp.symm.hom`, then c_g, then Rg_B(c_f), then the inverse B compositor. `ProEtale.finiteCoefficientDirectImageMap_comp` uses the recorded `finiteDirectImageComposition` in the corresponding orientation. Pass. |
| Finite coefficient chains A → B → C | Both `finiteCoefficientDirectImageMap_coefficientChain` theorems use φ, ψ, ψ.comp φ, the inverse scalar compositor at X, extension of c_AB, c_BC, and direct image of the source scalar compositor. Pass: the formulas specialize to every finite chain; the construction and its formal identities do not require the intermediate B itself to be A_E,m. |
| Exact comparison pullback and specified etale-origin pro-etale objects | The input is `(comparisonUpperStar (ModuleCat A) T.left).mapDerivedCategory.obj K`. In `ProEtale.finiteCoefficientDirectImageMap_etaleOrigin_isIso`, the map is the renamed `finiteCoefficientChangeDirectImageMap` followed by `Rf_pro,B.map ((pbcComparisonReduction T.left φ).hom.app K)`. The target is therefore literally Rf_pro,B of ν_T^*(K_B), as required. I read the mate definition and invertibility normalization of `pbcComparisonReduction`; it is not an arbitrary scalar comparison. Pass. |
| Pro-etale canonical transpose and isomorphism | `ProEtale.IsFiniteCoefficientDirectImageMap` and its uniqueness theorem use the actual published `leftDerivedUpperStarRestrictScalarsIso` and `derivedUpperStarLowerStarAdjunction`. The etale-origin isomorphism theorem has the same D, l, E, n, B, T, X, f, constructibility and Tor binders as the etale theorem. Pass. |
| Pro-etale naturality and coherences | The three pro-etale `finiteCoefficientDirectImageMap_*` identities concern the renamed B-linear map, with the same scalar and geometric compositors. Naturality of the actual comparison-reduction isomorphism transports these to the displayed ν_T^*(K_B) targets. Pass. |

The source checks include `sites-cohomology.tex`: 06YY (derived change of rings),
07A4 (canonical tensor/pullback isomorphism), 0G7E (pullback of flat-term K-flat
resolutions), 07A6 (unbounded derived adjunction), and 0D6J/03FD (the canonical
module/abelian cohomology comparisons). They impose no hidden properness, flatness
of B, or Noetherian hypothesis on the abstract map construction. Noetherianity
needed for constructible flat models follows here from finite type over the field.
I read the exact pro-etale declarations in the group's 51-module framework and
`coord/pefw-upstream-framework.md`, rather than substituting the older checkout.

Edge cases: the empty T and X, K = 0, the zero B-algebra, identity geometric and
coefficient maps, nonflat finite B, a = b, and positive level n = 1 are all admitted.
There is no index type or nonempty-index assumption. n = 0 and l = p are excluded
exactly as in the node. No extra `IsNoetherian`, `Nontrivial`, `IsProper`, topology,
or smallness hypothesis was introduced. Universe u is bound; site object and Hom
universes remain u+1 and u, with ModuleCat at u+1. `finiteCoefficientSiteSize` derives
the etale essential-smallness witness instead of assuming an equality of universes.
The lifted finite coefficient ring and arbitrary finite B use the established
etale size convention and do not drop a finite-ring case.

Independent searches:

- LeanFinder: “derived pushforward commutes with finite scalar base change for
  constructible torsion sheaves”; eight underived pushforward/section results,
  including `SheafOfModules.pushforwardComp`, none this theorem.
- Loogle: `"restrictScalars", "lowerStar"`; no results.
- Mathlib grep through msearch: `scalar.*[Pp]ushforward|[Pp]ushforward.*scalar`;
  three underived/action hits, no derived coefficient comparison.
- Direct rg in Mathlib, upstream WeilConjectures and project Sheaf for scalar
  extension, pushforward, coefficient comparison, projection maps and every
  newly introduced declaration name. The upstream ordinary projection map is
  the recorded A-linear map, not this B-linear isomorphism theorem.
- Opened `CompactSupportCoefficientChange.directImageCoefficientComparison` and
  its `CoefficientTensorModel` and counit theorem. That finite-coefficient
  presentation interface does not give the unrestricted scalar functor map or
  etale theorem here; its finite specialization is the same canonical construction.
- Found `ProEtaleConstantRingMap.finiteCoefficientDirectImageMap`: its full name
  is `AlgebraicGeometry.ProEtale.finiteCoefficientDirectImageMap`, but it is a
  ring-sheaf structure map, not derived coefficient change. I confirmed its
  current server source through `scompile.py --source`.

Mismatches repaired:

1. H9: the proposed pro-etale derived map reused the full name of that existing
   ring-sheaf map. Renamed only the new derived definition to
   `AlgebraicGeometry.ProEtale.finiteCoefficientChangeDirectImageMap`, updated
   every pro-etale statement using it and the node's `lean.declarations`.
   The theorem names are retained. The initial Worker report's old map name
   should be read with this correction.
2. H4: the proposed pro-etale `finiteCoefficientRestrictionPullback` was only a
   wrapper for the already published `leftDerivedUpperStarRestrictScalarsIso`.
   Removed the wrapper, used the published declaration directly, and removed
   the duplicate from `lean.declarations`.
3. Rewrapped the single long line caused by the longer map name. No hypotheses,
   conclusions, source statement, proof plan, or dependency record were changed.

All definitions have actual data; each chosen comparison is determined uniquely
by its displayed universal equation. Every theorem body remains `by sorry`.
Docstrings give the source, blueprint tag and the appropriate node proof steps.
The primary `lean.statement` was checked verbatim against the final signature;
all variables and the one universe are explicitly bound.

Second-reader validation: `scompile.py Q61 lem-coef-finite-direct-image` on the
final module passed locally in both sandbox and library names (13.0 s and 14.4 s),
with no errors or warnings. The first local attempt encountered an overlay timeout;
the wrapper's server confirmation passed, and the subsequent final local run also
passed. All final declaration names are present exactly once in the node record,
no delivered Lean line exceeds 100 characters, and no theorem was proved.
