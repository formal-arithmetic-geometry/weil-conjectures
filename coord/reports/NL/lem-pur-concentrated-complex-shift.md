## Worker report

The module `Sheaf.Paper.ConcentratedComplexShift` states
`AlgebraicGeometry.Scheme.concentratedComplexShift`. It uses the existing finite-Tor
predicate `WeilConjectures.finiteTorConstructible` for the finite coefficient ring
`P.Ring = A_{E,n}` supplied by `PurityFiniteSetting`, the existing pro-etale derived
category and cohomology functor, and the existing pro-etale locally constant module
predicate. All theorem proofs are `sorry`; the helper definition contains no postponed
data.

The helper theorem `proEtaleCoefficientInverseImageMap_isIso` records the canonical
constant-coefficient inverse-image map as invertible, and the definition
`proEtaleConstantDerivedPullback` is the derived functor of the specified module
inverse-image construction with that canonical coefficient comparison. Its inverse is
therefore the `asIso` of the canonical map, rather than an arbitrary chosen map.

The geometric hypotheses are rendered as `P : PurityFiniteSetting.{u}`, a scheme
`T : Scheme.{u}`, and `a : T ⟶ Spec (CommRingCat.of P.field.k)` with
`[IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]`; these are exactly a
separated finite-type scheme over the fixed field. The complex is
`K : proEtaleDerivedCategory T P.Ring`, and
`hK : WeilConjectures.finiteTorConstructible P.coefficients.l P.extension P.level
P.level_pos T K` is the stated `D^b_ctf(T, Λ)` condition in the finite-level purity
conventions. The integer is `r : ℤ`.

The first clause takes
`hconcentrated : ∀ i : ℤ, i ≠ r → IsZero ((DerivedCategory.homologyFunctor
(proEtaleRingModules T (proEtaleConstantRing T P.Ring)) i).obj K)` and concludes
`Nonempty (K ≅ H^r(K)[-r])`, with `H^r(K)` rendered by the same homology functor and
placed in degree zero by `DerivedCategory.singleFunctor` before shifting by `-r`.
`Nonempty` records the canonical truncation isomorphism without introducing a
noncanonical map.

The second clause quantifies `U : Scheme.{u}` and `u : U ⟶ T` with
`[Surjective u] [Etale u]`, then a module sheaf
`L : proEtaleRingModules U (proEtaleConstantRing U P.Ring)`. Its hypothesis is
`Nonempty ((proEtaleConstantDerivedPullback P u).obj K ≅ L[-r])`, with the shift
again represented as a degree-zero `singleFunctor` object followed by `⟦-r⟧`.
The assumptions that `L` is locally constant and has finite geometric stalks are
rendered by `IsLocallyConstantProEtaleModuleSheaf U P.Ring L` and
`∀ Ω y, Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing U P.Ring) L)`.
The conclusion gives vanishing of every `H^i(K)` for `i ≠ r`, local constancy of
`H^r(K)` via `IsLocallyConstantProEtaleModuleSheaf T P.Ring`, and finiteness of every
geometric stalk of `H^r(K)`. No uniform stalk-size bound is added.

Dependency declarations used:

- `Sheaf.Paper.PurityFiniteSetting`, declaration `WeilConjectures.PurityFiniteSetting`
and its fields `Ring`, `Coefficient`, `field`, `coefficients`, `extension`, `level`,
and `level_pos`.
- `Sheaf.Paper.FiniteTorAmplitude`, declaration
`WeilConjectures.finiteTorConstructible`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`, declaration
`AlgebraicGeometry.Scheme.proEtaleDerivedCategory`.
- `Sheaf.AlgebraicGeometry.ProEtaleOperations`, declarations
`proEtaleRingModules`, `proEtaleRingDerivedPullback`, and
`proEtaleConstantRing`.
- `Sheaf.Paper.ProEtaleFixedModuleLocalConstancy`, declaration
`AlgebraicGeometry.Scheme.IsLocallyConstantProEtaleModuleSheaf`.
- `Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk`, declaration
`AlgebraicGeometry.Scheme.proEtaleGeometricModuleStalk`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`, declarations
`DerivedCategory.homologyFunctor` and `DerivedCategory.singleFunctor`.

Edge cases checked before writing: `r` may be any integer, including negative and zero;
the empty scheme makes the stalk clauses vacuous; `L` may be zero; the cover is a
single surjective etale morphism and is not assumed finite or quasi-compact; stalk
finiteness is pointwise with no common cardinality; `P.level_pos` permits level one;
and the conclusion keeps every degree outside `r` rather than only a finite range.

Searches for an existing declaration:

- `msearch.py leanfinder NL lem-pur-concentrated-complex-shift "derived category object
cohomology concentrated in one degree canonical shifted cohomology sheaf"`: eight hits,
including `DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE`; it supplies an
existential t-structure result but no cohomology-sheaf statement with the etale-cover
clause.
- `msearch.py loogle NL lem-pur-concentrated-complex-shift
"DerivedCategory.homologyFunctor singleFunctor shift isomorphism"`: zero hits
(`singleFunctor` is unknown to Loogle).
- `msearch.py grep NL lem-pur-concentrated-complex-shift
"concentrated.*cohomology|singleFunctor.*homology|locally constant.*finite"
Mathlib/Algebra/Homology Mathlib/AlgebraicGeometry`: no combined match.
- `rg` over `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and this project's
`lean/Sheaf` found only generic truncation infrastructure and pro-etale constructibility;
no declaration for this item. The exact item id was absent.

No new definition node or dependency module was needed. The finite-Tor dependency was
already landed in `newtargets-dag` and was added to `stmt_deps`; its declaration is used
verbatim. No statement correction or `STATEMENT-DISPUTED:` applies.


## Second reading by NL

I read the unchanged node against its actual source,
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-thm-dnc/lem-pur-concentrated-complex-shift.md`,
including both proof steps, and the fixed-setting source
`sk-def-purity-conv/def-pur-conventions.md`. This is a blueprint source, not a
Stacks statement with additional standing hypotheses. The conventions explicitly make
the finite-level assertion first; integral and field versions are separate coefficient
transports. No node statement correction is needed. The following list records the
objects, assumptions, and conclusions independently of the worker's report.

1. Fixed global finite-field and coefficient data: `P : PurityFiniteSetting.{u}`.
   I opened `PurityFiniteSetting` and `FiniteFieldDatum.CoefficientDatum`: their fields
   give the prime p, positive exponent, q, finite base and its algebraic closure k,
   the prime ell different from p, its chosen algebraic closure, the finite
   intermediate coefficient extension, and the positive level. `P.Ring` unfolds to
   `Padic.coefficientExtensionRing P.coefficients.l P.extension P.level`, the actual
   quotient of the integer ring by the uniformizer power. Verdict: exact finite-level
   setting, with no arbitrary coefficient ring substituted.
2. A separated finite-type k-scheme T: `T : Scheme.{u}` and
   `a : T ⟶ Spec (CommRingCat.of P.field.k)` with `[IsSeparated a]`,
   `[LocallyOfFiniteType a]`, and `[QuasiCompact a]`. The latter two together are
   finite type, as the existing finite-field source also records. Verdict: exact;
   the explicit named structure morphism is an accepted project convention.
3. An object K of D^b_ctf: `K : proEtaleDerivedCategory T P.Ring` and
   `hK : WeilConjectures.finiteTorConstructible P.coefficients.l P.extension
   P.level P.level_pos T K`. I opened `FiniteTorAmplitude`: this predicate is the
   intersection of `intrinsicFiniteTorsionConstructible` and
   `HasFiniteProEtaleTorAmplitude`. I also opened the former: its boundedness is
   finiteness of the nonzero cohomology degrees and its constructibility condition
   applies to every cohomology sheaf in the same constant-ring module category.
   Verdict: uses the landed node, without dropping finite Tor amplitude.
4. An arbitrary degree: `r : ℤ`. Verdict: exact, with no positivity assumption.
5. Clause (1) hypothesis: the first conjunct begins
   `(∀ i : ℤ, i ≠ r → IsZero ((DerivedCategory.homologyFunctor ... i).obj K)) → ...`.
   I opened the cohomology dependency's Mathlib declaration: `homologyFunctor C i`
   factors the cochain representative's homology functor via localization, exactly
   the node's kernel/image cohomology sheaf. Verdict: every degree other than r.
6. Clause (1) conclusion: `∃! e : K ≅ ((DerivedCategory.singleFunctor ... 0).obj
   ((DerivedCategory.homologyFunctor ... r).obj K))⟦-r⟧, ...`.
   The equation sends `e.hom` through the canonical `singleFunctors.shiftIso
   (-r) r 0 (neg_add_cancel r)` and then applies `homologyFunctor ... r`; it equals
   the inverse component of `singleFunctorCompHomologyFunctorIso ... r`.
   I opened Mathlib `FullyFaithful.lean` and the `SingleFunctors.shiftIso`
   signature. The former comparison is H^r(single_r M) ≅ M; the latter is
   single_0(M)[-r] ≅ single_r(M). Thus this equation says exactly that e induces
   the identity of H^r(K). For a concentrated object H^r is fully faithful, so this
   normalizes the isomorphism uniquely. The canonical truncation zigzag has this
   normalization (the degree-r cycles-to-cohomology quotient), so this is the
   node's canonical truncation isomorphism, without an arbitrary isomorphism choice.
   Verdict: exact canonicity, repaired from the worker's bare `Nonempty`.
7. Clause (2) cover: the second conjunct separately quantifies
   `∀ (U : Scheme.{u}) (u : U ⟶ T) [Surjective u] [Etale u], ...`.
   Verdict: any surjective etale morphism, with no quasi-compactness, finiteness,
   connectedness, or finite-type condition on U added. This conjunct now has no
   concentration hypothesis; that hypothesis belongs only to clause (1).
8. Clause (2) sheaf and pullback hypothesis: `L : proEtaleRingModules U
   (proEtaleConstantRing U P.Ring)` and
   `Nonempty ((proEtaleConstantDerivedPullback P u).obj K ≅
   ((DerivedCategory.singleFunctor ... 0).obj L)⟦-r⟧)`.
   I opened `ProEtaleInverseImage` and `ProEtaleOperations`: the coefficient map is
   the adjoint of the specified constant-section direct-image map, the module
   pullback is inverse image followed by actual sheafified tensor extension along
   that map, and its derived functor is exact termwise descent. The helper now uses
   `ProEtale.finiteCoefficientCommRingMap_isIso` from `ProEtaleConstantExact` with
   `ULift P.Ring`, after installing finiteness from the recorded
   `Padic.finite_coefficientExtensionRing` and the discrete topology. `asIso` is
   applied to the actual canonical map. Verdict: the specified uncompleted Lu*,
   with no arbitrary comparison or extra hypothesis.
9. Clause (2) properties of L: `IsLocallyConstantProEtaleModuleSheaf U P.Ring L`
   and `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ U),
   Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing U P.Ring) L)`.
   I opened the current recorded `ProEtaleFixedModuleLocalConstancy` module and
   its public import `ProEtaleLocallyConstantSheaf`. The recorded interface keeps
   the original ringed-site predicate as well as adding the fixed-scalar encoding.
   Our category needs the original predicate: it is coverwise isomorphism on
   localized sites to actual constant module sheafifications, with arbitrary
   models varying over the cover. I opened the stalk construction too: it is the
   colimit over pointed weakly etale neighbourhoods, with its colimit scalar
   action. Verdict: locally constant module sheaf and pointwise finite geometric
   stalks, without freeness, finite presentation, or a uniform cardinal bound.
10. Clause (2) conclusions: the conjunction is vanishing of the same
    `homologyFunctor ... i` for all `i ≠ r`, the same
    `IsLocallyConstantProEtaleModuleSheaf` applied to `homologyFunctor ... r`, and
    finiteness of its `proEtaleGeometricModuleStalk` at every geometric point of T.
    Verdict: all three clauses are present and follow from the cover assumptions
    alone; the first conclusion is no longer assumed at the outset.

Edge cases: every integer r is allowed, including zero and negative degrees; the
shift is -r, so the degree-zero sheaf sits in cohomological degree r. Zero K and
zero L are allowed. When T is empty the geometric-stalk assertions are vacuous;
there is no nonemptiness instance, and U may be empty in that case. The independent
descent assertion has no finite or quasi-compact cover hypothesis. There is no
nonempty-index assumption on local trivializing covers, so the empty scheme is
not excluded. Level zero is excluded exactly by the source's n >= 1; level one
is included. The coefficient prime differs from p by the fixed data, and no new
characteristic hypothesis is imposed. All schemes have the arbitrary fixed
universe u, the small site keeps objects in u+1 and morphisms in u, coefficients
are the standard ULift from u to u+1, and modules are in u+1. The geometric-point
binders use the same Type u convention as the recorded geometric-stalk interface;
no equality of the site's two universes or extra smallness instance is imposed.

Independent duplicate searches:

- `msearch.py NL lem-pur-concentrated-complex-shift leanfinder
  "canonical isomorphism between an object with only one nonzero homology and the
  single complex on its homology"`: eight hits, including
  `HomologicalComplex.singleObjHomologySelfIso` and
  `HomologicalComplex.homologyFunctorSingleIso`. These compare the homology of a
  single complex, not both assertions here.
- The independent Loogle query `CochainComplex.homologyπ` returned zero hits with
  an unknown-identifier diagnostic. LeanSearch for "derived sheaf cohomology
  concentrated in degree r unique isomorphism identity on homology" was unavailable
  (Internal Server Error); this is recorded as unavailable, not as evidence of absence.
- The launcher grep query `singleFunctorCompHomologyFunctorIso|finiteCoefficientCommRingMap_isIso`
  returned no hits. Direct `rg` searches with `single.*homology`, `homology.*single`,
  `concentrated`, `proEtaleConstant.*Iso`, and `CoefficientInverseImageMap` across
  Mathlib homological algebra, upstream `WeilConjectures/CategoryTheory`, and
  `lean/Sheaf` did locate the canonical Mathlib comparisons and, critically, the
  published `ProEtale.finiteCoefficientCommRingMap_isIso`. I opened its signature
  and proof docstring. This exactly supplies the worker's new invertibility theorem,
  so I removed that duplicate. Exact new declaration names were also searched in
  the upstream name index and both source trees; no remaining collision was found.
  The t-structure existential result found by the worker was opened too: it chooses
  an unspecified Y and supplies no independent cover-descent assertion, so it does
  not replace the combined node.

Mismatches and changes:

- H3: `hconcentrated` was an outer binder governing both clauses. Moved it inside
  the first conjunct as an implication, so clause (2) derives concentration.
- H3: `Nonempty (K ≅ H^r(K)[-r])` did not express the stated canonicity. Replaced
  it by the uniquely normalized isomorphism above, with the exact same target.
- H4/H5: the worker's `proEtaleCoefficientInverseImageMap_isIso` repeated the
  existing finite commutative coefficient theorem and introduced an unnecessary
  extra sorry not tracked by a separate DAG statement. Removed it and reused the
  published theorem and the published coefficient-ring finiteness theorem inside
  the real pullback definition. Only the main node's theorem remains postponed.
- H8: expanded the main theorem's docstring into all six DAG proof steps, including
  the localization indexing argument and both directions of the stalk comparison;
  added the helper's explicit source place.
- Proof-plan imports: added the stated truncation triangle, covering conservativity,
  weakly etale localization, and covering-axiom modules, together with the etale
  point lifting source. Their declarations are proof dependencies, not extra
  hypotheses or duplicate notions.
- Updated `lean.declarations` after removing the duplicate and regenerated
  `lean.statement` verbatim from the repaired theorem signature. The mathematical
  node statement, proof, and source are unchanged. The original worker report is
  retained above; its canonicity and helper-theorem descriptions are superseded
  by this second reading.

There are no new definition nodes. A subsequent compile exposed the dependency-module
compatibility repair described below. The helper is a specialization of the already constructed canonical pullback, listed under this
node as allowed for the notion being stated. All new data is explicit; all remaining
theorem proofs are `sorry`. Compilation and the dry-run delivery preflight are
checked using the prescribed wrappers before pushing.


## Dependency modules

`lem-cbc-proetale-stalk-conservative`: both the local compiler and the current server
compiler rejected the combined imports, reporting that the legacy
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs` duplicates declarations
already imported from `FiniteCoefficient.UpperLowerStar.Defs`. The canonical
inverse-image dependency uses the latter, whereas the recorded conservativity module
imported the former through old localization and comparison modules. This is an
unusable recorded dependency interface under §1(B), not a missing mathematical
hypothesis. I deliver the same `ProEtaleStalkConservative.lean` with its entire body,
all helper definitions, signatures, and proof docstrings verbatim. Only the imports
change: localization comes from the matching published
`FiniteCoefficient.LowerShriek.Open.Defs`, and the comparison proof import is the
recorded `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived` rather than old
upstream comparison modules. The unused legacy lower-shriek conservativity import
is removed. The module's original restriction/locality proof does not use it.
The dependency node changes only in `lean`, with an explanatory note.

I independently read the dependency node's current four-part statement and seven
proof steps, its blueprint source, and Stacks `proetale.tex` at `section-points`
(Tag 0991), `lemma-classical-point` (0993),
`lemma-describe-pullback-from-etale` (0GLZ), and
`example-functions-mod-locally-constant-functions` (0F6D). The current node already
clarifies the blueprint's derived meaning and confines geometric-stalk detection
to etale-origin complexes; this delivery does not change that mathematical record.
The dependency audit is:

- Objects and hypotheses: `T : Scheme.{u}`, `Λ : Type (u+1)` with `[Ring Λ]`,
  `[Finite Λ]`, and discrete topology; no commutativity, Noetherian assumption on T,
  or finite-type condition. These are precisely the finite discrete left coefficient
  modules specified by `FiniteCoefficientModules`, whose canonical realization and
  cohomology functor are publicly imported from the recorded definition module.
- Clause (1): `finiteCoefficient_cover_detection` quantifies one actual pro-etale
  cover with arbitrary index universe, all derived maps, all cochain complexes, and
  all module sheaves. Its three conjuncts give invertibility after every slice
  restriction, acyclicity iff all cohomology vanishes, and the sheaf-zero criterion.
  `finiteCoefficientSliceRestriction_exact` supplies exactness of the real slice
  functor; the derived instance is `HasDerivedCategory.standard`. Empty covers and
  the empty scheme are included. Verdict: exact, unchanged.
- Clause (2): `finiteCoefficient_affine_basis_detection` uses the recorded
  `T.AffineProEt` inclusion and tests the sections of each cohomology map.
  `finiteCoefficient_affine_open_basis_detection` quantifies an arbitrary jointly
  surjective affine open cover and tests the composite basis objects. It never
  evaluates an arbitrary complex and claims exactness of that evaluation. The
  zero-sheaf criterion is `Subsingleton` on section modules. Verdict: all cases
  and quantifiers match, unchanged.
- Clause (3): `finiteCoefficientCohomologyStalk` composes actual cohomology with
  the underlying additive presheaf and the pointed-neighbourhood colimit.
  `finiteCoefficient_etale_origin_stalk_detection` has one conjunct for images
  of bounded-below etale maps under `finiteCoefficientDerivedComparison`, and
  one for arbitrary maps between the specified bounded constructible objects.
  It tests every degree and every geometric point. The former comparison is the
  recorded exact coefficient realization; the latter objects are defined as
  etale-origin objects, so there is no blanket geometric-stalk detection assertion.
  Verdict: exact, unchanged, including arbitrary maps in the essential image.
- Clause (4): `proEtaleAllFunctionsPresheaf` uses actual functions on point sets;
  `proEtaleConstantsToAllFunctions` is the constant-function map, and
  `proEtaleFunctionsQuotient` is its sheafified cokernel. The counterexample theorem
  gives the affine quotient by locally constant functions, zero sections over
  Spec k, zero geometric stalks for every algebraically closed extension field,
  and nonvanishing of the sheaf, for any nontrivial abelian group A. These are
  exactly the Stacks example and the node, with real constructed data and no
  missing infinitude condition. Verdict: exact, unchanged.
- The two abelian-sheaf criteria retain the same source-based covering and basis
  consequences. The replacement localization restriction has the same sectionwise
  construction and signature in the finite-coefficient framework. No new notion,
  map, theorem, or sorry is introduced by the import repair.

The dependency body was checked byte-for-byte equal from `universe u v` onwards;
its `lean.statement` therefore remains verbatim equal to the declaration signature.
Every delivered sibling is compiled separately by `scompile.py` in dependency order.
