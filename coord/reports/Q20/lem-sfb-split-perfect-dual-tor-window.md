## Worker report

The module `Sheaf.Algebra.Homology.SplitPerfectDualTorWindow` states
`CategoryTheory.splitPerfect_dual_torWindow`, with one `sorry`. Its only data definition,
`CategoryTheory.splitPerfectDualProjection`, composes the already existing product projection
`homComplexπ` with internal Hom of `HomologicalComplex.singleObjXSelf`. There is no choice of
an arbitrary projection or isomorphism, no new tensor, and no postponed data.

Hypothesis and clause correspondence, in the order of the unchanged mathematical statement:

- The site is `(C : Type c) [Category.{v} C] (J : GrothendieckTopology C)`.
  The coefficient and module universe is `max c v r`; the explicitly bound independent
  levels `c`, `v`, `r`, and derived morphism level `w` do not equate site object and arrow
  universes. `EssentiallySmall.{max c v r} C`, sheafification, and locally-bijective
  sheafification hypotheses express the chosen size convention and its standard structures.
  In particular the small pro-etale size pattern `c = t+1`, `v = t` is included.
- `R : Sheaf J CommRingCat.{max c v r}` is the arbitrary commutative coefficient sheaf B.
  `RingedTensorModules J R` unfolds to the recorded `ringedSiteModules`, hence precisely
  Mathlib's `SheafOfModules` over its underlying ring sheaf. `HasDerivedCategory.{w}`
  supplies the unbounded localization and `DerivedCategory.Q` its localization functor.
- `a b : ℤ`, `_hab : a ≤ b`, and `_hE : ∀ n, n < a ∨ b < n → IsZero (E.X n)` give the
  specified bounds, without assuming a priori that E has projective terms as global objects.
- `pE : StrictPerfectCoefficientPackageOnSite _ E` contains exactly the function
  `N : ℤ → ℕ`, degreewise maps `i`, `p`, and `splitting : i n ≫ p n = 𝟙 _`.
  Its finite product of copies of the unit is the finite free module B^N; in this additive
  category finite products and finite sums agree. There is no chain-map condition.
- Throughout the conclusion D is literally `homComplex E (ringedTensorUnitComplex J R)`.
  The latter complex is the existing `HomologicalComplex.single` of B in degree zero.
  The derived dual is literally `derivedInternalHomOfUniverses J R` applied to
  `(op (DerivedCategory.Q.obj E), DerivedCategory.Q.obj (ringedTensorUnitComplex J R))`.
- The first conjunct is exactness of `tensorLeft (E.X n)` and
  `(SheafOfModules.homFunctor R).obj (op (E.X n))`, for every integer n. `exactFunctor`
  means preservation of finite limits and finite colimits, exactly exactness here.
- The second conjunct universally quantifies I and f : B[0] → I and assumes only
  `I.IsKInjective` and `QuasiIso f`, then asserts `QuasiIso` of the actual Hom-functor
  image of f. I has no boundedness assumption and is not fixed to a preferred resolution.
- The third conjunct gives an isomorphism in D(B) from Q(D) to the specified derived dual,
  expressing that D represents that dual.
- `IsIso (splitPerfectDualProjection J R E n)` gives the canonical degree identification
  D^n ≅ Hom(E^(-n),B), not merely existence of an unrelated isomorphism. The following
  equality is `d_D ≫ projection_(n+1) = (n+1).negOnePow •
  (projection_n ≫ homObjMap (E.d (-(n+1)) (-n)) (𝟙 B))`.
  Thus a section φ is sent to (-1)^(n+1) φ ∘ d_E^(-n-1), with the correct sign.
- The next conjunct is `IsZero (D.X n)` if `n < -b ∨ -a < n`.
- Precomposition by `pE.p (-n)` and then `pE.i (-n)` is asserted to compose to identity.
  These are exactly p* and i* on Hom(E^(-n),B). Through the preceding canonical degree
  identification these give the displayed splitting of D^n. A separate conjunct identifies
  the intermediate Hom(B^N,B) with the same finite power B^N.
- `SheafOfModules.IsFlatOnSite` is asserted for each `E.X n` and `D.X n`, using its
  recorded definition as exactness of the sheafified tensor functor.
- The final conjunct quantifies every `M : RingedTensorModules J R` and `q : ℤ`.
  M[0] is the actual `CochainComplex.singleFunctor _ 0` value. For the existing
  `siteDerivedTensorIndependentCoefficients`, applying `DerivedCategory.homologyFunctor`
  gives `IsZero` for E ⊗^L M if `q < a ∨ b < q`, and for RHom(E,B[0]) ⊗^L M if
  `q < -b ∨ -a < q`. M has no flatness or other hypothesis.
- No constant-coefficient, enough-points, or constructibility hypotheses occur.

Dependency declarations used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`
  (through the existing transparent `RingedTensorModules`).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`, Q.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`, differentials, X.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`: the publicly retained
  `SheafOfModules.StrictPerfectCoefficientPackageOnSite` (read in StrictPerfectPackageOnSite).
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`: `homObj`, `homObjMap`,
  `homFunctor`; the actual sections are linear maps on localized sites.
- `WeilConjectures.Algebra.Homology.HomComplex`: `homComplex`, `homComplexFunctor`.
- `WeilConjectures.Algebra.Homology.HomComplexComponents`: `homComplexπ`, selected by the
  existing `homComplex_projections_exists` of the recorded Hom-projection node.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`: `derivedInternalHomOfUniverses`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `cochainModulesMonoidal`, giving the existing ordinary sheaf tensor and `tensorLeft`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients` exposes the recorded K-flat notion.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`
  and `CategoryTheory.exactFunctor`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`: `DerivedCategory.homologyFunctor`
  and its representative comparison `homologyFunctorFactors` (existing dependency repair below).
- Added landed definition dependency `def-zl-ringed-derived-closed-symmetric-monoidal-data`
  (`existing: true`), module `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`,
  owns the transparent category spelling `RingedTensorModules` and the concrete
  `ringedTensorUnitComplex`. Their definitions require no monoidal existence theorem.
- Added landed dependency `lem-weil-pbc-site-derived-tensor-descent`, module
  `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`, supplies
  `SheafOfModules.siteDerivedTensorIndependentCoefficients`, with its K-flat localization
  and representative specification. Added landed `lem-sc-hom-complex-projections` exposes
  the exact canonical projection used by the helper. These additions change no mathematics.
- Proof-only imports are the recorded `quasiIso_homComplex_map_of_bounded_exact_terms`
  from `WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso` and
  `isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite` from
  `Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients`.
  The other proof-only nodes (finite-retract-dual-exact, bounded-dual-components,
  kflat-single-tensor-comparison) have no recorded Lean yet, so no nonexistent modules
  are imported. They are not needed to type this stage-2 statement.

Source checks: read the actual sections of `literature/stacks-project/sites-cohomology.tex`
for 08JH (K-injective Hom comparison), 08JJ (dual degree -n and finite-free summands),
08G1 (2 implies 1, termwise flat tensor), and 06YQ (bounded-above flat implies K-flat).
The proof docstring follows all seven DAG proof steps and names their uses.

Edge checks: zero ring, zero E, zero M, rank N_n=0, empty site, and a=b all retain
well-typed quantifiers and conclusions. For a=b=k the reflected interval is [-k,-k].
At n=0 the dual differential has sign -1, at n=1 sign +1, and at n=-1 sign +1.
The bounds include their endpoints, including negative endpoints. Splittings outside
[a,b] impose no positive-rank condition. No characteristic exclusion is used.

Searches for an existing match:

- `msearch.py ... leanfinder "Bounded complex of finite free retract sheaves signed internal
  Hom dual has flat terms and reflected Tor amplitude"`: eight hits, principally generic
  DerivedCategory IsLE/IsGE support facts and CochainComplex.IsKProjective; no exact match.
- `msearch.py ... loogle "SheafOfModules, CochainComplex"`: zero hits.
- `msearch.py ... grep "splitPerfect|split_perfect|dual.*tor|dual.*Tor" CategoryTheory`:
  25 hits about unrelated category duality; no match.
- `rg` in Mathlib Algebra/Homology for TorAmplitude/strictPerfect/KFlat found no match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for split-perfect, dual/Tor,
  strict-perfect, and the exact item id: found RingedSiteStrictPerfectHom, generic
  `DerivedCategory.torAmplitudeIn_of_exactPairing`, and pro-etale fixed-coefficient
  `torAmplitudeIn_derivedDual`. Read those signatures: none states all the present
  clauses on an arbitrary commutative ringed site with the specified bounds and splittings.
- `grep -rn` for the exact item id under `lean/WeilConjectures`: no hit.

No mathematical statement correction, new node, or STATEMENT-DISPUTED flag is needed.
Compilation: the complete module passed both sandbox and actual-module-name server compiles
through scompile.py, with no warnings. Early universe inference errors were diagnosed by
small #check probes and corrected by explicit coefficient/unit universes. All probes were
removed from the delivery.

## Dependency modules

`def-weil-derived-cohomology-sheaves`: an existing-interface lean-only repair. The previous
primary `WeilConjectures.sfModelCohomology` belongs to the intrinsic common-stage Weil pair
category; its full signature and docstring do not accept an arbitrary sheaf of rings on a
site. The node's unchanged `mathlib_match` already specifies exactly the generic
`DerivedCategory.homologyFunctor`. Rebind its `lean` to that existing Mathlib declaration
and its canonical representative comparison `homologyFunctorFactors`. This adds no module,
no declaration and no alternate cohomology definition. Consumer validation is the main
module's two compiled `IsZero ((DerivedCategory.homologyFunctor _ q).obj ...)` clauses.
The old specialized declarations remain in their original source module.

## Second reading by Q20

This is the worker's final rereading, not an independent-agent review; the dispatched brief
reserves the independent reading to the maintainer and prohibits starting other agents.
I reopened the node and final file and checked every hypothesis and all ten conclusion
conjuncts against the correspondence above. In particular the comparison ranges over every
resolution, the projection is the product projection rather than an arbitrary identification,
the sign is n+1, the same p and i occur in the dual splitting, both exactness and flatness
are present, and the two tests use the original E and its actual derived dual with arbitrary
M. No clause mismatch was found. The only repair outside the item's lean record and added
landed imports is the cohomology dependency binding described above.

## Returned delivery repair

Repaired the H2 theorem-statement-dependency finding on immutable head `d17c0eceb3b5`.
Reopened the existing definition node
`def-zl-ringed-derived-closed-symmetric-monoidal-data`: its `existing: true` Lean record
lists both `CategoryTheory.RingedTensorModules` and
`CategoryTheory.ringedTensorUnitComplex`. Read their complete definitions in
`RingedDerivedClosedSymmetricMonoidal.lean` lines 52–61: the first is the transparent
ringed-site module category, and the second is the actual single complex of its unit.
Replaced `lem-sf-ringed-derived-closed-symmetric-monoidal` in the item's `stmt_deps`
with that existing definition node. The import remains because it supplies those two
definitions; no assertion of the monoidal existence theorem is used in the signature.
The genuine theorem dependencies `lem-sc-hom-complex-projections` and
`lem-weil-pbc-site-derived-tensor-descent` remain: the canonical projection and the
derived-tensor functor use their existence declarations.

Second reading of this repair: the Lean module and its verbatim recorded signature are
unchanged, so all hypotheses and the ten conclusion clauses retain the correspondence
above. The natural-language statement, proof and proof dependencies are unchanged.
The cohomology dependency repair is retained, as reviewed in the return. No new node or
new declaration is introduced by this repair.

Repair validation: `scompile.py Q20 lem-sfb-split-perfect-dual-tor-window` passed
both the sandbox-name and actual-module-name compiles with no diagnostics. Checked
that the item changes only `lean` and `stmt_deps`, the dependency changes only `lean`,
and `lean.statement` remains verbatim identical to the full theorem signature.
