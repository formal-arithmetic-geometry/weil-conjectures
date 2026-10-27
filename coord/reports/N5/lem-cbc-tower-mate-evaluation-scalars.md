## Worker report

The module `Sheaf.AlgebraicGeometry.TowerMateEvaluationScalars` states
`lem-cbc-tower-mate-evaluation-scalars` in several named theorems, all with whole
proof `by sorry`. Its helper definitions construct the canonical single-level maps
and endpoint comparisons from published operations. All declarations are in
`AlgebraicGeometry.ProEtale.StrictTower.MateEvaluationScalars`, and every one is
listed in the node's `lean.declarations`. No dependency module or new DAG node is needed.

Hypothesis and clause correspondence:

- Arbitrary commutative B: `B : Type (u + 1)` and `[CommRing B]`. Schemes have
  universe `u`; the original small pro-etale sites retain object universe `u+1`
  and morphism universe `u`. `coefficients B X` is precisely `constantSheaf` on
  `Scheme.ProEt.topology X`, with no replacement by a constant presheaf.
- Module sheaves, strict inverse systems, ordinary unbounded localization:
  `Modules B X`, `Towers B X`, `Derived B X`. The index `n : ℕ` represents positive
  level n+1, including positive level 1 at n=0. There is no bound on degrees or on
  tower transition maps. The universe-explicit instances `siteSheafify`,
  `siteLocallyBijective`, and `modulesAbelian` are the existing coefficient-universe
  sheafification/local-bijection and Mathlib abelian instances, with actual data.
  They disambiguate an imported instance with unresolved universe parameters.
- The specified termwise operations and adjunctions are imported as `G`, `R`, `J`,
  `adj`, `jAdj`, `gComp`, `jComp`, `evalG`, `evalR`, `evalJ`; none is replaced.
  `g`, `r`, `j`, `dAdj` are abbreviations of the already recorded single-level
  operations. `dJAdj` is the exact-derived open adjunction obtained from `moduleJAdj`
  and the canonical right-derived/exact-descent identification.
- The square has `V W S T : Scheme`, `k : V ⟶ W`, `f : V ⟶ S` (node's r),
  `p : W ⟶ T`, `i : S ⟶ T`, `[IsOpenImmersion k]`, `[IsOpenImmersion i]`,
  `[QuasiCompact k]`, `[QuasiCompact i]`, `[IsProper f]`, `[IsProper p]`, and
  `h : k ≫ p = f ≫ i`. There is no cartesian-square hypothesis. These binders
  occur on `singleDerivedAlpha`, `singleDerivedGamma`, `gamma_formula`,
  `evaluation_alpha`, `evaluation_gamma`, `scalar_alpha`, and `scalar_gamma`.
- The canonical fibre product, b, q, and s are those inside existing `singleAlpha`
  and `alpha`: `pullback p i`, `pullback.fst p i`, `pullback.snd p i`, and
  `squareLift k f p i h`. `singleDerivedAlpha` is localization of that existing
  ordinary `singleAlpha`, with the exact composition identifications inserted.
  Its data is `Localization.liftNatTrans`, not a choice of a natural transformation.
- The specified tower mate is `gamma B k f p i h`. The single-level mate is
  `singleDerivedGamma`, defined by `mateEquiv (dAdj B f) (dAdj B p)` on the exact
  descent of the same projector. `gamma_formula` displays, for BOTH versions,
  the unit at J_i R_f M, R_p of alpha at R_f M, and R_p J_k of the counit.
  This explicitly constructs and states the formula in the tower derived category.
- Exact evaluation and its G/J comparisons are the published `ev`, `evalG` and
  `evalJ`, induced by the termwise equalities `evaluationPullback` and
  `evaluationOpen`. `evaluation_resolution` says the specified `evalR` is invertible
  and gives its canonical K-injective resolution normalization. The equation
  includes the exact evaluation factorization, tower derived unit, evalR, and
  single-level derived unit on the evaluated K-injective tower complex. The
  helpers `towerDerivedUnit` and `evaluationFactors` expose exactly these existing
  quotient and exact-descent maps.
- Units, counits, transposes: `evaluation_transpose` quantifies over ALL M, N and
  t for every scheme morphism f. `evaluation_units_counits` explicitly gives both
  proper-adjunction equations. `evaluation_open_transpose` gives every open
  transpose, including the unit/counit specializations. The comparisons are the
  specified evalG/evalJ/evalR, not existentially chosen isomorphisms.
- Evaluation of the same clopen arrow: `evaluation_alpha` gives the endpoint
  comparison equation with exact singleDerivedAlpha. `evaluation_gamma` gives
  the endpoint comparison equation with singleDerivedGamma for every derived
  tower M and index n. Together with `gamma_formula` this is the asserted
  evaluated unit-square-counit formula.
- Arbitrary ring map: `{Λ : Type (u+1)} [CommRing Λ]` and `φ : B →+* Λ`, with
  no flatness or finiteness hypotheses. `coefficientMap` applies the existing
  constant-sheaf functor to φ. `coefficient_square` is precisely compatibility
  with the canonical constant-section inverse-image maps.
- `moduleRes φ X` is the published `proEtaleRingRestrictScalars` on that coefficient
  map, hence the original `SheafOfModules.restrictScalars`. `Res φ X` is its exact
  termwise descent. Its limit and colimit instances are extracted from the existing
  exactness theorem; no preservation of K-injectives is assumed.
- `scalarGModule` and `scalarG` use the canonical ordinary and exact-derived
  ring-sheaf inverse-image comparisons. `scalarR` is the already specified
  derived direct-image comparison normalized by the right-derived units.
- `scalarJInv` is the inverse open-unit transpose, constructed using `mateEquiv`.
  Its invertibility is the named theorem `scalarJInv_isIso`; its proof plan applies
  the ringed open/scalar theorem on the slice. Thus `scalarJModule` is its actual
  inverse, and `scalarJ` is the exact descent of that same map. There is no bare
  Nonempty choice. Invertibility uniquely determines the inverse used here.
- Open extension retains the underlying section maps: `scalar_open_normalized`
  gives BOTH unit and counit equations, before localization and after exact
  descent, as four explicit universally quantified equations (ordinary unit and counit,
  derived unit and counit). This characterizes the identity
  on the extension-presheaf generators because the fixed open unit sends each
  section to its structure-arrow generator and the counit evaluates it.
  This section description and its proof are spelled out in the docstrings.
- The same identity/zero projector is retained: `scalar_projector` is the explicit
  equality between restricted `clopenModulePi Λ f`, transported by the canonical
  scalar/open and scalar/pullback comparisons, and `clopenModulePi B f`.
  The imported projector is the first-factor section projection, characterized
  uniquely by identity on the open piece and zero on its complement.
  `scalar_alpha` gives the resulting identity for the whole ordinary clopen alpha,
  including its prescribed beta and compositors.
- Derived scalar adjunctions and the final identification: `scalar_transpose`
  quantifies over every derived map t and states the canonical transpose equation.
  `scalar_gamma` quantifies over EVERY `N : DerivedCategory (Modules Λ V)` and
  identifies Res_T of the Λ-mate with the B-mate on Res_V N after scalarR/scalarJ
  endpoint comparisons. It is the primary recorded declaration.
- There are no boundedness, flatness, derived faithfulness/cancellation, cartesian,
  finite-ring, or scalar-K-injective-preservation binders anywhere.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.StrictConstantTowerOperations`:
  `coefficients`, `Modules`, `Towers`, `Derived`, `constantRingIso`,
  `modulePullback`, `moduleDirectImage`, `towerPullback`, `towerDirectImage`,
  `G`, `R`, `adj`, `ev`, `evalG`, `evalR` and `evalR_isIso`.
- `Sheaf.AlgebraicGeometry.StrictTowerOpenExtension`:
  `moduleJ`, `moduleJAdj`, `J`, `jAdj`, `evalJ`.
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows`:
  `squareLift`, `pi`, `alpha`, `gamma`, their clopen and proper/open hypotheses.
- `Sheaf.AlgebraicGeometry.StrictTowerOrdinaryProperOpenArrows`:
  `singleAlpha`, `towerAlpha`, `alpha_eq_localized_singleAlpha`. This already landed
  definition node is added to stmt_deps; the ordinary alpha is not redefined.
- `Sheaf.AlgebraicGeometry.ProperOpenClopenProjector`:
  `clopenModuleAdj`, `clopenModulePi`, `clopenModule_section_projector`,
  `clopenTowerAbelian`. Its already landed node is added to stmt_deps because the
  actual ordinary projector occurs in scalar_projector's signature.
- `Sheaf.AlgebraicGeometry.TowerOpenBetaNormalization` supplies the ordinary beta
  and unit-preserving open compositors used by singleAlpha, through its import.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`:
  `Scheme.proEtaleRingRestrictScalars`, its properties,
  `proEtaleRingRestrictionPullbackInv`, its invertibility,
  `proEtaleRingRestrictionDerivedPullback`,
  `proEtaleRingRestrictionDerivedDirectImage`,
  `proEtaleRingDirectImageDerivedUnit`, `proEtaleRingSheafChangeAdjunction`.
  Its already landed node is added to stmt_deps for these canonical maps.
- `Sheaf.CategoryTheory.RingedOpenScalarAdjunction`:
  `SheafOfModules.RingedOpenScalar.comparison`, retained as a proof import.
  Its node is in proof_deps only: the normalization equations are written inline
  and do not use its `Equations` predicate.
- Mathlib: `Scheme`, `Scheme.ProEt`, `constantSheaf`, `SheafOfModules` (through
  `CategoryTheory.ringedSiteModules` in the recorded RingedSiteModules module),
  `Functor.ofOpSequence` (ℕ reindexing), `DerivedCategory`, `pullback`,
  `IsOpenImmersion`, `QuasiCompact`, `IsProper`, `IsClosedImmersion`,
  `SheafOfModules.restrictScalars`, `mateEquiv`, `Localization.liftNatTrans`.
  Read the full signatures/docstrings in their recorded source modules.
- Plain proof imports are the recorded tower-adjunction realization,
  universe-correct ringed-site K-injective resolutions, normalized tower derived
  evaluation, and weakly-etale localization. The levelwise-abelian Mathlib leaf
  is exposed by the strict-operations imports. All proof modules are included;
  no additional import is omitted for an import cycle.

Source read: Stacks sites-cohomology.tex, lemma-derived-pushforward-composition
(Tag 0D6E) and remark-base-change (Tag 07A7), with the complete adjunction
construction. Read the current DAG statements and the complete source definitions
of the tower, open, mate and scalar interfaces. The ordinary clopen alpha's
blueprint node and its localization characterization were also read.

Edge cases checked before finalizing: n=0 denotes positive level 1; identity square;
cartesian square (canonical lift is the pullback isomorphism); empty V or empty
open; zero module/complex; zero coefficient ring; infinite coefficient rings;
nonflat coefficient map ℤ→ℤ/2; noncartesian square; unbounded complexes and towers
with no common cohomological bound. Every case retains the same definitions and
is admitted by the binders. Arbitrary tower transition maps are allowed.
No statement defect or STATEMENT-DISPUTED flag was found.

Searches actually run through msearch.py:

- LeanFinder: “Evaluation and restriction of scalars preserve the proper adjunction
  mate of clopen extension by zero on unbounded derived strict inverse systems”.
  Eight hits: condensed locally constant adjunctions and counits, condensed
  profinite-solid maps, Nobeling product evaluation, and ordinary module scalar
  extension counit. None states this pro-etale strict-tower comparison.
- Loogle: `CategoryTheory.mateEquiv`. Twelve hits, including mateEquiv, its unit,
  counit, composition laws and the iterated correspondence. These provide the
  categorical constructor, not this normalized geometric assertion.
- Mathlib grep: `eval.*[Mm]ate|[Rr]estrict.*[Mm]ate` in CategoryTheory. Five hits:
  rigid monoidal coevaluation-mate lemmas and an unrelated sheaf comment.
- LeanSearch: “Evaluation of derived strict inverse systems preserves adjunction
  transposes and restriction of coefficient scalars preserves the proper open
  clopen mate”. Eight hits: derived adjunction constructors, ordinary module
  restriction/coextension adjunctions, scheme-module restriction adjunction,
  topological sheaf pushforward, and SheafOfModules pullback adjunction. No exact match.
- `rg` in WeilConjectures and Sheaf for the item ID, `single(Level|Gamma|Alpha)`,
  `evalGamma`, `scalarGamma`, and `mateEvaluation`: found existing `singleAlpha`
  and finite/etale-origin `gamma_evaluation`, but no theorem covering this item's
  arbitrary coefficients and every single-level derived object. Broader evaluation,
  restriction and mate searches likewise supplied only helper interfaces.

Validation: scompile.py compiles the delivered module in module mode under both its
sandbox and actual library name, within the fixed 60-second per-file limit, with
no errors or warnings. All variables and universes are bound explicitly;
`set_option autoImplicit false` is in force. No global build or direct git command
was run and no shared repository file was written. Definitions contain actual data;
all fourteen postponed theorems belong to this item's statement and carry their
source and a complete natural-language proof plan.

## Returned-delivery repair

The independent review of immutable head `8c9f35d22eb4` found that
`lem-cbc-ringed-open-scalar-adjunction` occurred in `stmt_deps` only to own
`SheafOfModules.RingedOpenScalar.Equations`, a plain Prop definition without a
definition node. Following the review's inline-equations option, expanded both
occurrences in `scalar_open_normalized`: each is the conjunction of the unit
equation for every source object and the counit equation for every target object.
The first pair uses `moduleJAdj` and `moduleRes`; the second uses `dJAdj` and `Res`.
These are exactly the original predicate's body, with the inverse of the symmetric
`scalarGModule`/`scalarG` comparison rendered as its `hom`. The four clauses keep
the original two-pair grouping. No hypothesis, mathematical clause, or canonical
map changes. The section identity remains fixed by the same canonical
`scalarJInv` transpose and its uniquely determined inverse.

Dropped only this theorem from `stmt_deps`, retained it in `proof_deps`, and
changed its import from public to proof-only. The other two theorem dependencies
remain in `stmt_deps`: the derived direct-image scalar comparison chooses the
unique normalized comparison supplied by the ring-sheaf adjunction theorem;
the actual clopen projector uses its owning theorem's isomorphism instance.
Compared the retained packet against the current read clone: only the item's
`lean` and its permitted interface dependency additions differ. The prescribed
delivery wrapper rebases the packet against current server main.

The initial saved-packet dry run passed (`f40857975b3`), but did not resolve this
semantic dependency fault. The present repair changes the actual Lean signature
and dependency list rather than re-pushing that unchanged packet.

Repair validation: `scompile.py` passed for both the sandbox module (57.3 s)
and actual library module (16.0 s), with no compiler errors or warnings. The
source self-check confirms all four explicit equations, preserved other theorem
interfaces, exact primary recorded signature, sorry-only theorem bodies, and
100-column limit. No definitions or binders changed.

## Second reading by N5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
