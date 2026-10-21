## Worker report

The module `Sheaf.Paper.IntegralQuotientExchangeComparison` states
`AlgebraicGeometry.ProEtale.IntegralQuotient.integral_quotient_exchange_comparison`.
Its single theorem has proof `sorry`; all helper definitions have real data. The node's
statement, dependencies and proof are unchanged. Helpers belong to the maps/realization
already requested by this node and are listed in `lean.declarations`.

Hypotheses and clauses, in the order of the node:

- Prime ell: `(l : ℕ) [Fact l.Prime]`. The extension is `(E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`.
- The valuation ring and uniformizer are the dependency's canonical
  `Padic.coefficientExtensionIntegers` and `Padic.coefficientExtensionUniformizer`,
  already used by `integral`, `finite`, and `reduction`. No different ring is chosen.
- R_T is `condensedRingObj (integral l E) T`, where `integral` is the recorded
  `sfbCondensedIntegers`. Its limit identification and actual finite projections
  are `sfb_integral_coefficient_limit`, imported through the coefficient interface.
- S_T is `condensedRingObj (finite l E n) T`. The inherited indexing uses exponent
  `n + 1`, so `n : ℕ` runs through exactly all positive exponents, including one.
  `sectionReduction` reconstructs the actual map `coefficientMap (reduction l E n) T`.
- The categories are `DerivedCategory (Modules … T)`: ordinary unbounded internal
  modules, not a complete or constructible subcategory. `D (reduction l E n) T`
  is the existing total left derived extension. `TensorNormalization` and
  `TensorNormalized` in the imported direct-image statement identify its restriction
  with uncompleted relative tensor; we introduce no replacement tensor or scalar functor.
- The scheme square is `{X' X Y' Y : Scheme.{u}}`, morphisms `h,f',f,g`, and
  `(sq : ChosenCartesianSquare h f' f g)` including its specified pullback identification.
- `L`, `F`, and `adj` are precisely the dependency's derived full module composites
  and their adjunctions. `ambient` is the recorded `condensedAmbientExchange`, exposing
  those same functors through the typed interface. No exchange inverse is used.
- Lambda is the family `b`. Its hypothesis `hb : ∀ u, PullNormalized … u (b u)`
  specifies exactly the dependency's balanced pullback comparison, using its universal
  computation counits. The dependency asserts existence of this family. Quantifying
  over its normalized presentation makes no additional geometric assumption; it also
  avoids selecting data from a mere existence theorem. Rho is exactly the existing
  `QuotientChange.rho … u (b u)`, formed with the actual adjunctions.
- The first conjunct is equality of natural transformations. Evaluating it at any K
  gives, in composition order, `L_g,S(rho_f) ≫ Ex_S(D_X K) ≫ F_f',S(lambda_h)`
  equal to `lambda_g ≫ D_Y'(Ex_R K) ≫ rho_f'`. Whiskering fixes their common source
  `F_R f ⋙ D_Y ⋙ L_S g` and target `L_R h ⋙ D_X' ⋙ F_S f'`. These are precisely
  the source and target displayed in the node when evaluated at K.
- The next two `IsIso` conjuncts record the specified source/target comparison
  isomorphisms from the direct-image comparison. Together with `b` as a natural
  isomorphism, they express identification of the reduced and finite exchanges.
- Naturality in K is retained as equality of natural transformations, rather than
  merely equality of unrelated morphisms for chosen representatives.
- The final realization clause is explicit, not only an assertion about endpoints.
  `ExchangeRealized` identifies each ambient exchange under the fixed termwise
  derived section equivalences and their actual push/pull comparisons. The section
  exchange is independently defined from `derivedAdjunction` and `sectionSquare`,
  which uses `derivedPullbackComposition`, the scheme-square equality, and its inverse.
- The existential `q T : ScalarDerivedPair (sectionReduction …)` is the existing
  sectionwise sheafified scalar functor, its universal unbounded derived pair, its
  K-flat computations and its normalized ordinary/derived scalar adjunctions.
  The ordinary equivalence comparison `e₀` is fixed on every balanced generator;
  `e` is fixed by the universal cochain computation equation on flat-term K-flat
  representatives. These are the two conjuncts of `ScalarRealized`. Thus the
  existential witnesses are characterized canonical comparisons, not arbitrary maps.
- The next conjunction identifies `χ` with `b` under `e` and the specified geometric
  pullback comparisons. `sectionProjection` is independently the mate of `χ` under
  the actual section geometric adjunctions. The following equation identifies this
  projection with `rho` under `e` and the specified direct-image comparisons.
- The final natural-transformation equation is the normalized finite rectangle:
  pullback of the projection followed by finite exchange equals `χ_g`, reduction
  of integral exchange, the projection for f', and finite pushforward of `χ_h.inv`.
  It has exactly the maps and orientation of `finiteReductionExchange_rectangle`,
  in the reconstructed coefficient coordinates, now identified with the internal
  maps by the preceding equations. It is not obtained by defining the section
  exchange as transport of the internal exchange.
- No properness, completeness, boundedness, constructibility, or exchange-isomorphism
  hypothesis is present. The two `∀ T, HasDerivedCategory.{u+1} …` binders select
  the localization universes for section modules as in the existing normalization
  interface. They are size/existence choices, not restrictions on complexes or schemes.
  Scheme sites keep object universe u+1 and morphism universe u; coefficients and
  section modules are in u+1. No equality of site object and morphism universes is imposed.

Dependency declarations used (names below are in their source namespaces):

- `Sheaf.Paper.IntegralQuotientDirectImageComparison`:
  `IntegralQuotient.integral_quotient_direct_image_comparison` and its reexports
  `integral`, `finite`, `reduction`, `QuotientChange.Modules`, `D`, `L`, `F`, `adj`,
  `PullNormalized`, `rho`, `extension`, and `compute`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` (through coefficients):
  `Padic.finite_coefficientExtensionRing` and the original coefficient constructions.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, the point pullback, and its commutative structure.
- `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`:
  `sfb_integral_coefficient_limit`, with its actual quotient-projection normalization.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `CondensedRing.moduleObjectDerivedPullback`, `moduleObjectDerivedPushforward`, and
  `derivedUpperStarLowerStarAdjunction` from its public upstream import.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`:
  the existing derived relative tensor/Hom structures, inherited through coefficients.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and its existence theorem,
  inherited through coefficients; no second derived-extension construction is supplied.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `ChosenCartesianSquare`.
- `Sheaf.Paper.CondensedAmbientExchange`:
  `CondensedRing.condensedAmbientExchange` and `condensedAmbientPullbackComparison`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `Scheme.ProEt.topology`.
- Size convention: explicit `universe u`, section `HasDerivedCategory.{u+1}` binders;
  this dependency has no definiendum or declaration to import.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `InternalAbelianSheafModule.sectionModuleEquivalence` and `sectionRingSheaf`.
- `Sheaf.Paper.SectionDerivedPushpullNormalization` and its realization reexports:
  `ModuleRingedComparison.derivedFunctor`, `derivedPullback`, `derivedPushforward`,
  `derivedPullComparison`, `derivedPushComparison`, `derivedAdjunction`,
  `derivedPullbackComposition`, `sectionLocalizationComparison`,
  `sectionDerivedPushpullNormalization`.
- `Sheaf.CategoryTheory.InternalSectionScalarAdjunction`:
  `sectionScalarMap`, `internalScalarGenerator`, `internal_section_scalar_adjunction`,
  and the imported `SheafOfModules.ScalarDerivedPair`.
- `Sheaf.Paper.FiniteReductionExchangeRectangle`:
  `Scheme.finiteReductionExchange_rectangle`, used as the proof-plan reference for
  the independently specified normalized section rectangle, not substituted for
  the internal/section identification asserted here.
- Remaining recorded proof modules are imported directly: K-flat resolution,
  internal/section tensor comparison, FourArrows, IntegralFinitePullbackComposition,
  ProfiniteCoefficientInverseImage, RingedTopoiCanonicalTensorPullbackOfUniverses,
  and `CategoryTheory.exchangeMate_cube`. The general mate definition is Mathlib's
  `mateEquiv`, inherited from the imported framework.

Edge cases checked before and after writing: exponent one is n=0 in the inherited
indexing; all higher positive exponents are retained. Empty schemes, zero complexes,
identity edges and identity squares are not excluded. Neither exchange is assumed
invertible. E=Q_l and ramified finite extensions use the same constructions.
The two-term quotient need not be flat over the integral coefficients: all scalar
extensions remain derived, and K-flatness is tested only for representative computations.

Searches made:

- `msearch.py … leanfinder`: "Canonical derived extension of integral sheaf coefficients
  to a uniformizer quotient commutes with the adjunction mate defining geometric base
  change exchange". Eight results: Jacobi–Zariski/cotangent-complex and normalization
  lemmas, none the normalized internal exchange or its section realization.
- `msearch.py … leansearch`: "Derived scalar extension of sheaf coefficients respects
  the canonical base change exchange as a normalized adjunction mate". Eight results:
  underived sheaf pullback adjunction and ordinary module scalar adjunctions, no match.
- `msearch.py … loogle '"mateEquiv", "comp"'`: ten mate-composition results,
  including `mateEquiv_vcomp`, `mateEquiv_hcomp` and conjugate-equivalence formulas.
  These are abstract proof tools, not this coefficient theorem.
- `msearch.py … grep '(exchange|baseChange).*(quotient|scalar)|(quotient|scalar).*(exchange|baseChange)'`:
  25 mostly algebraic tensor/base-change hits; no sheaf-derived exchange match.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for exchange/scalar/quotient
  combinations; `grep -rn` for the item id in `lean/WeilConjectures`: no existing
  declaration of this node. The existing constant-scalar DirectImageScalarExchange
  concerns constant coefficients, not the continuous integral coefficient object
  and its internal/section normalization. FiniteReductionExchangeRectangle supplies
  the section-side formula but not the required identification. Existing direct-image
  normalized scalar interfaces are reused in full. A declaration-name search also
  found no collision with the new full names.

No statement dispute, correction, new DAG node, or dependency repair is needed.

## Second reading by NM

The dispatcher explicitly forbids starting another agent. This section records a second
self-reading with the node, dependency signatures and completed module open; it does not
claim an independent reviewer. The maintainer's independent delivery review remains due.

I checked all coefficient hypotheses, the positive-level reindexing, unbounded internal
module categories and actual scalar extension against the direct-image dependency.
I matched each of the three arrows on both sides of the node's equation to the three
whiskered transformations in the first conjunct. The orientations and endpoints agree.
I checked that the scalar realization fixes generators and K-flat computation, the
exchange realization uses the independently specified derived adjunctions/compositors,
and the final rectangle uses the inverse horizontal comparison on the target side.
The rho identification uses the actual projection mate, so the section clause is
not just another equation between isomorphic endpoints. IsIso assertions concern rho,
not the exchanges. Every theorem proof remains sorry and every definition has real data.

Compile-driven repairs made the existing push/pull comparisons explicitly typed to
avoid unfolding two large implementations of the same functor, specified the site and
coefficient arguments of ScalarDerivedPair and IsFlatOnSite, and kept field notation
syntactically intact across line breaks. These change no mathematical hypotheses or
conclusions. The final file has no auto-implicit variables, private definitions or
file-local notation. Source read: blueprint paragraph (3) and Stacks 07A7/0E47/0E48.

Validation: scompile.py passed both sandbox and library-module compilation under the
normal 60-second limit (11.1 and 11.7 seconds before the final proof-import completion).
The delivery dry run below also recompiles the final module.
