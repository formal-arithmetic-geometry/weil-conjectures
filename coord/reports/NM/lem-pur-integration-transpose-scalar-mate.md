## Worker report

The module Sheaf.Paper.IntegrationTransposeScalarMate states
AlgebraicGeometry.Etale.IntegrationScalar.integrationTransposeScalarMate.
Its proof is sorry. The five auxiliary definitions only abbreviate the precise objects and
composites introduced by the item's statement; all contain real data. No independent notion
or dependency repair is needed. No statement correction or statement dispute is proposed.

Hypothesis and clause correspondence (names below are in namespace
AlgebraicGeometry.Etale.IntegrationScalar):

- Finite commutative rings and a unital map: A and B : Type (u + 1), CommRing instances,
  Finite instances, and φ : A →+* B. The coefficient and scheme universes follow the
  published ordinary small-etale category convention, with Scheme.{u}.
- A compactifiable separated finite-type map between Noetherian schemes: X, Y with
  IsNoetherian instances; f with IsSeparated, LocallyOfFiniteType and QuasiCompact;
  c : Compactification f. This chooses the compactification used to construct the
  compact-support functor, without imposing a geometric restriction beyond the statement.
- Ordinary unbounded categories: DerivedCategoryModule A X and its Y/B variants throughout.
  Scalar tensor Q is the published scalarExtension φ; F is the published
  rightDerivedLowerShriekOfCompactification (ModuleCat R) c.
- The actual right adjoints and counits: R, R' are functors, and adj, adj' are actual
  adjunctions from the specified F functors. Their counits and Hom equivalences are used
  directly. This quantifies over the actual choices permitted in the statement and does
  not postulate an unrelated exceptional comparison.
- The canonical q and its projection square: compactScalarMap φ c is the published
  proper/open arrow. Its invertibility and all-input projection square are supplied by
  etaleCompactScalarCoherence. ExceptionalCoefficients.comparisonInverse φ c is exactly
  its inverse on this domain. There is no extra invertibility hypothesis on q, including
  q evaluated at R.obj of the coefficient unit.
- W, W', and the orientation isomorphism: the corresponding binders W, W', and
  l : (scalarExtension φ X).obj W ≅ W'.
- The traces: t and t' have sources F(W) and F'(W') and targets the respective derived
  monoidal units, namely the constant coefficient sheaves in degree zero.
- The trace equation is ht: q_W ≫ F'.map l.hom ≫ t' = Q_Y.map t ≫ unitIso.hom.
  The unitIso is the uniquely normalized coefficient multiplication comparison of
  ExceptionalCoefficients; no arbitrary unit map is introduced.
- Invertible projection maps on all inputs: hP and hP' quantify over the entire
  corresponding derived categories and assert IsIso of compactScalarProjection.
- object f W K is the exact G₀ object, namely derived pullback of K tensor W.
  integration c W t hP K is inverse projection, tensoring the trace, then the normalized
  right unitor. The last factor makes explicit the statement's suppressed K tensor A = K.
- gamma is adj.homEquiv applied to integration, exactly its actual adjoint transpose.
- comparison is compactScalarProjectionTarget followed by tensoring l.hom. This is the
  prescribed scalar tensor/pullback comparison followed by l; all factors are canonical
  isomorphisms, although the abbreviation returns their underlying composite arrow.
- mate is adj'.homEquiv applied to q_(R K) inverse followed by Q_Y of adj.counit.app K.
  Thus it is precisely b, with the direction required by def-weil-pbc-adjunction-mate.
- The first conjunct is q_G inverse ≫ Q_Y.map c = F'.map a ≫ c'. The second is
  Q_X.map gamma ≫ b = a ≫ gamma'. These are the two displayed equations, written in
  Lean's diagrammatic composition order.
- The third conjunct is the implication from IsIso of both gamma components to IsIso b.
  It makes no claim that taking an arbitrary mate preserves an isomorphism.
- K is arbitrary in the unbounded category. In particular it can be
  𝟙_ (DerivedCategoryModule A Y), representing A_Y[0]. The same normalized unitIso,
  tensorIso, scalarPullbackIso and derived right unitor are used for this substitution.
  There is no boundedness, Tor-amplitude, flatness or constructibility binder.

Dependency declarations read and used:

- WeilConjectures.AlgebraicGeometry.DerivedCategories and
  WeilConjectures.SixFunctors.Etale.Derived.Coefficients:
  AlgebraicGeometry.Etale.DerivedCategoryModule.
- Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel:
  SheafOfModules.DerivedChangeOfRingsCochainModel and
  SheafOfModules.nonempty_derivedChangeOfRingsCochainModel. This general ringed-site
  construction is imported through the coherence module; the ordinary etale specialization
  is its already published scalarExtension, rather than a second ringed-site construction.
- Sheaf.Paper.EtaleCompactScalarCoherence:
  AlgebraicGeometry.Etale.compactScalarMap, compactScalarProjection,
  compactScalarProjectionTarget and etaleCompactScalarCoherence.
- Mathlib.CategoryTheory.Adjunction.Mates: CategoryTheory.mateEquiv. The explicit component
  form in mate uses the same counit/Hom-bijection convention; no new mate convention is made.
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses:
  SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback.
  The imported compactScalarProjectionTarget is the published ordinary etale specialization
  using the normalized tensorIso and scalarPullbackIso; the general interface is not copied.
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriek:
  AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification.
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint:
  AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification.
  The delivered theorem permits the actual right adjoint and actual adjunction as supplied
  mathematical data, rather than requiring a particular implementation of its choice.
- Sheaf.Paper.ExceptionalCoefficientMaps:
  AlgebraicGeometry.Etale.ExceptionalCoefficients.comparisonInverse, tensorIso and unitIso.
  This proof dependency is publicly imported through the coherence module.

Edge cases: for f = identity and W the unit, inverse projection followed by trace is the
normalized unitor, and the two equations are the unit/adjunction identities. W = 0 and W' = 0
give zero integrations without forcing b invertible, since the gamma-isomorphism condition
then only holds when its targets are zero. Zero coefficient rings and empty schemes remain
allowed; none of the binders requires a nonzero coefficient or a nonempty scheme. The
nonflat quotient Z/4 → Z/2 remains allowed, and Q of a right-adjoint unit object need not
be bounded below. The statement never assumes it is. Arbitrary K, including the unit and
unbounded objects, is admitted.

Searches made:

- msearch.py leanfinder, query: "Scalar extension commutes with integration defined by
  inverse projection and trace, and its adjoint transpose agrees with the exceptional
  counit mate". Eight hits, all for module-category extension/restriction adjunctions:
  homEquiv_extendScalarsComp, ExtendRestrictScalarsAdj.Counit.map/counit_app/counit,
  Counit.map_hom_apply, restrictCoextendScalarsAdj, extendRestrictScalarsAdj_unit_app_apply,
  and extendRestrictScalarsAdj_homEquiv_apply. No exact etale integration statement.
- msearch.py loogle, query: "CategoryTheory.Adjunction.homEquiv, CategoryTheory.IsIso".
  Two hits: Functor.isIso_ranAdjunction_homEquiv_iff and
  Functor.isIso_lanAdjunction_homEquiv_symm_iff. Neither states these integration equations.
- msearch.py grep, query: "[Ii]ntegration.*[Tt]ranspose|[Ss]calar.*[Mm]ate", subdirectory
  CategoryTheory. Zero hits.
- rg in lean/WeilConjectures and lean/Sheaf for the node id,
  integrationTransposeScalar, integrationScalarMate, integrationTrace: zero hits.
  Broader scalar/mate and integration/transpose searches found the underlying proper/open
  coefficient constructions and unrelated pro-etale or module results, not this statement.

Validation: scompile.py compiled both its sandbox check and the final library module cleanly
on the live server (12.9 s and 10.6 s). Only the main theorem is postponed; its docstring
contains all six DAG proof steps, including the coefficient-unit substitution.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
