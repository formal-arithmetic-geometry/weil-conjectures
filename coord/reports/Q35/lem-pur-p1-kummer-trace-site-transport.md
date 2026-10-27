## Worker report

Module: `Sheaf.Paper.P1KummerTraceSiteTransport`; main declaration:
`AlgebraicGeometry.ProEtale.VectorIntegrationSite.p1KummerTraceSiteTransport`.
Only the main theorem is postponed, with whole proof `sorry`. Its docstring gives
the nine-step mathematical argument of the DAG (the last two steps are combined).
All helper definitions have actual data; no auxiliary maps, isomorphisms, flatness,
Cartier hypotheses, Noetherianity or separatedness are assumed by the main theorem.

Clause-by-clause reading:

- The finite-field/prime/finite-extension data are exactly
  `P : WeilConjectures.PurityFiniteSetting`. The coefficient level is `P.level`,
  positive by `P.level_pos`. In finite-site coordinates it is `P.level - 1`:
  the coordinate quotient has exponent `(P.level - 1) + 1 = P.level`.
  This includes level one and uses no ramification divisibility.
- A finite-type k-scheme is `S`, `aS : S ⟶ Spec (CommRingCat.of P.field.k)`,
  `[LocallyOfFiniteType aS] [QuasiCompact aS]`. There is no separatedness binder.
  `isNoetherian_of_locallyOfFiniteType aS` supplies the Noetherian instance to
  the predicate, not an additional premise. `∃ hS : IsUnit (...)` supplies the
  source-implied invertibility of the coefficient prime, again as a conclusion.
- Every positive annihilating exponent is `∀ r : ℕ, ∀ hA : (l^(r+1) : A)=0`.
  The minimum exponent r=0 means the node's r=1. This is a bijective index
  change on positive integers, not a restriction to a selected exponent.
- Both sites and their ordinary unbounded derived categories are the recorded
  `Sheaf ... (ModuleCat.{u+1} A)` presentations. `comparison` is the recorded
  termwise derived `comparisonUpperStar`. No constructible category replaces it.
- `ordinaryFiniteLine`, shifted by 2, is the etale scalar-extended Kummer line.
  `line` is its comparison coordinate. The recorded `twistDerived` and
  `twistComparison` identify it with the specified inverse-limit pro-etale twist,
  with the prescribed root-projection normalization and tensor powers.
- `kummerTraceOrdinaryDatum` is literally the existing `projectiveLineTraceDatum`
  at l^(r+1), with its unit, normalized positive Chern class and decomposition.
  Its `decomposition.inv ≫ biprod.snd` is definitionally the recorded ordinary
  `projectiveLineTrace`. This helper only supplies the required IsUnit proof.
- The first conjunct of `P1KummerTraceTransport` is C(h^e) followed by the
  specified `directImage` mate equals `projectiveH`. Its source C(A_S) is the
  existing `unit` coordinate. `projectiveH` is the existing adjunct of the
  supported Cartier composite, not a comparison-defined replacement class.
- The second conjunct is C(b^e) then the mate equals `projectiveSum ≫ projectiveB`.
  `projectiveSum` is the specified biproduct comparison induced by the projections.
  This is precisely the node's decomposition equation with its source comparison.
- The third conjunct is `IsIso (projectiveB ...)`.
- The fourth conjunct is the mate followed by `projectiveTrace` equals C(t^e).
  The fifth is `projectiveH ≫ projectiveTrace = 𝟙 (unit A S)`.
  The existing `projectiveTrace` definition is inverse b followed by pr₂.
- The main theorem's second conjunct quantifies every pair U,T of finite-type
  k-schemes and every open immersion j, with every unbounded etale complex K.
  `kummerTraceEtaleOpenCounit` is the actual recorded derived counit, transported
  only from exact restriction coordinates to left-derived restriction coordinates.
  `kummerTraceOpenComparison` is the composite of the recorded termwise extension
  comparison and the canonical restriction comparison. Its equation states that
  this composite followed by the actual pro-etale counit equals C of the etale
  counit. No boundedness, constructibility, Tor or tensor premise is imposed.
- The final conjunct of `P1KummerTraceTransport` is the affine-chart specialization:
  `kummerTraceAffineComparison ≫ kummerTraceProAffine = C.map kummerTraceEtaleAffine`.
  The first helper is the actual counit mate at j!j*L[2] followed by Rq* of the
  displayed open source comparison. The latter helpers are literally Rq* of the
  actual open counit followed by the respective prescribed projective traces.
  `geoP1PushComparison` is the existing unbounded counit-transpose construction;
  on this bounded-below source it is the same canonical bounded-below mate,
  expressed through the canonical derived-functor compatibility isomorphisms.

Dependency declarations read and used, including their docstrings and signatures:

- `Sheaf.AlgebraicGeometry.ProjectiveLineTrace`: `projectiveLineTraceDatum`,
  `projectiveLineTraceTransport`, `projectiveLineTrace`.
- `Sheaf.Paper.ProEtaleProjectiveLineTrace`: `projectiveB`, `linePlus`,
  `projectiveSum`, `projectiveTrace`; and its imported
  `Sheaf.Paper.SupportedProjectiveChern`: `projectiveChern`, `projectiveH`, `projectiveU`.
- `Sheaf.Paper.FiniteSiteCoordinates`: `comparison`, `unit`, `line`, `directImage`,
  `twistComparison`, `twistDerived`.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`:
  `fixedComparisonDirectImageMatePlus`, its IsIso and counit normalization;
  its ambient construction is the recorded `directImage`.
- `Sheaf.AlgebraicGeometry.GeoP1Cohomology`: `geoP1PushComparison` (explicit
  adjoint transpose of C(epsilon) after the inverse-image comparison).
- `Sheaf.AlgebraicGeometry.OpenProjectionSiteTransport`:
  `openProjectionExtensionComparison`, `openProjectionRestrictionComparison`;
  these own the definitions attached to def-pur-open-site-comparison-arrows.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`:
  `openImmersionLowerShriekComparisonUpperStarIso` and coherence, used by the
  recorded open extension comparison, with the canonical adjunction normalization.
- `Sheaf.Paper.ProEtaleAffineLineCounit`: `openAdjunction`, `infinityCartier`.
  This landed node is added to stmt_deps to name the existing constructions.
- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`.
- Mathlib `LocallyOfFiniteType`, `QuasiCompact`, and
  `isNoetherian_of_locallyOfFiniteType`, with ordinary scheme maps throughout.
- The other original statement dependencies were read in their recorded source:
  `IntrinsicCoefficientTwistsUnrestricted`, `DerivedPullbackTensorHom`,
  `ComparisonDerivedPullbackFixed`, `ProEtaleFiniteModules`,
  `WeilConjectures.AlgebraicGeometry.DerivedCategories`, `CartierKummerMap`,
  and `FiniteTateSiteDescent`. Their objects and canonical comparisons are used
  through the finite-site and supported-Cartier modules; no competing copy is made.

Sources opened: Stacks proetale.tex, lemma-jshriek-comparison (Tag 09AF);
categories.tex, lemma-transformation-between-functors-and-adjoints (Tag 0B65);
current main-20261015 blueprint def-amb-p1-trace.md. The latter defines trace as
second-summand projection; the former fix exactly the counit/mate normalizations.

Edge cases: S empty is allowed and infinityCartier explicitly includes it;
no nonempty or connected binder. P.level=1 corresponds to coordinate level zero.
r=0 corresponds to the prime itself killing A. U empty and identity open j=T
are included. Arbitrarily ramified E and levels not divisible by the ramification
index are included. Nonseparated S remains allowed. The open counit quantifies
all unbounded K; only the projective direct-image instances use bounded-below
inputs (the shifted line and its exact open extension/restriction).

Searches actually run through msearch.py:

- LeanFinder: “Etale proetale comparison preserves projective line Kummer
  decomposition trace and open counit”: eight hits on etale ring presentations,
  etale composition, and IsEtale.of_comp; no matching statement.
- LeanSearch: same plain-language query: eight etale algebra/morphism hits,
  including Algebra.Etale.formallyEtale and Algebra.FormallyEtale.of_equiv; no match.
- Loogle: `CategoryTheory.Adjunction, CategoryTheory.Iso`: twelve generic
  adjunction transport lemmas (ofNatIsoLeft/Right and their unit/counit formulas),
  no geometric statement or canonical Kummer comparison.
- Mathlib grep: `projectiveLineTrace|projectiveLineDecomposition|Kummer.*trace|trace.*Kummer`:
  zero hits.
- rg in lean/WeilConjectures and lean/Sheaf for the item id, projectiveLineTrace,
  projectiveH/B, open counit, and infinityCartier: found the dependencies above
  and VectorIntegrationSiteComparison. That module has only three of the
  projective equations and a generic open counit equation; it lacks the explicit
  Chern transport, IsIso clause and affine-chart composite of this node. It is
  a downstream item, so this module does not import it or duplicate its definitions.
- Node search found def-pur-proetale-affine-line-counit owns infinityCartier and
  openAdjunction; they are reused and that landed node is cited.

No statement correction, new DAG node, dependency repair, or disputed statement.
Compiler verification uses only scompile.py, with every delivered module compiled.

## Second reading by Q35

A separate self-review pass matched the node and module with both files open;
no second agent was started, as the dispatcher explicitly prohibits subagents.
The independent maintainer review remains the delivery reviewer’s task.

This pass found and fixed the coefficient-level mismatch: the theorem now uses
P.level - 1 throughout, so its quotient exponent is exactly the convention’s
P.level rather than an independently quantified level. It also checked that
Noetherianity and prime invertibility are supplied, not assumed; the Chern
component uses the supported class; the sum equation includes projectiveSum;
the trace equations use the actual inverse-decomposition trace; and the open
counit equation ranges over unbounded K, including identity and empty opens.
The affine source comparison includes both the actual direct-image mate and
Rq* of the extension/restriction comparison, in the correct order. All helper
maps were reopened and read as actual compositions. No arbitrary orientation,
map, primitive root, flatness, or separated-base premise remains.

Final validation: the complete statement compiled through scompile.py in both sandbox
and library module modes. The subsequent dry run recompiles the final formatted source.

Compilation repair after interruption: removed the two `backward.isDefEq.respectTransparency` overrides. With the normal transparency discipline the identical signatures and canonical constructions compile in 37.8 and 39.8 seconds on the server, avoiding repeated unfolding of coefficient and category instances. No mathematical statement or data changed.
