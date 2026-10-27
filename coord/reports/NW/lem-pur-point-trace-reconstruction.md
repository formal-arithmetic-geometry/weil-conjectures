## Worker report

Module: `Sheaf.Paper.PointTraceReconstruction`; theorem:
`WeilConjectures.PointTraceReconstruction.pointTraceReconstruction`.
The only postponed proof is this theorem, with the node's six-step proof in its
source docstring. All eight helper definitions have real data. They name the
node's hypotheses or composites, rather than replacing any dependency notion.
No assertion of smoothness, invertibility of t, or existence of a normalized
class is made. The node statement, proof and proof dependencies are unchanged.

Hypothesis correspondence:

- The base is `D : FiniteFieldDatum`; its `k` is the fixed algebraic closure of
  the finite field and `D.p` its characteristic. `l`, `[Fact l.Prime]`, and
  `hl : l ≠ D.p` express the coefficient prime assumptions. `E` is a field
  finite dimensional over `Padic l`; `Ω` has the stated `IsAlgClosure` instance.
  These are the fields used by the published `FieldStage` interface. The
  valuation ring, uniformizer, and positive quotient levels are the existing
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, and
  `coefficientExtensionRing`. Natural index n denotes exponent n+1. We use the
  unbundled fields of the purity conventions, since the item uses the entire
  tower, rather than one `PurityFiniteSetting.level`.
- `[X.Over (Spec (.of D.k))]` specifies a; `IsSeparated`,
  `LocallyOfFiniteType`, and `QuasiCompact` on that same structural morphism
  express separated finite type. `c : Compactification a` is fixed throughout.
- `S : ConstructibleExceptionalCoefficients.System ...` is the specified
  constructible exceptional adjunction package, including the actual integral,
  rational and algebraically closed operations, scalar comparisons and counits.
  The positive finite operations are `FiniteExceptional.adjunction ... c n`.
- `SX`, `SZ`, `Ss` are the recorded reduction/limit calculi, and `r` is the
  recorded `FiniteAdjunctionDiagram.Realization`, with actual whole-system
  adjunction and its evaluation/counit equations. No unrelated functor or
  arbitrary right adjoint is substituted.
- `M` belongs to `FiniteAdjunctionDiagram.domain`, which includes normalization
  and finite-Tor constructibility of every level. `hM : UniformLevels ... M`
  explicitly supplies one ordered cohomological interval, one ordered Tor
  interval, and a single positive finite `Scheme.Stratification` on which all
  cohomology sheaves of all levels are locally constant. The predicate uses the
  actual evaluation, support, Tor-amplitude, homology, and canonical coefficient
  pullback declarations. Finiteness of the stalks is already part of domain
  membership, so it is not weakened to mere local constancy. All intermediate
  objects are in this constructible finite-Tor domain because r.F and r.G have
  this full subcategory as their domain and codomain.
- `N` is literally the recorded `FiniteAdjunctionDiagram.normalizedUnit`;
  `t : M ⟶ r.G.obj N` is one actual derived-system morphism, not a family of
  unrelated finite arrows. Its normalization proof uses the theorem-owned
  `coefficientUnit_mem`, so the realization theorem is a statement dependency.
- `MI` and `GI` are literally the derived limits of M and G N; their membership
  proofs `hMI`, `hGI` express the stipulated intermediate constructible finite-Tor
  domain. `UI` is literally `integralConstantCoefficientObject`, with the same
  domain membership `hUI`. There are no arbitrary presentations m or unit:
  the internal `m` is the identity isomorphism.
- `support : FiniteAdjunctionDiagram.IntegralSupport r` supplies the canonical
  compact-support comparison, with its specified finite projections. The helper
  `supportComparison` first uses the actual reconstruction counit at M (its
  invertibility is `purNormalizedReconstruction`), then `support.iso.app`, then
  the inverse of `S.ring.integralLeft`. Thus p and pG are fixed components of
  this construction at M and G N. No arbitrary support isomorphism is an input.
- `unitReduction : CompletedUnitPullback.Reduction ... Ss` specifies the unit
  identification with its actual reduction maps. Its `augmentation_eq` pins the
  augmentation to the reconstruction unit and whole-system comparison; its
  `finite_sections` and `reduction` fields pin the finite maps. The internal u
  is exactly `unitReduction.augmentation.symm`. There is no free u, unit or eN.
- The internal g is `A.adjunction.homEquiv` applied to
  `pG.inv ≫ L(ε_N) ≫ u.hom`, the adjunction conjugate of these fixed
  comparisons. The internal pg is `pG.hom ≫ (A.F.map g).hom`. Neither g nor pg
  is a free isomorphism. Invertibility of g, preservation of the counit, and
  naturality on F(t) are conclusions; hnatural and hcounit are removed.
- `pointUnit` is the stipulated coefficient-unit comparison in the point target.
  Its inverse is fixed by `pointUnit_normalized` to `pointUnitInclusion`.
  This fixes the isomorphism uniquely: the helper
  maps r to its actual constant section using `pointIntegralSectionMap` and
  the recorded exact-functor/single-complex comparison. Thus the degree-zero
  target is the regular O_E module, with no scalar rescaling. The module-size
  lift is exactly the `ULift` used in `pointIntegralFibre`, and its localization
  is the same Grothendieck-abelian derived category.

Conclusion correspondence, in order of the theorem's conjunctions:

1. `systemPairing r.adjunction t` constructs h_bullet as `r.F.map t` followed
   by the actual system counit. The first clause says its evaluation equals
   the finite counit transpose, with `supportEvaluation` and
   `exceptionalEvaluation` explicitly inserted.
2. The next three conjuncts assert `IsIso g`, the counit preservation equation
   `L(ε_N) ≫ u.hom = pg ≫ ε_UI`, and the naturality equation
   `L(F(t)) ≫ pg = p.hom ≫ P(ti)`. All comparisons are the fixed constructions
   described above; these equations are not premises. The let-bound `hr` is the
   limit of this very composite conjugated by p and u;
   `hi` is the specified integral counit transpose of the realized `ti`.
   `hr = hi.hom` is the actual reconstructed morphism equality.
3. `compactSectionsComparison` is the canonical integral left comparison,
   followed by `sfCompactSupportFiniteIntegralFunctor_obj`, followed by the
   actual point fibre. Its target is literally the ambient object of
   `integralCompactSections ... MI`. The point equality precomposes by its
   inverse and postcomposes by the normalized pointUnit: it is an equality
   of arrows from that RΓ_c to O_E[0], not merely an equality of cohomology
   groups or an existence of some pairing.
4. `TransportEquation ... q MI UI ti` is the rationalization equation with
   the actual recorded q comparison and b comparison. The following equation
   applies the actual `pointRationalFibre` to both sides. In that functor the
   scalar action on arrows is defined by sections and localization, so this
   is the scalar extension of the point-valued pairing, with its source
   comparisons still explicit.
5. The finite-field clause specializes to the rationalized `MQ`, `UQ`, `tq`;
   it does not assert the result for an unrelated arrow. It retains the actual
   `rationalScalar` and its coefficient embedding and applies the actual
   rational point functor at the larger field.
6. The common-stage clause transports this same tq to a finite field inside Ω
   using an explicitly supplied embedding i, then the recorded common-stage
   inclusion and its comparison b. It includes the resulting pointQbarFibre
   morphism equality. For each larger index L, the displayed naturality
   equation of `commonTransition` identifies the extended hf representative
   with the original one. Identity enlargement is included. The finite field
   stage is a finite extension with a specified embedding into the common
   field, exactly as required to represent the initial E inside Ω.
7. The last clause quantifies a supplied whole-system `z` and assumes exactly
   `z ≫ hb = 𝟙 N`. `zi` uses the SAME u and p. Its integral and point-valued
   composites with the pairing are identities. `zq` uses the SAME rational q;
   its rational and point composites are identities. For every common stage,
   `zf`, `zb`, and `hb'` use the SAME scalar/right-adjoint/support comparisons
   as the preceding clauses; their composites, before and after pointQbarFibre,
   are identities. No class is constructed without the supplied z.

`TransportEquation` also spells out functorial preservation of a retraction at
its particular supplied objects. This is precisely the conditional normalization
clause; the main theorem additionally identifies the class coming from z.

Dependencies read and used (names below are in namespace WeilConjectures unless
qualified otherwise):

- `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`, its finite field and
  coefficient conventions, realized by the unbundled D/l/E parameters above.
- `WeilConjectures.Compactification.RefinementCategory`:
  `AlgebraicGeometry.Compactification` and `.Refinement`; the fixed c uses this
  published compactification convention, with no refinement assumed.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` and public Data:
  `ConstructibleExceptionalCoefficients.System`, `.Operation`, `.FieldComparison`,
  `.FieldComparison.q`, `.FieldComparison.b`, `.rationalization`, `.rationalScalar`,
  `.commonInclusion`, `.commonTransition`.
- `Sheaf.Paper.QcqsCompactSupportRealization`: `sfQcqsCompactSupportRealization`,
  retained in `S.ring.integralLeft_normalized`; the source comparison uses the
  same `S.ring.integralLeft`, not a new compact-support operation.
- `Sheaf.Paper.NormalizedDVRTower` and its actual-system calculus dependencies:
  `NormalizedDVRTower`, `IsNormalizedCoefficientSequence`,
  `coefficientSequenceDerivedEvaluation`, `coefficientSequenceLimit`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and its full
  subcategory; `Sheaf.Paper.FiniteTorAmplitudeSites`/`FiniteTorAmplitude`:
  `finiteTorConstructibleIntegral`, `HasProEtaleTorAmplitude`.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointFibreIntegralAmbient`,
  `pointIntegralFibre`, `pointRationalFibre`, `pointQbarFibre`; its public
  completed-coefficient sections interface supplies `pointIntegralSectionMap`.
- `Sheaf.Paper.CommonStageCompactWeilCohomology` / `OrdinaryCompactCohomology`:
  `integralCompactSections`; this is the recorded RΓ_c object, not a copy.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`;
  `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory`, stage inclusions/transitions.
- Already-landed statement interfaces added to stmt_deps:
  `def-coef-derived-system-calculus-data` (`CoefficientDerivedSystemCalculus`),
  `def-coef-finite-adjunction-system-data` (`FiniteAdjunctionDiagram.Realization`),
  `def-weil-compact-support-finite-action`
  (`sfCompactSupportFiniteIntegralFunctor_obj`), and
  `def-weil-constant-coefficient-objects`
  (`integralConstantCoefficientObject`). Their existing modules are used directly.
  The constant-object theorem is not a statement dependency merely because the
  plain definition lives in its module.
- The theorem-owned `FiniteAdjunctionDiagram.normalizedUnit` and its membership
  proof, and `IntegralSupport`, use
  `lem-coef-finite-adjunction-diagram-realization`
  (`Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization`).
- `def-pur-completed-unit-pullback-data`
  (`Sheaf.Paper.CompletedUnitPullbackTower`): `CompletedUnitPullback.Reduction`,
  in particular its pinned `augmentation`; no independent unit comparison is
  introduced. `lem-pur-normalized-reconstruction-adjunction-calculus`
  (`Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus`):
  `purNormalizedReconstruction`, whose actual reconstruction counit determines
  the inverse used in `supportComparison`. Both are statement dependencies.
- The realization, reconstruction-calculus and completed-unit modules are public
  imports because the statement or helper constructions use their declarations.
  Private proof imports retain integral exceptional adjunction,
  `IntegralPointCoefficientAdjunction`, `RationalOperations`, and
  `PointSectionsScalarExtension`, as in the node's proof.
- Mathlib: `CategoryTheory.Adjunction.counit`, `Functor.map`,
  `Functor.mapDerivedCategorySingleFunctor`, `DerivedCategory.singleFunctor`,
  full-subcategory inclusion and `eqToIso`. No second adjunction, coefficient
  ring, stratification, support, Tor-amplitude, or point functor is defined.

Edge cases checked: n=0 means the first positive quotient, not the zero quotient;
X may be empty or disconnected; arbitrary shifts and zero objects fit the uniform
intervals; an empty scheme can have a positive stratification with empty strata;
t may be zero or noninvertible. In the latter cases the last assertion only
applies if its system retraction exists. No properness or smoothness is imposed.
An identity coefficient embedding and F=L are included. No exchange of sections
with an unconstructed inverse limit and no detection of morphism equality from
all finite reductions is used. Every universe is bound explicitly; the small
site and point module size follow the published declarations.

Searches actually run:

- msearch LeanFinder, query "A morphism of normalized quotient coefficient
  systems into exceptional inverse image has counit pairing compatible with
  reconstruction rationalization and common coefficient field transport":
  eight unrelated normalization/Dold--Kan hits; no matching statement.
- msearch Loogle, `CategoryTheory.Adjunction.counit,
  CategoryTheory.Functor.map_comp`: zero hits.
- msearch grep, `counit.*reconstruction|trace.*reconstruction|reconstruction.*counit`:
  zero Mathlib hits.
- msearch LeanSearch, "Coherent coefficient system counit transpose commutes
  with derived inverse limit and scalar extension": eight generic derived
  counit/adjunction hits, no whole-system exceptional reconstruction statement.
- msearch grep, `common.*stratif|uniform.*Tor|normalized.*bound`: 25 unrelated
  uniform-space/valuation hits, no uniform coefficient-system predicate.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, including the node id,
  trace/reconstruction/counit, common stratifications and finite Tor bounds:
  existing component interfaces above, no exact theorem. The upstream adic
  Poincaré/purity reconstruction results assume the smooth purity isomorphism
  and do not state the present arbitrary-system-arrow assertion. The common
  lisse-strata adic-tower statements use a different tower input; UniformLevels
  merely bundles this item's stated hypotheses using the actual system evaluations.

Source opened: current `literature/blueprint/latest/blueprint/sec-smooth-purity/`
`sk-cor-sp-all-coefficients/cor-pur-adic-and-rational-smooth-dualizing-complexes.proof.md`,
the counit/smooth-trace and coefficient compatibility clauses, together with the
node's detailed six-step proof. No statement fault or STATEMENT-DISPUTED finding.

## Repair of independent return f0dc8218d1d6

1. H2: replaced the statement dependency on
   `lem-weil-constant-coefficient-objects-constructible` by its actual definition
   owner `def-weil-constant-coefficient-objects`.
2. H2: added `lem-coef-finite-adjunction-diagram-realization` to stmt_deps for
   its theorem-constructed `normalizedUnit`. The new canonical construction
   also cites the already-landed `def-pur-completed-unit-pullback-data` and
   `lem-pur-normalized-reconstruction-adjunction-calculus` interfaces it uses.
3. H3: removed arbitrary p, pg, g, u, unit and eN parameters and removed the
   hnatural/hcounit premises. Reconstructed objects are literal limits and the
   literal completed unit. `supportComparison` uses `IntegralSupport.iso` and
   `S.ring.integralLeft`, through the actual reconstruction counit. g is the
   adjunction conjugate, pg is pG followed by P(g), and u is the inverse of
   `CompletedUnitPullback.Reduction.augmentation`. Counit preservation,
   naturality and invertibility of g are conclusions alongside the requested
   reconstructed pairing equality. No main-node statement correction is needed.

## Second reading by NW

The delivered section was a self-reading by the author (the dispatcher did not
allow a second agent). The maintainer's independent reader replaced it with this
clause-by-clause reading of head 85996a300b13.

Node statement against the Lean (`pointTraceReconstruction`):

- k, p, ℓ ≠ p, E/Q_ℓ in Ω, O_E, ϖ, A_n, s: `D : FiniteFieldDatum`, `hl : l ≠ D.p`,
  `E` finite over `Padic l`, `Ω` with `IsAlgClosure`. The quotient rings are the
  recorded `Padic.coefficientExtensionRing l E (n+1)`. Verdict: correct.
- a : X → s separated of finite type, and a fixed compactification: the
  `X.Over`, `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` instances on
  `X ↘ Spec k`, and `c : Compactification`. Verdict: correct, and nothing
  stronger is assumed.
- P_n ⊣ G_n, P ⊣ G and their counits: `FiniteExceptional.adjunction … c n`, and
  `A := S.ring.operation c (.integral E)` with its `.adjunction` from the recorded
  `ConstructibleExceptionalCoefficients.System`. Verdict: correct.
- M_• is normalized with ctf levels: `M : (FiniteAdjunctionDiagram.domain l E X).FullSubcategory`.
  Common bounds and stratifications: `UniformLevels`. That predicate uses the
  actual support, Tor-amplitude and local-constancy predicates. `0 < strata.n` is
  harmless, because `Topology.Stratification` allows empty strata. Verdict: correct.
- t_• : M_• → G_•((A_n)_s) is one actual system arrow:
  `t : M ⟶ r.G.obj normalizedUnit`. Verdict: correct.
- Intermediate systems lie in the domain: `hMI`, `hGI`, `hUI`. Verdict: these
  are exactly the node's stipulation.
- M = R lim M_•, and t : M → G(U_s) as the specified realization: `MI` is the
  literal limit. `ti = L(t) ≫ g`, where g is the adjunction transpose of
  `pG⁻¹ ≫ L(ε_N) ≫ u`. Here p and pG are `supportComparison`, built from the
  actual reconstruction counit (invertible by `purNormalizedReconstruction`),
  `IntegralSupport.iso` and `S.ring.integralLeft`. u is
  `Reduction.augmentation.symm`, pinned by `augmentation_eq`. A right comparison
  that preserves counits relative to a fixed left comparison is forced to be this
  mate, so g is pinned. `IsIso g`, counit preservation and naturality are
  conclusions, not hypotheses. Verdict: correct, and this repairs H3 of f0dc.
- h_n and the whole-system h_•: `hb := systemPairing r.adjunction t`, built
  before evaluation. Its first conjunct gives the evaluation at each n, with the
  recorded support and exceptional evaluation isomorphisms. Verdict: correct.
- The derived-limit realization of h_• is h: `hr = hi.hom`, where hr is p⁻¹,
  then L(hb), then u. Verdict: correct; this is the node's main identity.
- Fib_s(h) : RΓ_c(X,M) → O_E: `qi` is the integral left comparison followed by
  `sfCompactSupportFiniteIntegralFunctor_obj` onto `integralCompactSections`.
  `pointUnit` is pinned by `pointUnit_normalized` to the canonical constant-section
  map, and it is invertible by lem-pod-integral-point-coefficient-adjunction, so
  the hypothesis is satisfiable and fixes the isomorphism uniquely. Verdict:
  correct, though this conjunct follows directly from `hr = hi.hom`.
- Rationalization and finite field extension: `TransportEquation` with the
  recorded `rationalizationComparison` and `rationalComparison` (q and b are
  recorded comparisons), plus the `pointRationalFibre` equations. Verdict: correct.
- Common stage and independence of enlargement: `commonComparison`, the
  `pointQbarFibre` equation, and naturality of `commonTransition` for every
  L ≥ F. Verdict: correct. Identity enlargement is included.
- The conditional class c_•: `∀ z, z ≫ hb = 𝟙 N → …`. It uses the same u, p, q,
  d and b, at the integral, point, rational and common-stage levels. No class is
  asserted to exist, and t is not assumed invertible. Verdict: correct.

Edge cases: X empty (with a one-stratum empty stratification), t = 0 (the
z-clause is then vacuous unless N = 0), the identity coefficient embedding and
F = L, and n = 0 meaning A_1. All are covered.

Theorem-node stmt_deps (mechanical finding), judged:

- lem-coef-finite-adjunction-diagram-realization: `normalizedUnit` carries the
  membership proof `coefficientUnit_mem`. That is the content of this theorem
  node: the unit system is normalized with ctf levels. Without it, G_• cannot be
  applied to (A_n)_s at all, so this is a genuine dependency on the theorem
  (precedent: the f0dc return required this citation). The plain declarations
  `IntegralSupport` and `reducedConstructible` live in the same module and add no
  further edge. Moving them to a definition node is advisory.
- lem-pur-normalized-reconstruction-adjunction-calculus: the theorem's
  conclusion (IsIso of the actual reconstruction counit on normalized systems)
  is used to form the iso `e` inside `supportComparison`. This is a genuine
  dependency on the theorem.

One definition per notion: the helpers are a generic transpose, a transport
composite, a predicate bundling the node's hypotheses, the regular O_E[0] and its
canonical inclusion, and two composites of recorded comparisons. None duplicates
a recorded notion. stmt_deps owners: def-weil-constant-coefficient-objects and
def-pur-completed-unit-pullback-data are existing:true owners, which repairs H2 of
f0dc. The statement field is verbatim the file signature. There is exactly one
`sorry` and no proof beyond it. Docstrings carry the source place and the
blueprint tag, and the theorem docstring carries the six proof steps.
