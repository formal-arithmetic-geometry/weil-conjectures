## Worker report

The module `Sheaf.Paper.FiniteProjectionExchangeTransposes` states
`AlgebraicGeometry.ProEtale.FiniteProjectionExchange.finite_projection_exchange_transposes`.
Its proof is `sorry`; its docstring carries all eight DAG proof steps. All helper data
are actual composites of the published operations, never an existence choice or
an arbitrary map. The item JSON changes only `lean`. There are no dependency repairs,
new notions requiring nodes, statement corrections, or disputed statements.

Hypotheses and coefficient conventions:

- `D : FiniteFieldDatum` retains p, the positive exponent, q, the finite field and
  its specified algebraic closure; `C : D.CoefficientDatum` retains prime ell,
  `C.different : C.l ≠ D.p`, and the algebraic closure of the coefficient field.
- `E`, its field and Padic algebra instances, and `FiniteDimensional (Padic C.l) E`
  are the finite extension. `Padic.coefficientExtensionRing C.l E n` is the existing
  quotient of its valuation ring by its chosen uniformizer power. `hn : 1 ≤ n`
  retains every positive exponent. Its finiteness is supplied by the published
  coefficient finiteness theorem, not assumed as an extra hypothesis.
- `_S : SixFunctorOperationDatum D C E n hn` is the specified six-operation datum,
  including its completed, localized and common-stage normalizations. Only the
  finite operation component occurs in this finite-coefficient conclusion. As in
  `SixFunctorOperationDatum.finiteExchangeProjection`, those finite maps are the
  canonical fixed-scalar maps transported through the intrinsic realization;
  their formulas do not depend on additional choices in S.
- `Dcat (ULift (Padic.coefficientExtensionRing ...)) X` is the fixed-module
  presentation of the small pro-etale derived category. The coefficient lift
  matches the small site's object universe u+1 and morphism universe u.
- `X Y Y' : SixFunctorSpace D` retains finite type over k and their structure maps.
  There is no `IsSeparated` instance on those structure maps. The explicit
  `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` instances on f and g say
  exactly that the two k-morphisms are separated and of finite type. The over
  category supplies that they are k-morphisms. The arbitrary `IsPullback` supplies
  X', f', and g', without requiring the pullback to be definitionally a chosen one;
  the other two arrows inherit the stated morphism properties by base change.
- `finiteBC ... K` is precisely intrinsic bounded constructibility after the
  recorded `sfIntrinsicDerivedEquivalence`; `finiteCTF ... L` is the recorded
  `finiteTorConstructible`. K has no finite-Tor hypothesis. These are restrictions
  of the ambient formulas to the node's two input domains.

Clauses and maps:

- For EVERY `c : Compactification f`, `SquareLaw` asserts the displayed equation
  `diamondLeft ... = diamondRight ...`. `pf` is the existing
  `projectionMapOfCompactification` and `ex` is
  `rightDerivedLowerShriekOfCompactificationBaseChangeMap`. `mu` is the existing
  `leftDerivedUpperStarTensorIso`; `target` inserts that canonical tensor
  comparison and the inverse of `leftDerivedUpperStarSquareIso`. Thus these are
  exactly the typed versions of Ex at K tensor f*L after g*PF, and PF after
  Ex at K tensor identity. No isomorphism of PF or Ex is assumed.
- `c.ofIsPullback s` is the actual base-changed compactification. Its proper square
  uses h = `pullback.fst c.g g`; its open square is
  `c.isPullback_i_ofIsPullback s`. Its M is exactly `(ext A c.i).obj K`.
- `openFirst` is H(gamma), beta at K tensor j*P, and J' of the tensor/square
  comparison. `openSecond` is mu_H, beta_K tensor identity, and gamma'.
  `SquareLaw` asserts that their common source and target lie in `J'.essImage`.
  It separately asserts that restricting either route by L j'^* and following
  the inverse canonical open unit equals `openSource`. That source identification
  is built independently from the open unit, mu_j, mu_g', and the open square.
  Consequently both restricted maps are identities in the canonical unit
  coordinates. Here P=p*L; the proper square identifies j'^*h*p*L with f'^*g*L.
- `properFirst` is g*pi, proper exchange at M tensor p*L, then p'_*(d), with
  d = mu_h followed by identity tensor theta inverse. `exchangeFirst` is mu_g,
  proper exchange tensor identity, and pi_p'. For EACH of these actual maps,
  `SquareLaw` applies `(derivedUpperStarLowerStarAdjunction ... p').homEquiv.symm`
  and identifies it with `commonTranspose`. This last composite is
  p'^*(mu_g), mu_p', theta at p_*M tensor identity, then h(epsilon_p,M) tensor
  identity. It is exactly the displayed common transpose, with every canonical
  comparison visible. The comparisons are the published ringed/K-flat ones,
  rather than supplied monoidal structures.
- `RefinementLaw` quantifies over every refinement r between c and d. Its
  `baseRefinement s r` is the literal induced map between the fibre products,
  with its open and proper commutation equations. `rho` is
  `refinementComparisonAtWitness` conjugated by the retained presentation
  isomorphism. For K and for the target g'^*K tensor f'^*g^*L it retains arbitrary
  `EtaleOriginDerivedCategory` witnesses O and OT and their isomorphisms to the
  displayed actual objects. No arbitrary comparison is supplied. BOTH words in
  the equation are intertwined by the same g*(rho_K tensor identity) and target
  rho. This is clause (2), together with the equation for every c: hence it holds
  for the compactification-independent maps represented at any chosen c. Common
  refinement independence and cocycle are the recorded CompactificationCoherence
  dependency, rather than an extra invertibility hypothesis on a projection map.
  Constructible origin supplies these witnessed presentations; no finite-Tor
  assumption on g'^*K is used.
- `IdentityLaw` uses `Compactification.ofIsProper (𝟙 X)`, whose two factors are
  the identities. `identitySupport` is the canonical R id_* and id_! unit
  identification. Its inverse on K tensored with identity, followed by PF and
  its forward identification on the output, then the tensor image of
  `leftDerivedUpperStarId`, equals the actual identity on K tensor L. This is
  exactly clause (3) under the unit identifications.

Dependency declarations read and used:

- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`,
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage` and its
  three composites. The finite maps are the published specializations in
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar`,
  `.LowerStarProjection`, `.LowerShriekProjection`, `.LowerShriekBaseChange`.
  The canonical maps are used directly; no duplicate stage or operation is defined.
- `Sheaf.Paper.SixFunctorOperationDatum`,
  `WeilConjectures.SixFunctorOperationDatum` and `.finiteExchangeProjection`;
  `SixFunctorSpace` from its public stages module.
- `Sheaf.Paper.SmoothPurityCompactProjectionBaseChange`,
  `AlgebraicGeometry.ProEtale.CompactProjectionBaseChange.compact_projection_base_change`;
  its full signature and its Presentation/DiagramAssertion helpers were read.
  This dependency covers the separated case and does not state the extra clauses.
- `Mathlib.CategoryTheory.Adjunction.Mates`, `CategoryTheory.mateEquiv`:
  used through the published proper exchange. The adjunction hom equivalence
  gives the two transpose assertions directly.
- `Sheaf.Paper.FixProjectionCompactificationComparison`,
  `WeilConjectures.FixProjectionCompactification.comparison`, especially its
  `finiteLaw` and the actual refinement comparison. `rho` uses the same
  `refinementComparisonAtWitness` construction from its public dependency.
- `Sheaf.Paper.ExchangeFunctoriality`, `WeilConjectures.exchangeFunctoriality`;
  finite compact identification and finite exchange laws were read.
- `Sheaf.SixFunctors.OpenTensorNormalization`,
  `SheafOfModules.openTensorNormalization`, and its Assertion's beta/gamma
  restriction normalizations; `RingedDerivedMonoidalComparisons`,
  `CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons`.
- All remaining proof-dependency modules are imported: ProEtaleConstructibleOrigin
  (`constructible_proEtale_origin`), PullbackTorAmplitude (`sf_pullback_torAmplitude`),
  FiniteCoefficientTensorCtf (`finiteCoefficient_tensor_ctf`), ExtensionIntegersDvr
  (`Padic.extension_integers_dvr`), PullbackBoundedConstructible
  (`finiteCoefficientBoundedConstructiblePullback_exact_and_interval`), and
  CompactificationCoherence (`compactification_coherence`). Their statements and
  docstrings were read. They justify the precise comparison domains in proof step 6.

Searches (all via prescribed msearch or direct read-only rg):

- LeanFinder: "Compact support projection formula commutes with base change and
  both proper adjunction transposes equal the pulled back counit tensored with identity".
  Eight hits, ordinary adjunction facts; no exact statement.
- Loogle: `CategoryTheory.mateEquiv, CategoryTheory.Adjunction.rightAdjointProjectionMap`.
  Zero hits, latter identifier unknown to its Mathlib-only index; the project
  right-adjoint projection construction was found and reused directly.
- LeanSearch: "The compactly supported projection formula is compatible with
  base change via the same counit transpose". Eight unrelated ordinary
  tensor-product/condensed hits; no exact statement.
- msearch grep: `projection.*base.?change|base.?change.*projection`, CategoryTheory:
  zero Mathlib hits. Direct Mathlib rg gives no exact geometric statement.
- Direct rg of WeilConjectures by node id gives zero hits. Searching its finite
  pro-etale derived modules finds the canonical maps, not all requested assertions.
- Direct rg of Sheaf by the geometric and transpose terms finds
  SmoothPurityCompactProjectionBaseChange and RingedExchangeTensorCoherence.
  The former assumes separated schemes and omits transposes/refinement/identity;
  the latter is a general ringed mate equality, without those geometric clauses.
  Neither can serve as an existing match. Search of dag/lean_names_upstream.json
  yields no matching node declaration. Searches also checked the new full
  namespace and declaration name against the library: no collisions.

Edge cases: n=1 remains allowed; n=0 is correctly excluded by the node. The zero
complexes and empty schemes remain allowed. The statement imposes no finite Tor
condition on K, no flatness/smoothness on g, and no absolute separatedness. It never
inverts PF or proper/compact exchange. The identity compactification uses the
identity unit comparisons, and identity refinements are included in RefinementLaw.
The refinement's open square need not be Cartesian. All universes and variables
are explicitly bound; no file-local notation, private definition, or local instance
is exported. There are no tests or proofs beyond the expected statement `sorry`;
proof fields of the fibre-product refinement use only their canonical equations.

Validation: scompile.py compiled both sandbox and named library module cleanly,
within the default 60-second per-file limits, with no warnings. Dry-run and delivery
results are recorded by the delivery tool.

## Second reading by NK

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
