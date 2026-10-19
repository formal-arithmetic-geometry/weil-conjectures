## Worker report

This repairs returned immutable head `7011555fad75`. The prescribed initial dry run
of the saved packet passed at `bae3b15782`; no unchanged packet was pushed. The
reviewer's ownership, citation, TeX, import and independent-reading corrections are
applied below. The retained mathematical formulas and the item's DAG statement are
unchanged. Four modules remain, each owned by exactly one delivered node.

The theorem now concludes `BoundaryQFiniteConclusion`, which unfolds to the conjunction
of `BoundaryQCompatibility` and `BoundaryDualityCompatibility` on the actual finite
coefficient ring and etale/pro-etale derived categories. All helper definitions have real
data; there are no new axioms or arbitrary maps replacing canonical constructions.

Hypotheses and clauses, read against the unchanged DAG statement:

- The global finite-field datum is `D : WeilConjectures.FiniteFieldDatum`; the prime and
  characteristic exclusion are `[Fact l.Prime]` and `hl : l ≠ D.p`. The field extension
  is `E`, `[Field E]`, `[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]`.
  The positive level is exactly `n` with `hn : 1 ≤ n`, including level one. The ring is
  `Padic.coefficientExtensionRing l E n`, not an arbitrary coefficient ring. Its finite
  instance is supplied by `Padic.finite_coefficientExtensionRing ... hn`.
- `i : Z ⟶ T`, the two `Over (Spec D.k)` instances, the two triples
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`, `i.IsOver`, and
  `IsClosedImmersion i` render every geometric condition. Compactness of T is derived
  from its finite-type structure morphism inside the conclusion definition; it is not
  an added hypothesis.
- The coefficient category is `ModuleCat.{u+1} (ULift.{u+1,u} A)`. The generalized
  coefficient interface accepts the lifted scalar ring once at the module-value universe;
  it neither changes site sizes nor adds an equality of universes. The site categories are literally
  `DerivedCategory (Sheaf X.smallEtaleTopology (coefficients A))` and
  `DerivedCategory (Sheaf (Scheme.ProEt.topology X) (coefficients A))`.
  `comparison` is the recorded exact termwise derived comparison inverse image.
  This does not force four abstract categories into a common independently chosen
  object/morphism universe.
- `PT` and `PZ` in the conclusion are exactly
  `WeilConjectures.finiteTorConstructibleEtale l E n hn T/Z`: bounded constructibility
  and the fixed finite interval for tensor with every degree-zero module sheaf.
  M,N are represented in `DerivedCategory.Plus` and required to satisfy this predicate;
  this represents all bounded finite-Tor objects. The separate condition on G_e N is
  the recorded `Etale.DerivedCategory.isBoundedConstructible` at Z.
- `etaleImage`, `etaleExceptional`, `exceptionalAdjunction`, `proetaleImage`, and
  `proetaleExceptional` use the equivalent coefficient-universe interface supplied in
  `BoundaryQMaps` (the relocation requested in the return). They use
  `Compactification.ofIsProper i`, hence the identity-open compactification and the normalized identification of proper compact support with
  ordinary direct image. No ambient pro-etale exceptional adjunction is assumed.
- The hypotheses are literally `CounitComparison A i N`,
  `ProjectionComparison (coefficients A) i ((etaleExceptional A i).obj N.obj) M.obj`,
  and `IsIso` for the two named projection components, etale at G_e N and pro-etale at
  G_p C_T N and C_T M. `rawHomTransport` is the same recorded four-part Hom chain with
  the ambient objects exposed; its construction asserts no unbounded bijectivity.
  `rawOriginMap` is the comparison-unit map on G_e N, extending `exceptionalOriginMap`.
- `EtaleSignedSymmetry` and `ProSignedSymmetry` are normalized presentations of the
  actual signed braiding: their `hom_eq` fields prescribe EVERY component by `HEq`
  to `DerivedMonoidal.braiding`. They are not free swap maps. The q assertion quantifies
  over these normalized presentations, all of which give the same component arrows.
  The duality assertion also quantifies over these normalized presentations. Its
  evaluation maps are extracted from the recorded `AmbientDualityPairing` witnesses;
  their symmetry is the same canonical Koszul braiding by that predicate's normalization.
  No extraction between two concrete presentations of the monoidal structure is needed.
- `etaleQForAdjunction` is the exceptional transpose of F_e(signed symmetry),
  `inv (etaleProjection ...)`, signed symmetry, and tensor with the actual
  `adj.counit.app N`. The projection is the recorded
  `Etale.rightDerivedLowerStarProjectionMap`, not a free morphism.
  `proT` is exactly the same composite using
  `ProEtale.rightDerivedLowerStarProjectionMap` and the normalized exceptional counit.
  `proCounit` is F_p of theta_N inverse followed by the origin counit extracted from
  `CounitComparison`. That counit is determined by its displayed formula using the
  inverse of the canonical direct-image mate, not chosen from a bare existence claim.
- `qSourceIso` is the actual tensor comparison followed by the inverse pullback-square
  comparison in the first factor. `proQInComparisonCoordinates` applies F_p to this
  source map followed by `1 tensor exceptionalOriginMap N`, composes with `proT` and
  the inverse tensor comparison at the target, and takes the actual restricted
  transpose through the Hom chain. By naturality of that transpose it is precisely
  `sourceComparison ≫ (1 tensor theta_N) ≫ q_p ≫ G_p(tensorComparison.inv)`.
  Thus `BoundaryQCompatibility` states C_Z(q_e) followed by theta_(M tensor N) equals
  that arrow. In particular theta_N is retained rather than dropped.
- The etale dualizing objects in the finite conclusion are
  `finiteDualityEtaleObject A (NagataCompactification (X ↘ Spec D.k))`, for T and Z.
  The pro-etale dualizing objects and w_T,w_Z are supplied as in the node. The
  dualizing compatibility is the explicit equation
  `C_Z.map de.hom ≫ wZ.hom = rawOriginMap ... ωT ≫ G_p.map wT.hom ≫ dp.hom`.
- `IsEvaluationComparison` fixes chi by the already recorded
  `siteComparisonEvaluationHom` followed by internal Hom of w. Chi is not an
  arbitrary isomorphism. `PairingTransposeEquality` is equality of the two actual
  tensor-Hom adjunction transposes, with the real monoidal comparison included.
  Its general clause applies to every pairing on the stipulated class and hence to
  finite composites of q, evaluation and symmetry once their comparison squares
  are composed. `FiniteDualityCompatibility` also retains evaluation and its
  double-dual transpose from the recorded duality interface.
- `etaleBoundaryPairing` is the displayed signed symmetry, q, exceptional image of
  evaluation (with the required order swap), then de. Its pro-etale counterpart is
  `proBoundaryPairingCoordinates`: the same formula, using the pro q, chi_T, the
  pro-etale evaluation from `hTp`, and dp. The final clause explicitly asserts
  `PairingTransposeEquality` for these formulas with chi_Z. K and its dual are
  bounded-below representatives K,N with `e : N.obj ≅ RHom(K,ωT)`; all K,N,
  pullback K, G_e N and the indicated duals satisfy the actual PT/PZ predicates.
  Isomorphic representatives add no restriction. This includes the identity case.

The theorem docstring gives the four proof steps: invert the projection square and use
counit/symmetry comparison; transpose using the actual adjunction mate; transport
evaluation and arbitrary finite composites; specialize to the displayed boundary pairing.
Its proof remains `sorry`, as required at stage 2. No statement correction is made.

Dependency declarations used, with their owning modules:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`;
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and the recorded coefficient constructions.
- Mathlib scheme morphism modules: `LocallyOfFiniteType`, `QuasiCompact`,
  `IsSeparated`, `IsProper`, `IsClosedImmersion`; the recorded derived category,
  bounded-below subcategory and sheaf categories.
- `Sheaf.Paper.FiniteTorAmplitudeSites`:
  `WeilConjectures.finiteTorConstructibleEtale`;
  `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible`.
- `Sheaf.Paper.BoundaryExceptionalComparisonData`: `comparison`, `etaleImage`,
  `proetaleImage`, `directImageMate`, `pullbackSquare`.
  `Sheaf.Paper.BoundaryQMaps`: `coefficients`, `etaleExceptional`,
  `proetaleExceptional`, `exceptionalAdjunction`, `homTransport`,
  `exceptionalOriginMap`, `CounitComparison`, `rawHomTransport`, `rawOriginMap`,
  `proCounit`. These are the equivalent module-value-universe presentation of the
  recorded exceptional formulas, as requested explicitly by the reviewer.
- `Sheaf.Paper.BoundaryProEtaleProjectionComparison`: `tensorComparison`,
  `etaleProjection`, `ProjectionComparison`; its imported fixed pullback square and
  the etale/pro-etale `rightDerivedLowerStarProjectionMap` declarations.
- `WeilConjectures.SixFunctors.Etale.Derived.Hom` and the pro-etale counterpart:
  `derivedTensorHomAdjunction`, `derivedHom`; these are the fixed-module presentation
  of the recorded ordinary uncompleted internal Hom.
- `Sheaf.Paper.DualityPairing`: both `AmbientDualityPairing` predicates;
  `Sheaf.AlgebraicGeometry.EvaluationHomSiteComparison`: `siteComparisonEvaluationHom`;
  `Sheaf.SixFunctors.FiniteDualitySiteComparison`: `finiteDualityEtaleObject` and
  `FiniteDualityCompatibility`.

Edge cases: n=1 is included; n=0 remains excluded exactly by hn. The characteristic
exclusion is retained. Empty Z/T and zero complexes are not excluded; no Nonempty scheme
or nonzero-object assumption occurs. The identity immersion is admitted. Each finite-Tor
interval is quantified as in the recorded predicate, without an amplitude bound added
by the worker. The site sizes remain those of the actual module/sheaf categories.

Searches: msearch LeanFinder for the exceptional tensor comparison and its transpose
returned Cartesian expComparison results and rigid tensor-Hom equivalences, not this
statement; Loogle for `Adjunction.homEquiv, BraidedCategory.braiding` returned zero hits.
LeanSearch for canonical exceptional q and tensor-Hom transport returned elementary module
contraction and rigid-category lemmas, not the site comparison. Grep of Mathlib,
slopmaster2 and the published Sheaf sources found the existing projection maps and
ordinary exceptional tensor map (different tensor order), which were reused, but no
exact combined assertion. `blueprint_refs.py search "q comparison"` returned no blueprint
node. Exact `BoundaryQCompatibility`/`PairingTransposeEquality` searches found no published
declaration. Each helper node records these searches and its source. The upstream
TensorStructure and DerivedCategoryBraided docstrings explain the concrete-module
monoidal-instance comparison cost; the repair retains normalized data instead of
making sfFiniteExceptionalFixed irreducible or raising the compiler limit.

## New nodes

`def-weil-boundary-q-foundation` owns `BoundaryQFoundation`: the normalized signed
symmetries, canonical etale q, identical pro-etale t, and the source comparison. It
assembles the recorded braiding, projection transformations and pullback comparison.
There is no second tensor product or new projection map. The searches above find the
components but no declaration in this tensor order with these site interfaces.

`def-weil-boundary-q-maps` owns `BoundaryQMaps`: the module-value-universe coefficient
and exceptional interfaces, the Hom/unit maps, uniquely normalized restricted counit,
comparison-coordinate pro q, and q equality predicate. All eleven relocated declarations
carry this node's blueprint tag and appear in its `lean.declarations`. It cites
the foundation and published exceptional/projection data, not the consumer item.

`def-weil-boundary-q-pairing-transport` owns `BoundaryQTransport`: evaluation-normalized
Hom comparison, equality of transposes, the two explicit boundary pairings and their
duality assertion. It cites maps and the published duality/evaluation interfaces.
All three follow the item's source proof paragraph. Their edges are foundation -> maps
-> transport -> item in import order, with no helper pointing back to the item.

## Returned-delivery repairs

- H1/H2: followed the reviewer's relocation option. Moved `coefficients`,
  `etaleExceptional`, `exceptionalAdjunction`, `proetaleExceptional`, `homTransport`,
  `exceptionalPlus`, `exceptionalOriginMap`, `CounitComparison`, `rawHomTransport`,
  `rawOriginMap` and `proCounit` into `BoundaryQMaps`. Retagged their docstrings and
  added all eleven names to `def-weil-boundary-q-maps.lean.declarations`. Deleted
  `BoundaryQExceptionalComparisonData.lean`, its foundation import and the undelivered
  dependency-node repair. Each remaining module has exactly one owning node.
- H11: replaced the original author's self-check with the independent reading below,
  performed by this newly dispatched N7 repair worker on the retained packet.
- H12: the foundation node now cites
  `lem-weil-boundary-proetale-projection-comparison` in its TeX statement and
  `stmt_deps`, covering both `tensorComparison` and `etaleProjection`. All three new
  node statements now introduce their objects in TeX, with typed arrows and formulas;
  none uses Lean identifiers as its mathematical definition. Their source records
  now name the current `main-20261015` proof paragraph.
- H9: removed all six redundant direct proof imports from the item module. The
  lower-star projection, comparison pullback, duality pairing, finite-duality,
  generalized tensor pullback and pullback-coherence modules are already reached
  through `BoundaryQTransport` and its dependencies. Removed the redundant
  `DualityPairing` import from maps as well. The item has one public import.

## Second reading by N7

Reader: the N7 repair worker in this new dispatcher session, separate from the worker
who authored the retained packet and its former self-check. I read the unchanged item
node, all four retained Lean modules, all three helper-node records and the published
exceptional/projection and duality interfaces. The reading precedes delivery and is
not an assertion that the maintainer will read it later. No additional agent was started.

Sources read: `main-20261015`,
`sec-smooth-purity/sk-lem-sp-tower/cor-weil-boundary-duality-discharge.proof.md`,
final paragraph (tensor-Hom adjunction and evaluation); the comparison paragraph of
`sec-six-functors/sk-thm-sf-pf-proetale/thm-sf-pf-proetale.proof.md`; and the final
paragraph of `sec-smooth-purity/sk-lem-sp-tower/lem-weil-finite-duality-site-comparison.proof.md`.
I also read `BoundaryExceptionalComparisonData` through its Hom/unit/counit definitions,
`BoundaryProEtaleProjectionComparison` through its canonical projection square and
conditional inverse square, both `AmbientDualityPairing` predicates, and
`finiteDualityEtaleObject` and `FiniteDualityCompatibility` in the published modules.

Hypotheses checked against the item:

- The global datum is `FiniteFieldDatum.{u}`. Prime ell, ell different from p, the
  finite extension of `Padic l`, and positive n are exactly the theorem binders.
  `BoundaryQFiniteConclusion` uses the recorded finite quotient ring with its existing
  positive-level finiteness theorem, rather than a freely chosen coefficient ring.
- Both schemes have `Over (Spec (.of D.k))`; each structure morphism has the three
  finite-type/quasi-compact/separated instances. `i.IsOver` and `IsClosedImmersion i`
  express the stated closed immersion over k. Compactness of T is derived inside the
  conclusion from quasi-compactness, so it is not an additional hypothesis.
- `coefficients (ULift A)` is literally the established `ModuleCat.{u+1} (ULift A)`.
  The two sheaf categories use the actual small sites. The module-value-universe
  presentation does not identify site object and morphism universes. The relocated
  exceptional definitions expand to the same identity-open normalized etale adjunction
  and the same `R nu_*`, etale exceptional, comparison composition.
- `finiteTorConstructibleEtale` fixes PT/PZ. Maps quantifies over bounded-below M,N
  satisfying PT and separately asks that G_e N be bounded constructible. The two
  hypotheses `CounitComparison` and `ProjectionComparison` use the canonical mate,
  unit and counits. The exact projection components each have their own `IsIso`
  hypothesis; no invertibility is asserted without its hypothesis.

Conclusions and helper statements checked:

- Foundation defines q by transposing F of signed symmetry, the inverse projection,
  signed symmetry, and tensor of the exceptional counit, in that order. `proT` has
  the identical order. Every symmetry component is fixed by `hom_eq` to the descended
  Koszul braiding. `qSourceIso` uses the actual monoidal comparison and inverse
  pullback-square comparison in the first factor. Its new TeX statement displays
  these same arrows, and the added projection citation owns its two named components.
- Maps constructs `proCounit` by F_p of theta_N inverse and the origin counit fixed
  by the canonical mate formula. `assembleProQ` applies F_p to the source comparison
  and 1 tensor theta_N, then the pro t, then inverse target monoidal comparison,
  and applies the actual Hom transport. `comparedEtaleQ` is C_Z(q_e) followed by
  theta at the tensor target. Thus `BoundaryQCompatibility` keeps both theta_N and
  theta_(M tensor N); its TeX definition records precisely that equation. The generic
  assembly parameters are supplied by the actual canonical families in every consumer.
- Transport fixes chi by `IsEvaluationComparison`, exactly the evaluation-defined
  Hom map followed by internal Hom of w. `PairingTransposeEquality` compares the
  actual adjunction transposes using the inverse monoidal source comparison.
  `BoundaryDualityForFunctors` includes the dualizing compatibility square
  C_Z(de);wZ = theta;G_p(wT);dp. Its first two clauses give general pairing transport
  and evaluation/double-dual compatibility on PZ. The explicit boundary clause uses
  signed symmetry, q, G of evaluation after the specified dual representative, and d.
  The source swaps on both sides place inverse-image K first for the tensor-Hom
  adjunction; they are canonical isomorphisms, so this is exactly the displayed pairing's
  transpose in that order, not a different pairing.
- I counted all seven displayed finite-Tor conditions: K, N representing D_T K,
  i_e^*K, G_e N, D_T N, D_Z i_e^*K and D_Z G_e N. The pro counterpart uses chi_T,
  pro evaluation and dp. It is compared under evaluation-normalized chi_Z. The
  retained theorem therefore covers the specific boundary pairing as well as the
  general transpose and double-dual clauses.
- Every helper is a definition with real data or a property; its new TeX node states
  that definition, not an unproved theorem. The imported exceptional and projection
  notions are reused. The relocated universe presentation and the generic assembly
  helpers leave the canonical formulas unchanged. The only postponed theorem is
  `boundary_proetale_q_compatibility`, with its four-step proof docstring.

Edge cases read through the binders: n=1 is included and n=0 is excluded exactly as
in the source; the identity closed immersion, empty schemes, and zero complexes are
allowed. No nonempty scheme, nonzero object, fixed Tor amplitude or ambient pro-etale
exceptional adjunction is assumed. The helper dependency edges are foundation, maps,
transport, item in that order; no helper depends on the item.

Mismatches found in this independent reading were the returned ownership/blueprint-tag
mismatch, missing foundation projection citation, helper statements written in plain
text with Lean names, and redundant item imports. These are repaired as listed above.
I found no further hypothesis or conclusion mismatch in the retained mathematical
formulas, and made no mathematical statement correction.

## Validation

The required initial dry run passed at `bae3b15782` before repairs. Final compilation,
preflight and delivery results for the repaired four-module packet are recorded below.

Final `scompile.py` sequential four-file pass: clean, with no errors or warnings.
Library-file times: foundation 12.0 s, maps 5.0 s, transport 6.0 s, item 3.8 s.
The private overlay and sandbox passes were also clean; no timeout limit was changed.
The sandbox ownership/declaration/signature/tag/citation audit passed. Exactly one
`sorry` remains, the stage-2 theorem proof. Final `deliver2.py --no-push` passed preflight and all file compiles at
`d6da2f5183`, staging precisely the report, four node files and four Lean modules.
