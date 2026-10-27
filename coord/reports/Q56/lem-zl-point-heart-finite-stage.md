## Worker report

The delivery states `WeilConjectures.zl_point_heart_finite_stage` in
`Sheaf.Paper.PointHeartFiniteStage`. Its only postponed proof is the theorem itself.
The auxiliary declarations give concrete functors, canonical comparison composites,
and the data and equations quantified by that theorem. None selects an arbitrary
map or chooses data from a mere existence theorem. There are no new DAG nodes and
no dependency-record repairs. The natural-language statement is unchanged.

The fixed hypotheses are `D : FiniteFieldDatum`, `l`, `[Fact l.Prime]`,
`hl : l ≠ D.p`, and `Ω` with its field, Padic algebra and algebraic closure instances.
Thus D supplies the prime power, finite base field and chosen algebraic closure.
The heart-equivalence clauses use the point `Spec (.of D.k)`. The Weil clause
uses the recorded geometric-fibre category over `zlPointHeartBase D`, defined
locally as `Over.mk (𝟙 (Spec (.of D.k₀)))`. The geometric point into that fibre is
exactly `localClosedPoint`, with the closed point and compatible residue-field
embedding as in the landed citer. Prime-invertibility instances are derived,
not extra assumptions. The source and target modules use the common ambient
size parameter of the recorded point-fibre and cohomology APIs.

Clause-by-clause rendering:

- The finite coefficient fields in Ω are `Padic.FiniteCoefficientFields l Ω`.
  The first conjunct asserts `ZlPointHeartExact E.val (zlPointHeartOmega ... E.val)`
  for every such field. `zlPointHeartOmega` is literally the full-heart inclusion,
  `pointRationalFibre`, and `coefficientFdCohomology E 0`.
- The second conjunct asserts the same property for Ω. `zlPointCommonHeartOmega`
  is literally the full common-stage-heart inclusion, `pointQbarFibre`, and the
  recorded `coefficientQbarCohomology ... 0`.
- `ZlPointHeartExact` expresses the exact equivalence onto finite-dimensional
  vector spaces without choosing another abelian instance. It requires Full,
  Faithful, Additive, finite-dimensional values, and essential surjectivity onto
  every finite-dimensional module. This is exactly equivalence with the full
  category of finite-dimensional vector spaces. It further requires preservation
  and reflection of finite limits and colimits (in particular kernels, cokernels
  and the zero object), explicitly reflects zero objects, and states
  `(S.map ω).ShortExact ↔ S.ShortExact` for every ShortComplex. The zero-morphism
  instance in this last quantification is supplied by Additive; it imposes no
  condition on a sheaf or on its Frobenius.
- `ZlPointTruncationComparison` supplies natural upper and lower comparisons in
  all degrees. `le_counit` and `ge_unit` characterize the canonical truncation
  comparisons, precluding a noncanonical splitting. The source t-structures are
  the actual recorded rational and common-stage standard t-structures; the target
  is the usual module derived t-structure. H^0 itself is the recorded kernel/image
  cohomology, so its heart identification uses these canonical comparisons.
- `zlPointHeartScalar` is the specified rational fibre/scalar isomorphism followed
  by `fieldDerivedHomologyIso` in degree zero. Its normalization is the standard
  formula on cycle classes, inherited from the recorded coefficient theorem.
  `ZlPointScalarTruncationSquare` states both scalar/truncation squares with the
  defining upper counit and lower unit equations for all four comparisons.
- The next two conjuncts are the explicit scalar identity and successive-extension
  equations. They use `sfRationalScalarUnit`, `sfRationalScalarComp`,
  `ModuleCat.extendScalarsId`, and `ModuleCat.extendScalarsComp`. The quantification
  over arbitrary finite coefficient field models and algebra maps includes every
  subfield inclusion E⊆L⊆Ω, including identities and repeated fields.
- The final conjunct quantifies an actual fixed pair
  `F : sfCommonStageWeilSheaf D l hl (zlPointHeartBase D) Ω`. This is exactly the
  recorded heart-carrier full subcategory, on `(D.geometricFiber ...).left`, with
  its recorded geometric Frobenius. No continuity predicate appears. It quantifies
  the canonical point data `y`, `ι`, `hι` used by the citer, and applies
  `localClosedPoint D (zlPointHeartBase D) y ι hι`.
- `ZlPointFiniteStageWitness.A` is the finite field E₀. `M` is an actual object of
  `sfWeilSheaf` category on the recorded geometric fibre, using its canonical small
  coefficient model `AlgebraicallyClosedCoefficients.Coefficient`. Its underlying
  complex `M.obj.carrier` is an actual finite-stage heart object by `M.property`;
  `M.obj.str` is its Frobenius isomorphism, including both inverse identities.
- `target_le` retains F's original raw representative and extends it to A.
  `targetTheta` and `u` are actual isomorphisms at A. `intertwining` holds in
  this single finite-stage Hom set. Consequently all inverse equations and the
  intertwining equation hold together at A, not merely in the colimit.
  `target_structure` identifies the descended target Frobenius with F.obj.str using
  the recorded pullback/scalar identification and the canonical `isoToStage`.
- `e` is an isomorphism in the actual fixed-pair category from the included
  `sfWeilStageObject ... A M.obj` to `F.obj`. `e_hom` and `e_inv` identify both
  arrows with the representatives
  u and u.inv at A, so the finite-stage equations genuinely concern e too.
- `fibre` has the claimed Ω-vector-space endpoints. `fibre_normalization` states
  exactly that it is the canonical point pullback followed by H^0 Fib applied to
  e inverse and then `zlPointWeilStageOmega`. Its endpoints are literally the
  `zlPointWeilFiber` and `zlPointFiniteFiber` expressions used by the citer, after
  unfolding the two identity-base abbreviations. The comparison first uses
  `localQbarPullbackStageIso` along the same `localClosedPoint`, then
  `zlPointStageOmega`. It uses the specified object formula of `pointQbarFibre`, the
  canonical Shrink field equivalence, `fieldDerivedHomologyIso`, and the tensor
  tower. The order Ω tensor_E V is the existing coefficient convention, related
  to V tensor_E Ω by the canonical tensor commutor.

Dependency declarations read and used:

- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory`, `Stage`, `inclusion`,
  `stageSystem`, and its literal finite-stage category and Hom calculus.
- `Sheaf.Paper.SfConstructibleHeart`: `sfRationalHeart`,
  `sfCommonStageHeart`, their heart properties and their standard t-structures.
- `Sheaf.Paper.SfWeilSheafComplex`: the fixed-pair convention and its precise
  stage-pullback identification construction. The statement uses its exact
  `sfCommonStageWeilSheaf`, `sfWeilSheaf`, `sfWeilStageObject`,
  `sfWeilFrobeniusPullback`, `sfCommonStageWeilFrobeniusPullback`, and
  `sfWeilStagePullbackIdentification` declarations without replacing the scheme
  or its Frobenius.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointRationalFibre`, `pointQbarFibre`,
  its uniquely specified object/map formulas, `pointRationalFibreScalarIso`.
- `Sheaf.Paper.CoefficientCohomologyModules`: `coefficientFdCohomology`,
  `coefficientQbarCohomology` and their prescribed stagewise tensor formula.
- Added landed statement dependency `def-weil-frobenius-point-transport`:
  `Sheaf.SixFunctors.FrobeniusPointTransport`, `frobeniusPointIso` and
  `frobeniusPointPrimeInvertible`. It supplies the existing actual point
  automorphism and the derived prime-invertibility structure.
- Added landed statement dependency `lem-weil-scalar-extension-composition`:
  `Sheaf.Paper.SfScalarExtensionComposition`, `sfRationalScalarUnit` and
  `sfRationalScalarComp`, the normalized comparisons used by the signature.

- Added landed statement dependency `def-weil-local-frobenius-trace`:
  `Sheaf.Paper.LocalFrobeniusTrace`, `localClosedPoint`, `localPointComplex`,
  `localQbarPullbackStageIso`; these supply the existing canonical geometric point,
  finite point complex, and the literal pullback-stage comparison.

The module imports every recorded proof module, and the Mathlib matches for
localization exactness, exact-functor cohomology, the standard t-structure,
derived single full faithfulness, abelian-group direct limits and tensor extension.
The theorem docstring contains all ten steps of the node's proof: finite t-exact
realization, reflection, heart restriction, scalar compatibility, finite heart
models, the finite-matrix Hom argument, exactness, transport of Frobenius,
simultaneous finite-stage equality witnesses, and the normalized fibre identification.

Edge cases checked before writing: zero objects and zero-dimensional vector spaces;
E=Q_l; identity coefficient inclusions; E=L or L=N in a scalar tower; a raw common-stage
representative which was not initially in the finite heart; nontrivial Jordan blocks;
and a Frobenius eigenvalue with arbitrary l-adic valuation. No semisimplicity,
diagonalizability, continuous Z-action, or continuous profinite action is assumed.
The original representative is retained in the common-stage witness even when its
heart membership is only witnessed after a further extension.

Searches:

- `msearch.py leanfinder`: “The constructible heart at a geometric point is equivalent
  to finite dimensional vector spaces and every algebraic closure coefficient Weil
  sheaf descends with its Frobenius to a finite extension”. Eight hits (scheme fibres,
  Artinian schemes, Witt isocrystals, residue fields); none states this lemma.
- `msearch.py loogle`: `Functor.IsEquivalence, PreservesFiniteLimits,
  ReflectsFiniteLimits`. Service returned no hits and reported the unqualified
  Functor.IsEquivalence identifier unknown. Direct source inspection supplied the APIs.
- `msearch.py grep`: `heart.*equiv|equiv.*heart|finite.*stage.*Weil`. No Mathlib hits.
- `rg` in WeilConjectures and Sheaf: point/heart combinations and this node id.
  No existing declaration states this node. `PointWeilHeartFlag` overlaps the proof
  but its theorem asserts a flag and mixedness, not this equivalence/coherence
  statement. `PointRealizationStandardCohomology` is recorded on a related node;
  both its local file and the current server source were unavailable, so it is
  not used or duplicated. The present node's own listed proof route suffices.
- Read the current `literature/blueprint/latest` paragraph 7, which uses the
  dimension-zero invertible Frobenius Jordan filtration, and the node's detailed
  ten-step expansion of the exact point-heart and finite-coefficient input.

No mathematical statement fault or statement correction was found.


## Repair of returned delivery

The return at immutable head `49c85b853c6d` identified H3+H4 (F1): the final
conjunct had privately specialized Frobenius to `Spec k` instead of accepting
objects of the dependency's recorded Weil category. Applied correction (a).
Removed `zlPointFrobenius`, `zlPointCommonFrobenius`, and `zlPointStagePullback`.
The point base is defined in this module as `zlPointHeartBase`; there is no import
of `PointWeilHeartFlag` and hence no dependency on the downstream flag theorem.

The final conjunct now accepts the exact `sfCommonStageWeilSheaf` category.
The witness contains an actual finite `sfWeilSheaf` and the recorded
`sfWeilStageObject ... M.obj ≅ F.obj`. Its single-stage target structure uses
`sfWeilStagePullbackIdentification`, with no new Frobenius functor. The witness
retains the original raw target representative and both arrows of `e`, so the
previously accepted simultaneous inverse/intertwining conditions remain intact.

Its fibre uses `commonStageDerivedPullback` along `localClosedPoint`, followed by
the specified point-fibre functor and degree-zero cohomology. The normalized scalar
comparison first uses the recorded `localQbarPullbackStageIso` and then the previously
accepted point scalar comparison. This is the same geometric point and the same
finite and common-stage fibre as in `lem-zl-point-weil-heart-flag`, not an
unrecorded equivalence between two Frobenius categories.

The dependency declarations were read in the live read clone, including their full
types and docstrings. `rg` found the existing `localPointComplex`,
`localClosedPoint`, and `localQbarPullbackStageIso` in `LocalFrobeniusTrace`;
no new notion or dependency module was necessary. The current main node has no
Lean record for this returned item, so this is a replacement of the returned
packet, not a competing redeclaration in the live library. The module and node
record were compared with the retained returned packet: only the Weil interface,
its concrete fibre normalization, the corresponding declaration list, and the
additional landed statement dependency changed. The natural-language node
statement and its proof remain unchanged.

The advisory about the stage-change cohomology conjunct is acknowledged: this is
an instance of the landed `coefficientQbarCohomology_changeStage`, retained as the
node's explicit compatibility clause. The returned acceptance of the existing
finite/closure truncation clauses and scalar squares is retained; this repair
changes the Weil-category interface requested by H3+H4.


Validation: the revised module compiled through `scompile.py` in both sandbox and
library modes without errors or warnings. A temporary, subsequently removed probe
imported this module and `PointWeilHeartFlag`. Its first example applied the final
conjunct directly to `F : sfCommonStageWeilSheaf ... (zlPointBase D) Ω` with the
citer's `y`, `ι`, `hι`. Its second example used the witness fibre as an isomorphism
between the exact `zlPointWeilFiber` and `zlPointFiniteFiber` expressions, by
unfolding only the fibre functors, identity-base abbreviations, functor composition,
and the inherited full-subcategory inclusion. Both compiled successfully. Thus the
consumer check establishes compatibility of both the objects and their fibres.
The owning module does not import the downstream citer.

## Second reading by Q56

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
