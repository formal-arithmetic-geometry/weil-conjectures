## Worker report

This delivery states `AlgebraicGeometry.Etale.exists_ordinaryFiniteP1Adjunction`
in `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction`. Its proof is `sorry`;
the complete nine-step DAG proof is in its docstring. The accompanying `OrdinaryFiniteP1Kummer`, `OrdinaryFiniteP1Arrows` and
`OrdinaryFiniteP1Data` modules construct the canonical maps and describe the
normalized data and three base-change squares. No proof of the target is attempted.

Clause-by-clause reading:

- `N : ℕ`, `hN : 0 < N` render N ≥ 1. `A : Type (u + 1)`, `[CommRing A]`,
  `[Finite A]`, `hA : (N : A) = 0` render exactly finite commutative coefficients
  killed by N; neither a field nor flatness over Z/N is assumed.
- The family `d` ranges over every `S : Scheme.{u}` with `[IsNoetherian S]` and
  `hS : IsUnit (N : Γ(S, ⊤))`. Mathlib's `IsNoetherian` extends locally
  Noetherian and quasi-compact, equivalently the finite Noetherian affine cover.
  Invertibility of the global section N is equivalent to stalkwise invertibility.
- `ProjectiveLine S` is the recorded `ProjectiveSpace (ULift (Fin 2)) S`;
  every `ProjectiveLine S ↘ S` is its structural projection.
- `DerivedCategoryModule A T` is the recorded ordinary small-etale module
  derived category, with no boundedness subcategory. The explicit coefficient
  universe matches its `ModuleCat.{u+1} A` encoding.
- `ordinaryFiniteLine` is the degree-zero image of the existing
  `Scheme.finiteEtaleTateLine T N A hA`, not a new twist. Its scalar-extension
  sheafification generators are the existing `finiteEtaleTateOneGenerator`.
  The auxiliary `OrdinaryFiniteTwistTransport` packages the canonical roots
  inclusion and pure-tensor normalizations already in `etaleFiniteTwistPullback`.
- `ordinaryFiniteP1KummerClass` applies the actual `kummerδ₁` to
  `Pic.toCohomologicalPicardGroup (Pic.ofIsInvertible (ProjectiveSpace.twist ... 1))`,
  and then `Sheaf.H.map ordinaryFiniteRootMap`. The root map is constructed from
  the scalar-extension unit and the sheafification unit, sending z to 1 tensor z.
  `ordinaryFiniteClass` interprets a module-derived class by exact forgetting of
  Ext and precomposition with the integral constant generator. `chern_spec`
  requires equality with that actual class; there is no unconstrained map.
  The upstream twist has the stipulated O(1) transition, with its inverse ratio.
- `ordinaryFiniteP1ChernPushforward` is the inverse-image/direct-image adjunct
  of `chern` after the canonical constant-object pullback comparison.
  `ordinaryFiniteP1Unit` is the shifted twisted adjunction unit.
- `OrdinaryFiniteP1Datum.decomposition` has source
  `ordinaryFiniteLine S [2] ⊞ ordinaryFiniteUnit S` and target the specified
  direct image. `decomposition_hom` fixes its hom to `biprod.desc` of exactly
  those two components. It is an isomorphism, rather than a mere cohomological
  equivalence or rank computation.
- `OrdinaryFiniteP1Datum.trace` is by definition `decomposition.inv ≫ biprod.snd`.
  `trace_chern` is exactly h followed by this trace equal to the identity.
- `ordinaryFiniteP1Right` is left-derived (equivalently exact) inverse image,
  followed by the existing derived tensor with the shifted twist on the right.
  `adjunction` asserts `Rq_* ⊣ ordinaryFiniteP1Right` on the entire categories.
- `ordinaryFiniteProjection` is the symmetry-conjugated map of the recorded
  proper projection theorem, with K first. `counit_normalization` uses `OrdinaryFiniteP1CounitNormalization`, whose
  definition asserts π followed by the actual `adjunction.counit.app K` equals tensoring the trace
  followed by the derived right unit constraint. The recorded projection
  theorem makes this π invertible for this proper projection over Noetherian
  schemes, so the equation is equivalent to precisely the node's formula
  ε = π inverse followed by (1 tensor trace) and the unit constraint.
- `OrdinaryFiniteP1BaseChange` asserts three equations for every morphism of
  Noetherian bases: the decomposition square, the trace square, and the actual
  counit square for every unbounded K. The first uses `ordinaryFiniteP1DecompositionSourceMap`, the canonical biproduct
  comparison assembled from the images of its two projections. Each uses
  `ordinaryFiniteP1Exchange`, which is the recorded `exactDerivedBaseChangeMap`
  transported by the exact/left-derived comparison. The final square uses
  `ordinaryFiniteP1RightBaseChange`, constructed from the actual tensor-pullback
  isomorphism and the inverse-image composition square of projective space.
  This fixes actual arrows, rather than merely isomorphism classes.

Dependencies used in statements and definitions:

- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`:
  `ProjectiveLine`, `ProjectiveSpace.map`, `map_over`, `isPullback_map`.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: `Etale.DerivedCategoryModule`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` and its derived modules:
  `upperStar`, `lowerStar`, `derivedUpperStarLowerStarAdjunction`,
  `leftDerivedUpperStarComp`, `singleFunctorCompLeftDerivedUpperStarIso`,
  `leftDerivedUpperStarIsoMapDerivedCategory`, and tensor pullback comparison.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf` (and its imported finite twist):
  `finiteEtaleTateLine`, `finiteEtaleMuModuleObj`, `finiteEtaleMuModulePresheaf`,
  `finiteEtaleTwistScalar`, `finiteEtaleTateOneGenerator`.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`:
  `Scheme.etaleFiniteTwistPullback`, furnishing the normalized transport used
  in the existence proof; the helper record repeats its characterizing equations.
- `Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison`:
  `RawModuleScalarComparison.forget`, with its exactness instances.
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`:
  `rootsOfUnitySheaf`, `kummerδ₁`, `kummerSequence_shortExact`.
- `WeilConjectures.AlgebraicGeometry.Sites.GmPicard`:
  `Pic.toCohomologicalPicardGroup`, with the existing `ProjectiveSpace.twist`.
- `Sheaf.AlgebraicGeometry.ProperProjectionFormula`:
  `isIso_proper_projection_formula_reordered` and its canonical map.
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`:
  `exactDerivedBaseChangeMap`; tensor and tensor-unit declarations from the
  recorded upstream derived tensor modules, including `derivedTensorRightUnitor` and its already packaged
  constant-object form `derivedTensorSingleUnitIso`.

The main module imports every recorded proof-dependency module, directly or
through its public statement dependency. The supported
Kummer node is still unstated and is not needed to type the statement. The
projection-mate exactness dependency is now published and is imported explicitly
as `Sheaf.Paper.ProjectionMateExact`.

Edge cases checked mathematically before writing: the empty scheme; disconnected
and nonreduced Noetherian bases; the zero coefficient ring; N=1 (which forces A
zero); finite A not flat over Z/N (e.g. A=Z/2 with N=4); non-affine bases; arbitrary
unbounded K. All are retained. No coefficient characteristic, field, connectedness,
separatedness of the base, or boundedness assumption was introduced. The global
family d permits comparison between any Noetherian bases and hence, in particular,
between Noetherian S-schemes. Canonical twist transport is characterized by its
normalizations and has no choice of primitive root or orientation.

Searches: `msearch.py` LeanFinder on ordinary finite-coefficient projective-line
duality and then canonical scalar Kummer/projective-line arrows returned unrelated
Picard algebra maps, Hilbert 90 and cotangent-space declarations. Loogle on
`Adjunction, DerivedCategory, ProjectiveLine` and on `"kummer", "DerivedCategory"`
found no match. Mathlib grep on projective trace/adjunction and Kummer Chern/class
found no match. LeanSearch was unavailable with Internal Server Error; this is
recorded, not treated as a successful negative search. Greps of upstream
WeilConjectures, side Sheaf, and the item id found no existing theorem. DAG and
blueprint searches found only the downstream trace definition, the target, and
the different supported Kummer construction, not a normalized-data interface.
The new node records the queries and returned names. The source blueprint pages
thm-amb-p1-adjunction, thm-amb-p1-decomposition and def-amb-p1-trace were read in
the launcher literature checkout.

No source statement correction is proposed. No mathematical statement dispute
was found. The required file-only compilation and dry run are being checked below.

## New nodes

`def-asd-ordinary-finite-p1-kummer-class` owns `OrdinaryFiniteP1Kummer`: the
scalar-root map, its naturality, the integral generator, exact-forgetting
realization of module-derived classes, and the actual scalar Kummer class of
O(1). Its maps are composites of existing scalar extension, sheafification, Ext
and Kummer constructions. No data comes from a postponed existence proof.
The scalar-root section map has a named naturality theorem with its complete
proof plan. Searches find the ingredients but no declaration of this composite
Kummer realization. The recorded projective-space twist is used for O(1).

`def-asd-ordinary-finite-p1-arrows` owns `OrdinaryFiniteP1Arrows`: normalized
twist transports, the shifted unit and Chern adjunct, the ordered projection,
the right-adjoint functor and its canonical base-change comparison. The
`ordinaryFinitePullback`, `ordinaryFinitePushforward` and `ordinaryFiniteTensor`
forwarding definitions use exactly the recorded functors; their purpose is to
elaborate the coefficient instances once. The right-adjoint comparison uses the
upstream tensor-pullback isomorphism followed by the right-tensor functor applied to the two
canonical factor comparisons. The node cites the
Kummer realization node, existing finite twists, tensor, scalar forgetting,
exchange, and projective geometry. Searches above found no declaration of this
combined arrow interface. Its sources are the cited projective-line blueprint
pages and Stacks Kummer sequence. The downstream `def-amb-p1-trace` uses this
theorem to obtain its decomposition; it cannot supply the interface needed to
state the theorem. There is no dependency wait on that downstream node.

`def-asd-ordinary-finite-p1-data` owns `OrdinaryFiniteP1Data`: the normalized
projective-line decomposition/adjunction record, its trace and the three
base-change equations. The main theorem quantifies over these data. Every map
in its equations is fixed by the preceding two definition nodes. Its sources
and searches are the same projective-line decomposition, trace and adjunction
sources; no existing declaration of the combined normalized-data interface was
found. Each module has its own node and a separate compilation boundary.

Current verification searches (2026-10-15 UTC): `msearch.py` LeanFinder query
"Ordinary etale projective line adjunction over finite rings with Kummer normalized
trace and unbounded derived categories" returned eight standard-etale algebra
results, including `StandardEtalePair.instEtaleRing` and
`Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`; none
states this adjunction. Loogle query `"Adjunction", "DerivedCategory"` returned
zero hits. Mathlib grep `projective.*(trace|adjunction)|kummer.*(Chern|class)` in
AlgebraicGeometry returned zero hits. The same named-construction search
`ordinaryFiniteP1|P1KummerClass|finite.*P1.*adjunction` in both upstream
WeilConjectures and the shared Sheaf source returned zero hits. The upstream
item-id search also returned zero hits. `scompile.py --source` confirmed the
item's module is not yet published.

The helper definitions allow N=0 where their ingredients do: ZMod 0 is the
integer coefficient ring, and the roots sheaf is G_m. The existence theorem
retains the required positivity hypothesis. No helper theorem asserts a
rank-one or invertible-twist claim at N=0. The sole auxiliary postponed
theorem `ordinaryFiniteRootGenerator_naturality` matches the section-map
naturality clause of `def-asd-ordinary-finite-p1-kummer-class`; its docstring
gives the composition-of-naturality-squares proof needed to complete it.

The counit determines the adjunction unit uniquely for the fixed functors;
therefore the actual counit base-change square also expresses transport of the
normalized adjunction, including its unit. The Chern-class witness is fixed
by its realization: Hom in D(A) from the constant free rank-one A object
to F[n] is H^n of the underlying sheaf. Exact coefficient forgetting followed
by precomposition with the integral generator is this canonical identification.
Thus `chern_spec` specifies the scalar Kummer arrow rather than allowing an
unrelated derived arrow with a prescribed rank or stalk value.

Current repair of the earlier attempt: the arrows module publicly imports the
recorded finite-twist pullback module. The three functor wrappers reuse the
recorded upstream functors. Shift compatibility is requested on the upstream
inverse-image functor explicitly, rather than relying on instance search to
unfold a forwarding definition. The general twisted-pullback comparison names
the existing tensor-pullback component and applies the right-tensor bifunctor to
the canonical factor comparisons. Its projective-line specialization supplies
only the canonical square comparison and normalized shifted-line comparison.
All these definitions have real data; no existence choice supplies a map.

The earlier attempt's compile logs are retained in the scratchpad for diagnosis.
The current four-file compile and required no-push dry run will be recorded
below when they finish. This worker does not write the independent second reading.

Fresh verification search: LeanFinder query "Ordinary etale projective line
adjunction with finite coefficients and Kummer trace" returned eight unrelated
standard-etale algebra results; Loogle `"Adjunction", "ProjectiveLine"` returned
zero hits; Mathlib grep `ordinaryFiniteP1|P1KummerClass|projective.*adjunction`
in AlgebraicGeometry returned zero hits. The broadened case-insensitive upstream
and side-library search for projective-line adjunction/trace/decomposition found
only downstream proof docstrings citing this item, plus unrelated text. The
server source query also reports that this item's module is unpublished.

Verification of this resumed worker (UTC date from the compilation host): all four
modules compiled separately through the prescribed scompile wrapper, with no
errors or warnings. The Kummer, arrows, data and target modules took respectively
27.0 s, 21.1 s, 59.9 s and 3.2 s, each under the unchanged 60 s limit.
The Chern specification predicate now carries its owning Kummer node's blueprint
tag and appears in that node's declaration list; the colimit instance is also
listed in its owning arrows node. All lean.statement values were refreshed from
the exact source signatures using the project's declaration reader.
The target's natural statement, hypotheses, proof and proof dependencies are
unchanged. Its extra statement dependencies cite the new arrows and data nodes
(the Kummer node is reached through them), plus the published finite-twist sheaf,
normalized twist-pullback and scalar-forgetting nodes used in their construction.
The no-push delivery check is in progress.

A fresh dependency-import audit found that the projection-mate exactness module
has now been published. The target imports it privately, as required for an
already-stated proof dependency. Every other already-recorded proof-dependency
module was present in the delivery's imports. Fresh searches of Mathlib, upstream
WeilConjectures, the side library and the DAG again found no duplicate interface.

Performance repair: the initially successful data compile was close to the
60-second limit, and the dry run reproduced a timeout. A diagnostic copy with
a lower heartbeat budget located the cost in kernel checking of the dependent
`OrdinaryFiniteP1Datum` structure. The counit formula is now the named predicate
`OrdinaryFiniteP1CounitNormalization`; the field applies that predicate to exactly
the same decomposition and actual adjunction. The first base-change square now
names its canonical two-summand map as
`ordinaryFiniteP1DecompositionSourceMap`. Both helpers are defined in full in the
owning data module, have that node's source/blueprint docstrings, and are listed
in its lean.declarations. Unfolding them gives precisely the original formulas.
No file was split, no hypothesis changed and no compile limit was raised.
Diagnostic options and marker commands occur only in the scratchpad.

Final repaired compilation through scompile.py passed without errors or warnings.
The four delivered modules took 38.0 s (Kummer), 28.0 s (arrows), 14.7 s (data),
and 3.3 s (target). The newly required ProjectionMateExact proof import was
confirmed separately by the same server wrapper in 12.2 s. The local mirror's
stale KFlat universe interface was resolved by the wrapper's prescribed server
confirmation; it required no change to any dependency or additional hypothesis.
The final no-push delivery check follows.

Required final dry run: `deliver2.py Q43
lem-asd-ordinary-finite-p1-adjunction --no-push` printed
`OK (dry run): commit 357658d4e2 compiles and passes the preflight except for
the second reading, which the second reader writes; nothing pushed.`
The complete output is retained in `scratchpad/final-completed-dry-run.log`.
The independent second reading remains for the designated second worker.

## Second reading by Q43

I independently read the item node, its source place, the four delivered modules, and the three new definition nodes. The node's objects and hypotheses render as follows.

- The positive integer is `(N : ℕ)` with `hN : 0 < N`; the finite commutative coefficient ring is `(A : Type (u + 1)) [CommRing A] [Finite A]` with `hA : (N : A) = 0`. This is exactly the node's `N ≥ 1`, finite commutative `A`, and `NA = 0`; no field, flatness, characteristic, or connectedness assumption is added.
- The projective line and projection are rendered by `ProjectiveLine S` and `ProjectiveLine S ↘ S`, using the recorded projective-space declaration. The derived categories are `DerivedCategoryModule A S` and `DerivedCategoryModule A (ProjectiveLine S)`, so they are the entire ordinary small-etale module derived categories at the stated coefficient universe.
- The concrete coefficient line is `ordinaryFiniteLine A N hA T`, i.e. the degree-zero `finiteEtaleTateLine`; `ordinaryFiniteP1KummerClass` is the actual Kummer boundary of the recorded projective-space twist, followed by the canonical scalar-root map. `ordinaryFiniteP1ChernSpec` forces the datum's Chern arrow to realize this class, so it does not permit an unrelated arrow.
- `OrdinaryFiniteP1Datum.decomposition` has source `ordinaryFiniteLine ... S⟦2⟧ ⊞ ordinaryFiniteUnit ... S` and target the actual pushforward of the shifted projective-line line. `decomposition_hom` is exactly `biprod.desc` of `ordinaryFiniteP1Unit` and `ordinaryFiniteP1ChernPushforward`; `trace` is definitionally `decomposition.inv ≫ biprod.snd`, and `trace_chern` is the node's `t_q h = 1` clause.
- The adjunction is `(ordinaryFinitePushforward A (ProjectiveLine S ↘ S)) ⊣ ordinaryFiniteP1Right A N hA S`. `OrdinaryFiniteP1CounitNormalization` states, for every unbounded `K`, the actual ordered projection followed by the actual counit equals tensoring the trace and the canonical tensor-unit isomorphism. This is the node's displayed counit formula with the specified projection map.
- `OrdinaryFiniteP1BaseChange` quantifies over Noetherian `S'` and `S`, a morphism `f : S' ⟶ S`, both invertibility hypotheses, and every `K`; its three conjuncts are the decomposition square, trace square, and actual counit square. The target theorem `exists_ordinaryFiniteP1Adjunction` existentially supplies one normalized transport and one datum family for all such bases, then asserts this base-change predicate. This explicit global packaging supplies the canonical choices implicit in the node's “define” language and preserves every node clause.

The dependent definitions were also checked against their nodes. `OrdinaryFiniteTwistTransport` carries the roots inclusion normalization and the pure-tensor generator normalization from the finite-twist pullback node. The arrows module reuses the recorded inverse/direct image, derived tensor, exchange, and ordered projection constructions; it introduces no arbitrary map or `Nonempty` choice. The data module's two named helper predicates are only abbreviations of the node's actual counit and decomposition-source formulas, and all their fields have real data or postponed named propositions.

Edge cases were checked in the signatures and definitions: `N = 1` (forcing the zero coefficient ring under `hA`), the zero ring and zero derived categories, empty schemes, disconnected and nonreduced Noetherian schemes, non-affine Noetherian bases, arbitrary unbounded complexes, and finite rings that are not flat over `ℤ/N`. No index type, characteristic, field, separatedness, or boundedness restriction excludes a case in the node. The only positivity restriction is the node's `hN` on the existence theorem; helper definitions retain the general parameters they can type.

Searches were repeated with LeanFinder (`Ordinary etale projective line adjunction with finite coefficients and Kummer trace`), Loogle (`"Adjunction", "ProjectiveLine"` and `"kummer", "DerivedCategory"`), grep over Mathlib AlgebraicGeometry, grep over upstream `WeilConjectures`, grep over shared `lean/Sheaf`, and DAG/blueprint searches. They found no existing declaration of this normalized ordinary-etale projective-line interface; the hits were standard-etale algebra or unrelated Picard/Hilbert-90 results. LeanSearch was unavailable with an Internal Server Error and is recorded as unavailable in the worker searches. The cited finite-twist, scalar-comparison, exchange, and projection declarations are existing dependencies and were opened rather than copied.

I found no mismatch requiring a repair. In particular, the Lean statement is not a weaker cohomological or rank assertion: it fixes the actual Kummer class, biproduct decomposition, trace, ordered projection, counit, adjunction, and all three base-change arrows. The four modules compile separately through `scompile.py` under the unchanged 60-second limit, and the resulting no-push delivery preflight is now rerun after this report section is present.
