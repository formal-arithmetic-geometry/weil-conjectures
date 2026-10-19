## Worker report

This inherited report describes the superseded three-module draft. The final independent
reading in `## Second reading by Q37` below records the delivered single-module interface.

`Sheaf.Paper.PbcTowerCompatibility` states the unchanged node as
`pbcTowerCompatibility`: for the specified geometric input `c : PbcFourCorners A`
and finite etale origins `_origins : PbcFourArrows c`, there exists a
`PbcTowerCompatibilityWitness c`. All theorem proofs remain `sorry`; definitions
are actual constructions or choices uniquely specified by representative equations.

Each hypothesis and conclusion is rendered as follows:

- The adic coefficient datum is `c.datum : Scheme.AdicCoefficientDatum A`, including
  Noetherianity, finite generation, additive torsion of A/I, and finite perfect positive
  quotients. The datum is reexported by the dependency's recorded
  `Sheaf.Paper.AdicCoefficientDatum` from `CompletedAdicCoefficientDatum`.
- The four corners use `c.X`, `c.Y`, `c.X'`, `c.Y'`, the four named morphisms,
  `c.square : ChosenCartesianSquare g' f' f g`, and `c.proper : IsProper f`.
  The normalized integral and finite coefficient identifications are `cf`, `cg`,
  `cf'`, `cg'`; their projection and square equations retain the stipulated
  compatibility. `c.K` is intrinsically derived complete via `c.complete`.
- The finite origins are `PbcFourArrows.reductionPlus`,
  `reductionIdentification`, and `origin`, one for each n. They impose neither
  a uniform lower bound nor compatibility between origin witnesses.
- The four finite objects are the constructed `c.cornerA n`, `c.cornerB n`,
  `c.cornerC n`, `c.cornerD n`, in the quotient coefficient derived category.
  `c.corner i n` applies the existing exact `completedAdicDerivedRestriction`.
  No completed geometric pullback is substituted for ordinary derived pullback.
- The four derived-tower objects are `PbcTowerCompatibilityWitness.tower i` for
  `i : PbcCorner`, whose four constructors are a,b,c,d. Their category is precisely
  `DerivedCategory (CompletedAdicTowers c.Y' c.datum)`, where the tower category is
  `ℕᵒᵖ ⥤ CompletedAdicModules c.Y' c.datum`. Fields `h`, `h'`, `v`, `v'` have
  the four required sources and targets.
- `evaluation i n` identifies the evaluated tower with the specified restricted
  corner. `evaluation_h`, `evaluation_h'`, `evaluation_v`, `evaluation_v'` recover
  the actual canonical finite arrows `c.h n`, `c.h' n`, `c.v n`, `c.v' n`.
- `evaluation_transition i b a hab` recovers every original quotient transition
  for a≤b. The map `c.transition i b a hab` is the canonical transport of
  `pbcReductionTransition`; its defining representative formula is
  s tensor x ↦ q(s) tensor x. The evaluation-side map is the localization of the
  natural transformation of ordinary evaluation functors. Thus transitions are
  prescribed rather than freely chosen to fit an arbitrary realization.
- `rectangle : h ≫ v' = v ≫ h'` is an equality in the derived tower category.
  Evaluation naturality and `evaluation_transition` imply compatibility with
  all original transitions, including nonconsecutive and identity maps.
- `endomorphism_compatibility` quantifies over every `phi : c.K ⟶ c.K` and
  supplies tower actions whose evaluations are `c.action i n phi`, induced by
  the actual corner functors. Its four equations assert equivariance of each
  arrow in the derived tower category. As tower morphisms, the actions also
  commute with every transition. No unrelated quadruple of actions is an input.

Dependency declarations used directly are `AlgebraicGeometry.ProEtale.PbcFourCorners`
from `Sheaf.Paper.PbcFourCorners`, `AlgebraicGeometry.ProEtale.PbcFourArrows` and the
canonical arrow constructions from `Sheaf.Paper.PbcFourArrows`,
`AlgebraicGeometry.Scheme.AdicCoefficientDatum`, `CompletedAdicModules`,
`CompletedAdicTowers`, `completedAdicEvaluation`, `completedAdicQuotientReduction`,
and `completedAdicDerivedRestriction` reexported by
`Sheaf.Paper.AdicCoefficientDatum`, and
`AlgebraicGeometry.Scheme.IsCompletedAdicDerivedComplete` from
`Sheaf.Paper.CompletedAdicIntrinsicCompletion`. The restriction comparisons reuse
`proEtaleRingRestrictionDerivedPullback` and
`proEtaleRingRestrictionDerivedDirectImage` from the recorded ring-sheaf
change-adjunction interface. The source and K-flat normalization of each additional
helper are given in its owning module's docstring and listed in `lean.declarations`.

Edge cases checked: Lean n=0 is source exponent 1 (all exponents are n+1);
all a≤b, including a=b, are retained. Empty schemes, zero objects, the zero ring,
I=0, I=A and an empty generator family are not excluded when the datum's stated
hypotheses hold. There is no characteristic restriction or uniform cohomological
bound. Scheme and coefficient universe u follow the existing datum interface;
the small site keeps object universe u+1 and morphism universe u, and module
values have universe u+1.

Existing search records are retained in `searches.jsonl`: LeanFinder on
"Derived tower objects of four corner families and commuting rectangle" found
category-square declarations only; the alternate query "derived category inverse
sequence lift commuting base change diagram" found localization factorization
and injective-resolution naturality, not this assertion. Loogle `DerivedCategory`
found the category and its basic instances; the earlier query with
`NaturalTransformation` was rejected and is not negative evidence. The Mathlib
grep `tower.*rectangle|four.*corner` in CategoryTheory found no match. LeanSearch
"four corner derived tower coefficient reduction base change" was unavailable
(Internal Server Error). Direct project and upstream `rg` searches for
`lem-weil-pbc-tower-compatibility`, `pbcTowerCompatibility`, and
`PbcTowerCompatibilityWitness` found no complete existing declaration.

No statement dispute, statement correction, or new definition node is needed.
The dependency interface repairs below preserve all natural-language statements.
The inherited second reading is retained below; the next reader independently
checks this completed sandbox before delivery.

## Reused dependencies

The final delivery has no dependency module and no dependency-node replacement.
It imports the recorded `ProperBaseChangeFourCorners`, `ProperBaseChangeFourArrows`,
`AdicCoefficientDatumCompleted` (through those modules), `IntrinsicCompletionCompleted`,
and the generic evaluation/transition infrastructure of `BoundedConstructibleTower`.
The newly landed four-arrow module was discovered when the delivery wrapper refreshed
the base; it is read in full and used directly. Earlier dependency-repair sections
below are historical. All redundant dependency modules and node copies were removed.

## Earlier second reading (a previous round; superseded)

The original Worker report above describes the superseded draft. I independently opened
the main DAG node, both definition dependencies, their recorded dependency signatures,
the completed coefficient implementations, and the Stacks source. The original Lean did
not state the node: it replaced specified geometric constructions by arbitrary diagrams
and arbitrary maps. I repaired all three modules; the natural-language node statement is
unchanged. The corrected interface is described below and supersedes the earlier report.

The source checklist, with its Lean rendering and verdict:

1. Coefficients are a commutative Noetherian ring A, a finitely generated ideal I,
   additive torsion of A/I, and finite perfect positive quotients P_n=A/I^n. These are
   `PbcFourCorners.datum : Scheme.AdicCoefficientDatum A`, whose inherited
   `CompleteCoefficientDatum` fields are `noetherian`, `finitelyGenerated`,
   `quotientTorsion`, and `quotientPerfect`, together with `quotientFinite`. Verdict:
   exact. The first draft's bare arbitrary ring was insufficient when its datum was
   treated merely as ambient category data; the repaired corners use the full datum.
2. The ambient coefficient ring is the limit of the actual finite continuous-function
   sheaves, and finite reduction retains the quotient-ring action. The modules reuse
   `completedAdicCommRing`, `completedAdicFiniteCommRing`,
   `completedAdicQuotientReduction`, and `completedAdicDerivedRestriction`. In
   particular, `cornerA` through `cornerD` are finite-coefficient derived objects
   before restriction. Verdict: exact; the former arbitrary completed-module diagrams
   did not construct these objects or retain their specified quotient origins.
3. Objects are schemes X, Y, X', Y' and a cartesian square with arrows f, g, f', g',
   with f proper. These are the corresponding fields of `PbcFourCorners`, including
   `square : ChosenCartesianSquare g' f' f g` and `proper : IsProper f`.
   No separatedness, quasi-compactness or Noetherian hypothesis is added to a scheme.
   Verdict: exact. All of this geometry was absent from the first draft.
4. The specified integral and finite coefficient identifications are canonical and
   compatible with projections and composition. `PbcCoefficientIdentification.integral`
   and `.finite` give their isomorphisms. `.finite_normalization` fixes their adjoints
   to the existing `finiteCoefficientDirectImageRingMap`, obtained from precomposition
   on connected components and sheafification. `.projection` is precisely the stated
   coefficient square. `integral_square` and `finite_square` record composition around
   the geometric square. These are the specified coefficient identifications of the
   dependency, not arbitrary maps or extra flatness assumptions. Their normalizations
   also determine compatibility with every quotient. Verdict: exact.
5. K belongs to the unbounded completed-coefficient derived category on X and is
   intrinsically derived I-complete. This is `PbcFourCorners.K`, together with `r`,
   `generators`, `generators_span`, and `complete`. The predicate is the already
   published `IsCompletedAdicDerivedComplete` on this exact continuous-function
   coefficient presentation, not completeness in the constant coefficient category.
   The representative and generators express the source's finitely generated ideal;
   no boundedness of K is assumed. Verdict: exact; K and completeness were missing.
6. K_n is derived scalar extension of K and E is ordinary, uncompleted Lg'^*K;
   E_n is its finite-level pullback. These are the real constructions `Kn`, `E`,
   and `En`. `pbcReductionPullback` is chi in the source, selected from a unique
   comparison retaining its complete K-flat representative equation. Its ordinary
   comparison is the adjoint conjugate of the recorded identity-on-sections
   restriction/direct-image comparison, using the existing tensor-unit-normalized
   `adicDatumOrdinaryAdjunction`. Its counit reuses `adicDatumComplexCounit`.
   Thus no comparison is selected from an unconstrained `Nonempty` assertion.
   Verdict: exact, including the quotient-linear comparison delta=chi^-1.
7. The four finite corners are, respectively, Lg_n^* S_n(Rf_*K),
   Lg_n^* Rf_{*,n}K_n, S_n(Rf'_*E), and Rf'_{*,n}E_n. These are literally the bodies
   of `PbcFourCorners.cornerA`, `.cornerB`, `.cornerC`, `.cornerD`. All operations
   are the existing identified-coefficient `proEtaleRingDerivedPullback` and
   `proEtaleRingDerivedDirectImage`. Verdict: exact; no freely chosen corner remains.
8. The four-arrow dependency retains specified bounded-below etale origins at every
   finite level, with no uniform lower bound and no compatibility across levels.
   `PbcFourArrows.reductionPlus`, `.reductionIdentification`, and `.origin` retain a
   bounded-below presentation of the actual K_n and its `EtaleOriginWitness`.
   Transporting the witness through the specified identification gives exactly alpha_n.
   Verdict: exact; the former arbitrary natural transformations had no such witnesses.
9. The four finite arrows are the projection companions, reduced ambient exchange,
   and canonical finite exchange. `pbcFiniteProjection` is explicitly the adjunct
   of chi followed by reduction of the ambient counit. `PbcFourCorners.h` is its
   pullback; `.h'` is projection followed by Rf' of delta; `.v` is chi followed by
   reduction of `.exchange`; `.v'` is `.finiteExchange.app (Kn n)`. Both exchanges
   reuse the recorded `proEtaleAmbientRingedExchange`. The three invertibility
   clauses of the definition are `pbcFourArrows_isIso`; it makes no assertion that
   v_n is invertible or that the rectangle already commutes. Verdict: exact.
10. The original quotient maps make four objects of D(Tow_A(Y')). These are
    `PbcTowerCompatibilityWitness.tower : PbcCorner → DerivedCategory
    (CompletedAdicTowers c.Y' c.datum)`, for the four constructors a,b,c,d.
    The four witness arrow fields have exactly the corresponding sources and targets.
    The theorem asserts `Nonempty (PbcTowerCompatibilityWitness c)` for the specified
    `c` and its etale origins. Verdict: exact. The former theorem erroneously
    quantified over arbitrary four diagrams and arbitrary arrows; even its claimed
    rectangle was false for freely chosen noncommuting arrows.
11. Evaluations recover the finite corners and arrows after scalar restriction.
    `.evaluation` identifies each evaluated tower with `c.corner i n`, which is the
    explicit scalar restriction of the specified finite corner. The four
    `.evaluation_h`, `.evaluation_h'`, `.evaluation_v`, `.evaluation_v'` equations
    recover the actual canonical finite maps under those same isomorphisms.
    Verdict: exact; quotient actions have been retained until the prescribed restriction.
12. Every quotient transition, not just the objects at each n, is recovered.
    `pbcReductionTransition_existsUnique` fixes the derived transition by its formula
    s tensor x ↦ q(s) tensor x on every K-flat representative and its derived-counit
    equation. `underlyingTransition` applies the actual corner functors to this map.
    `underlyingIso` consists entirely of the existing canonical restriction/pullback
    and restriction/direct-image comparisons. `transition` is their transport of
    that same quotient map. `.evaluation_transition` compares it with the actual
    derived evaluation transformation for every b,a and a≤b, including a=b.
    Verdict: exact. The former pointwise evaluation isomorphisms omitted this clause.
13. The rectangle is an equality in the derived tower category before evaluation:
    `.rectangle : h ≫ v' = v ≫ h'`. Verdict: exact. Naturality of evaluated tower
    morphisms together with clause 12 makes the rectangle commute with every original
    transition; no inference of derived equality merely from equality of evaluations
    is used in the proof plan.
14. Compatibility concerns endomorphisms of K. `.endomorphism_compatibility` quantifies
    over `phi : c.K ⟶ c.K`, supplies actions on all four towers, identifies their
    evaluations with `c.action i n phi` induced by the actual corner functors, and
    imposes all four arrow equivariances in D(Tow). These actions are tower morphisms,
    so they also commute with every transition. Verdict: exact. The former
    `PbcCompatibleEndomorphism` was an arbitrary precommuting quadruple of actions,
    omitted K itself, and strengthened the quantifier to actions not induced by K.

Edge cases: `n : ℕ` denotes the positive exponent n+1 everywhere, so Lean n=0 is
source level 1; no source exponent zero is discarded. All a≤b are included, so identity
and nonconsecutive quotient maps are covered. Empty schemes, zero objects, the zero ring,
I=0 and I=A are not excluded. The generator type `Fin r` includes r=0. There is no
nonempty arbitrary-index hypothesis: the source fixes the positive-natural tower. There
is no restriction on characteristic, a uniform cohomological bound, or compatibility
between etale-origin witnesses. Scheme universe u uses its actual small site with object
universe u+1 and morphism universe u; the finite quotient is lifted into u+1 and module
values are in u+1. No equality between those site universes was imposed.

Searches independently repeated with different terms:

- LeanFinder: `derived category inverse sequence lift commuting base change diagram`.
  Hits were `DerivedCategory.left_fac`, `right_fac`, exact-derived factorization and
  injective-resolution naturality; none states the specified coefficient rectangle.
- Loogle: `DerivedCategory`. The category, single functor and its basic instances were
  found and read; no four-corner tower construction was found.
- LeanSearch: `four corner derived tower coefficient reduction base change`.
  The service returned Internal Server Error. This is recorded as unavailable, not a
  negative search verdict.
- `rg` in Mathlib/Algebra/Homology, upstream WeilConjectures, and project lean/Sheaf
  for tower/rectangle, four/corner and the proposed declaration names found no existing
  complete statement. Project searches for scalar adjunctions and reduction counits
  found `adicDatumOrdinaryAdjunction` and `adicDatumComplexCounit`; the repair reuses
  these existing canonical constructions through typed views rather than restating them.
- Dependency source reads included `CompleteCoefficientDatum`,
  `CompletedAdicCoefficientDatum`, `AdicCoefficientDatum`,
  `AdicCoefficientDatumCompleted`, both completed intrinsic-completion interfaces,
  `ProEtaleOperations`, `ProEtaleOperationsCanonicalAdjunction`,
  `ProEtaleAmbientRingedExchange`, `ProEtaleRingSheafChangeAdjunction`,
  `ProEtaleFiniteModules`, `ProEtaleFiniteCoefficientDirectImage`, and
  `EtaleOriginWitness`. The previously reported replacement of the adic coefficient
  node is unnecessary: its current recorded module publicly reexports the needed
  completed datum. That stale node-copy change was removed.

Source reading: Stacks `proetale.tex`, `lemma-pushforward-Noetherian-case` (099N),
`lemma-describe-constructible-complexes` (09C2), and `theorem-proper-base-change` (09C9),
including the preceding constructibility definition and the complete proper-base-change
hypotheses. 099N gives the single-object completion/pullback formulas; 09C9 supplies the
proper square, derived completeness, bounded-below etale origins and perfect quotients.
09C2's quasi-compactness and uniform interval concern its constructible specialization,
not the general tower lemma, so neither was silently added. The source note explicitly
attributes the derived-tower assembly to the blueprint. The main proof docstring now
follows all five DAG proof steps, including quotient/object naturality, explicit transport
through the horizontal isomorphisms, construction of the fourth edge, and endomorphism
naturality before evaluation. The dependency helper proof docstrings give their canonical
adjunction, K-flat and pure-tensor computations.

No new DAG node was needed and no statement correction was made. All changes repair the
Lean rendering and dependency interfaces to match the unchanged source statements. Every
definition has real data or selects an object uniquely fixed by its full normalization;
every theorem is postponed with `sorry`. There is no file-local notation, private copy,
file-local instance, hollow hypothesis, or unbound universe. Public helper declarations are
listed in each owning node's `lean.declarations`; the three primary signatures are copied
verbatim into `lean.statement`.

## Dependency modules (second-reading corrections)

`def-weil-pbc-four-corners`: rebuilt `Sheaf.Paper.PbcFourCorners` to construct the actual
four finite-coefficient objects from the proper cartesian square, normalized coefficient
identifications and derived-complete K. Its canonical reduction/pullback and quotient
transition helpers retain the full representative and pure-tensor normalizations. This
replaces the arbitrary four-diagram structure, which did not define the dependency notion.

`def-weil-pbc-four-arrows`: rebuilt `Sheaf.Paper.PbcFourArrows` to retain the specified
etale origins and define the four maps by their explicit canonical formulas. The finite
projection helper is the exact scalar-extension adjunct specified in this node; the
ambient projection-formula mate itself remains the existing recorded declaration. Its
invertibility assertion is the three isomorphism clauses of the definition. No map or
precommuting endomorphism quadruple is an unconstrained input.

`def-weil-pbc-intrinsic-completion`: under §1(B), record the already published
`AlgebraicGeometry.Scheme.IsCompletedAdicDerivedComplete` in
`Sheaf.Paper.CompletedAdicIntrinsicCompletion` with `existing: true`. The current recorded
completed-constant presentation has a different coefficient-ring presentation and cannot
be applied directly to K over this node's continuous-function `completedAdicRing`. The
reused existing interface is the exact same Koszul completion notion on that precise
coefficient sheaf, with its normalized unit. No completion definition was copied. The
item cites this already recorded dependency explicitly. The existing adic datum record
was left unchanged because its current module already reexports the required interface.

The final declaration-list audit also corrected four primed helper names (`F'`, `G'`,
`h'`, `v'`): the automatic inventory had stripped their apostrophes and listed the
unprimed declarations twice. All four are now recorded with their exact Lean names.

Compilation exposed an inference issue in the evaluation-transition definition: the
opaque `completedAdicEvaluation` name hid Mathlib's localization-lifting instance. Its
implementation now passes the definitionally identical existing exact evaluation functor
explicitly, retaining the same canonical localization and transition formula.

Validation: the prescribed `scompile.py Q37 lem-weil-pbc-tower-compatibility`
run on all three sibling modules passed locally, one file at a time, with no errors
and no disallowed warnings. The primary signatures match their node records verbatim,
all explicit helper declarations are inventoried with exact names, and the node delta
contains only the authorized Lean interfaces and the added recorded dependency.

The first delivery dry run compiled all delivered modules and the existing-declaration
probe. Preflight found only that its exact `## Dependency modules` section still
contained the inherited draft; that section now names and explains all three final
dependency repairs. No Lean source or mathematical statement changed in this fix.

## Worker continuation, 2026-10-16

I reopened the three current modules and their four node copies and replaced the
stale Worker report, which still described the arbitrary-diagram draft. This
continuation changes no Lean declaration or node statement. The earlier independent
second reading remains historical evidence; the dispatcher assigns the final reader.

Fresh searches: LeanFinder `strict derived coefficient towers four corners base
change evaluation compatible endomorphisms` returned cotangent-complex and algebraic
base-change lemmas, no tower realization. Loogle
`DerivedCategory, CategoryTheory.NatTrans` returned zero hits. Mathlib grep
`tower.*rectangle|four.*corner` in Algebra/Homology returned zero hits. Direct `rg`
in upstream WeilConjectures and project Sheaf found no target or witness declaration.
The similar `Scheme.pbcReductionTransition` in `BoundedConstructibleTower` uses its
own scalar-extension interface and lands in a restricted quotient category; its
signature and defining adjunction were read. The current helper instead fixes a
natural transformation between the recorded completed reduction/restriction functors
by its K-flat equation, on the precise coefficient presentation of this delivery.

The local checkout has no downloaded blueprint or Stacks text. I therefore checked
the external source pages directly: [099N](https://stacks.math.columbia.edu/tag/099N),
[09C9](https://stacks.math.columbia.edu/tag/09C9), and
[09C2](https://stacks.math.columbia.edu/tag/09C2). Their role agrees with the node's
source note: single-object reduction and proper base change provide inputs, while
the derived-tower assembly and its precise transitions are stated by the blueprint
node and its five recorded proof steps. No extra constructibility or quasi-compactness
hypothesis from the specialization in 09C2 was inserted.

## Second reading by Q37

I independently read the item and all its statement dependencies, the exact recorded
Lean sources, the delivered module, the earlier return, and the Stacks tex places.
This section supersedes every earlier reading and continuation above. The informal
item and all dependency statements remain unchanged; no statement_change is needed.

Source checklist (objects, hypotheses and conclusions), with the final Lean rendering:

1. A is commutative and Noetherian; I is finitely generated, A/I is additive torsion,
   and each positive P_n=A/I^n is finite and perfect over A. Rendering: the theorem's
   `{A : Type (u+1)} [CommRing A]` and `c.datum : ProEtaleAdicCoefficientDatum A`,
   whose CompleteCoefficientDatum fields are `ideal`, `noetherian`, `finitelyGenerated`,
   `quotientTorsion`, `quotientPerfect`, with the additional `quotientFinite` field.
   Verdict: exact. The first draft's Type u restriction was a mismatch and is repaired.
2. X,Y,X',Y' and f,g,f',g' form the proper cartesian square. Rendering:
   `PbcTowerInput.X`, `.Y`, `.X'`, `.Y'`, `.f`, `.g`, `.f'`, `.g'`,
   `.square : ChosenCartesianSquare g' f' f g`, and `.proper : IsProper f`.
   Verdict: exact; no scheme finiteness, nonemptiness, separatedness or dimension
   hypothesis is added. The bundle stores only the inputs to the recorded corner and arrow functions.
3. Coefficients are the finite sheaves and their actual limit A_T, with the stipulated
   canonical inverse-image identifications and quotient compatibility. Rendering:
   `adicDatumRing`, `adicLisseRingSystem`, `adicDatumProjection`,
   `fourCornerCoefficientIso`, `fourCornerFiniteIso`, and `fourCornerProjectionComm`.
   Read the latter definitions: the integral comparison is the recorded profinite
   comparison conjugated by the identity-on-objects quotient-tower identification;
   the finite comparison is the constant coefficient comparison. The normalized
   `adicDatumFiniteCoefficientIso` identifies this finite presentation with the
   continuous-functions presentation, naturally for quotients. Verdict: exact.
   The former competing continuous-function datum and arbitrary coefficient-iso
   input are removed. The existing `fourArrowIntegralCoefficients_comm` and
   `fourArrowFiniteCoefficients_comm` supply square coherence for the fixed maps;
   neither an arbitrary coefficient isomorphism nor a coherence hypothesis is added.
4. K is an unbounded derived A_X-module, intrinsically derived I-complete.
   Rendering: `c.K : adicDatumDerived c.X c.datum`, the generating tuple and span
   equation, and `c.complete : IsCompletedIntrinsicallyDerivedComplete ... c.C c.eC`.
   `C` and `eC` merely represent K, exactly as in the recorded corner declaration;
   the predicate is invertibility of its actual Koszul completion map. Every derived
   object has such a representative. Verdict: exact. The alternate unbridged
   completion predicate and its node-record replacement were removed.
5. K_n is derived finite scalar extension; E is the ordinary uncompleted pullback;
   E_n is its finite pullback. Rendering: `Kn`, `E`, `En` use `adicDatumReduction`,
   `fourCornerPullback`, `fourCornerFinitePullback` directly. The existing
   `fourCornerReductionPullback` runs S(Lu*) -> Lu_n*(S); its inverse is chi in
   the arrow definition and its hom is delta. Its source theorem fixes the actual
   ordinary adjunction-conjugate comparison on flat-term K-flat representatives.
   Verdict: exact, with the correct directions and quotient-linear coefficient action.
6. The finite origins consist of independently specified L_n in D^+(X_et,P_n) and
   alpha_n identifying their pro-etale images with K_n. Rendering: `PbcTowerInput`
   has `reductionPlus`, `origin : EtaleOriginWitness ...`, and
   `reductionIdentification`, exactly the W,w,e inputs of `properBaseChangeFourArrows`.
   The last uses the recorded `fourArrowOriginTransport`, which is derived restriction
   along the existing normalized `adicDatumFiniteCoefficientIso.hom`, to put the
   witnessed object into the recorded finite-corner category. I read its underlying
   `finiteOriginRestriction` and `finiteOriginTransport` definitions and exactness
   theorem in `FiniteLevelRingedProEtaleBaseChange`.
   Verdict: exact; both coefficient presentations are canonically identified rather
   than required to be definitionally equal. No uniform lower bound or compatibility
   between witnesses at different n is imposed.
7. The four corners are precisely the four objects in the dependency, and not
   arbitrary derived diagrams. Rendering: `PbcTowerInput.corners` is a call to
   the recorded `properBaseChangeFourCorners` with these exact inputs;
   `cornerA`, `cornerB`, `cornerC`, `cornerD` are its four projections.
   Verdict: exact. The redundant four-corner construction/module/record was dropped.
8. The four arrows are the actual maps h_n,h'_n,v_n,v'_n. Rendering:
   `PbcTowerInput.arrows` calls the recorded `properBaseChangeFourArrows` with all
   original inputs and origins, and `.h`, `.h'`, `.v`, `.v'` project its maps.
   I read this existing function: its first two components are pullback of
   `fourArrowProjectionIso` and the second projection followed by Rf' of delta;
   its third is chi followed by reduced ambient exchange; its fourth is the
   canonical `fourArrowFiniteExchange`, certified invertible with the specified
   origins. The projection helper is exactly the finite counit adjunct, and both
   exchanges use the canonical ringed mate. Verdict: exact. The concurrent landing
   makes the entire drafted arrow dependency redundant, so its module and node copy
   are dropped; no projection, exchange, coefficient transport or invertibility
   theorem is restated in this delivery.
9. The four corner families become objects in D(Tow_A(Y')) after scalar restriction.
   Rendering: `PbcTowerCompatibilityWitness.tower : PbcCorner ->
   DerivedCategory (adicDatumTowers c.Y' c.datum)`; the recorded tower category is
   `ℕᵒᵖ ⥤ adicDatumModules c.Y' c.datum`. The theorem asserts a nonempty witness
   for the specified input (including its origins). Verdict: exact, D of strict towers rather
   than a functor into D. The four constructors a,b,c,d give exactly four positions.
10. The four arrows are morphisms of these derived towers. Rendering: witness fields
    `h : tower .a -> tower .b`, `h' : tower .c -> tower .d`,
    `v : tower .a -> tower .c`, `v' : tower .b -> tower .d`.
    Verdict: exact, with all sources and targets checked.
11. Evaluation recovers the named objects and maps. Rendering: `evaluation` identifies
    each existing `Scheme.pbcTowerEvaluation` with `c.corner i n`, the exact scalar
    restriction of the finite corner. `evaluation_h`, `evaluation_h'`, `evaluation_v`,
    `evaluation_v'` are the four conjugation equations with those same identifications.
    Verdict: exact; the finite arrows retain their finite coefficient action until
    the prescribed restriction. Existing evaluation definitions are reused.
12. The original quotient transitions are retained. Rendering: `evaluation_transition`
    quantifies over every a≤b and identifies the existing `Scheme.pbcTowerTransition`
    with `c.transition i b a hab`. The latter transports `underlyingTransition` along
    the existing canonical restriction/pullback/direct-image comparisons.
    `pbcReductionTransition_existsUnique` fixes its only scalar-reduction map by its
    equation on every K-flat representative with `adicDatumOrdinaryTransition`.
    That existing ordinary map sends s tensor x to q(s) tensor x; no new ordinary
    reduction or freely chosen transition is introduced. Verdict: exact, including
    adjacent, nonconsecutive and equal-index maps. The added additivity instance just
    exposes the existing extension/restriction composite to instance search.
13. The rectangle commutes in the derived tower category and with every transition.
    Rendering: `rectangle : h ≫ v' = v ≫ h'`. Naturality of each evaluated tower
    morphism and the preceding transition equations give the original transition
    squares. Verdict: exact. Equality in D(Tow) is asserted before evaluation; it
    is never inferred from a false faithfulness claim about individual evaluations.
14. The rectangle is compatible with every endomorphism of K. Rendering:
    `endomorphism_compatibility : ∀ phi : c.K -> c.K, ∃ act ...` gives four actual
    tower endomorphisms, identifies their evaluations with `c.action i n phi`, and
    asserts all four arrow equivariances in D(Tow). The actions use the same actual
    corner functors and coefficient identifications as the objects and transitions.
    Verdict: exact. These are endomorphisms of K, not an arbitrary precommuting
    quadruple assumed as input; their tower-morphism type includes transitions.

Source places read: Stacks `proetale.tex`, 099N
`lemma-pushforward-Noetherian-case`, including `lemma-naive-completion` before it;
09C2 `lemma-describe-constructible-complexes` and its preceding definition; 09C9
`theorem-proper-base-change`, its hypotheses and proof. The source note explicitly
says the derived-tower assertion is the blueprint's addition; the five recorded DAG
proof steps supply its strict realization, quotient/object naturality, transported
horizontal arrows, fourth edge and endomorphism naturality. The main docstring
carries all five steps. 09C2's quasi-compactness, constructibility and common bounds
are hypotheses of its specialization, not of this node. They are not added here.
099N and 09C9 require the Noetherian and completeness hypotheses already present.

Edge cases: n : ℕ means source exponent n+1, so n=0 covers exponent 1. No source
positive level is lost. All a≤b, including a=b, are retained. The index is the fixed
positive-natural tower, so there is no arbitrary nonempty-index assumption. Empty
schemes, zero derived objects, the zero ring, I=0, I=A, and the empty generator tuple
r=0 are admitted when the stated datum holds. There is no characteristic exclusion,
no bound on K, and no common bound across its reductions. The coefficient ring and
module values are in u+1, and Scheme.{u} keeps its small pro-etale site's object
universe u+1 and morphism universe u; no universe equality or lowering is imposed.

Independent searches with different terminology: LeanFinder on inverse sequence,
scalar restriction, natural transformation and base-change square found ordinary
sheaf-module restriction and pullback naturality, not this derived-tower theorem.
Loogle `CategoryTheory.evaluation` found the generic exact evaluation infrastructure;
the earlier `Localization.liftNatTrans` query was rejected as an unknown identifier
and gives no absence evidence. LeanSearch on a commuting derived square of inverse
systems was unavailable (Internal Server Error), recorded as such. Mathlib rg for
properBaseChangeFourCorners, adicDatumDerivedTower, pbcTowerCompatibility returned no
match. Concept searches for tower/square/rectangle/base change in Mathlib, the upstream
WeilConjectures tree, the 51-module project framework and project Sheaf found no complete
statement. They did locate `Scheme.pbcTowerEvaluation`, `pbcTowerTransition` and the
standard tower localization in `BoundedConstructibleTower`; I read and reused them.
Its elementwise `Scheme.pbcReductionTransition` uses the other completedAdic scalar
extension interface and has a quotient-category target; it is not a natural map of
these recorded `adicDatumReductionUnderlying` functors. The helper here only descends
the already recorded ordinary quotient map using the actual adicDatum universal
counits. Searches and source reads found no existing identical declaration.

Mismatches repaired: (H3) restored Type (u+1) coefficients and the correct small site;
(H4/H13) removed the second datum/corner construction and unbridged completion-record
replacement, reusing the exact recorded dependencies; reused the landed normalized finite
coefficient witness transport and all four canonical arrows; (H4) reused the existing derived evaluation/transition
infrastructure; exposed inherited additivity for the existing reduction composite;
updated all declaration inventories and exact primary signatures, and removed the
inherited extra direct completion dependency (already imported through the corners). No new node was
created, no target or informal statement changed, and every theorem proof is `sorry`.
All definitions have constructed data or choose an object fixed by the full stated
universal/representative characterization. The main module's only input bundle
stores the original parameters and origin witnesses; its corner and arrow projections
use the exact existing declarations.

Concurrent landing handled before push: while the first dry run was finishing,
`def-weil-pbc-four-arrows` acquired the recorded `ProperBaseChangeFourArrows` module
(from NP's delivery of NG's dependency). I opened its full source and the finite-origin
transport it imports, checked all formulas and signatures against the dependency node,
and stopped the push wrapper during compilation. The earlier three-theorem arrow module
and dependency-node copy were removed. `PbcTowerInput` now bundles exactly the inputs of
both recorded functions, including their origin data; the main theorem takes this single
bundle. This is the same quantification as the earlier input-plus-origins presentation.
The final statement uses their outputs literally, avoiding a duplicate declaration.

The earlier two-file compile and dry-run result `c677ec7d04` were successful but are
superseded by this final one-file delivery. That dry run also demonstrated that the
queue/index staging failure was transient and the server confirmation path repairs a
missing local overlay cache. Final one-file validation follows below.

Final validation: the single delivered `PbcTowerCompatibility.lean` compiled cleanly
through scompile.py, including the newly published arrow interface and its finite-origin
transport. Its two theorem proofs remain `sorry`; all definitions use existing
constructions or the uniquely normalized quotient transition. The final static audit
checks the exact primary signature, unique declaration inventory, 100-character line
width, and one module/one node with no dependency replacement. Dry-run commit
`2d69b767b9` passed the stage-2 preflight and compiled, staging exactly this report,
the item node and its module. No errors or warnings remain.
