## Worker report

The item module is `Sheaf.Paper.ProjectionFormulaBaseChangeNaturality`.
It states the naturality of the specified projection mate for arbitrary maps in K,
the two equations for the actual bounded-totalization arrows, including specified
coefficient-representative identifications, and base-change compatibility on the actual
small ringed pro-etale sites. The proof of every theorem is `sorry`; every definition
has actual data. There is no statement correction and there are no new DAG nodes.

Clause-by-clause correspondence:

- Small ringed sites, commutative coefficient sheaves, ordinary uncompleted tensor,
  and unbounded derived categories: the general reduction theorem has the same C, D,
  JC, JD, R, S and RI binders as the recorded `ringedProjectionFormulaArrows`.
  The base-change theorem uses `ProEt.topology T`,
  `Sheaf (ProEt.topology T) CommRingCat.{u+1}` and
  `DerivedCategory (proEtaleRingModules T R_T)` on all four schemes. It does not use
  condensed-module, completed, bounded-constructible or constant-coefficient categories.
- A ringed-topos map and its canonical module pullback: `uInv`, `uPush`, `adj`,
  finite-limit preservation, `I`, `c`, `uStar`, `hobj` and `hmap` are exactly the
  corresponding arguments of the recorded arrows. `hobj` and `hmap` fix extension
  of scalars after inverse image, on objects and on maps; they do not quantify over
  an unrelated arbitrary pullback functor.
- Derived pullback and tensor: `LF`, `epsilon`, `hLF`, `PR`, `PS`, `hPR`, `hPS`,
  `TR`, `TS`, `rR`, `rS` and `k` are the recorded flat-term K-flat representative
  presentations and the normalized ordinary comparison. `V`, `am`, `RF`, `eta`,
  `hRF`, `computeR`, `computeL`, `adjD` and `canonicalAdj` are exactly the recorded
  ordinary and derived adjunction/right-derived data. No new tensor comparison or
  arbitrary adjunction is substituted into the totalization arrows.
- Arbitrary K and Q and naturality in K: `derivedProjectionFormulaMate_naturality`
  binds `E E'`, arbitrary `Q`, and `q : E ⟶ E'`. Its two sides are precisely pi
  followed by R(q tensor identity), and (Rq tensor identity) followed by pi.
  This is the uncurried existing counit mate, with arbitrary tensor comparison
  presentation `alpha`; instantiation by the canonical comparison gives the node's pi.
- Bounded finite-projective coefficients with strict-perfect packages: the reduction
  theorem binds `F`, `P : StrictPerfectCoefficientPackage ... F`, and `hbounded`.
  Each degree of P is the specified retract of a finite free module. `E`, `K`,
  `hK`, `repE`, and their primed counterparts are K-injective presentations of the
  source and target K-objects. The universal map is `phi : E ⟶ E'`.
  Taking E'=E and the same representative gives every endomorphism in the node.
  F is arbitrary, so this is pointwise for every chosen Q_n; there is no restriction
  on the set of reduction indices or an implicit existence claim about representatives.
- Pi_n and rho_n are the `.1` and `.2` of the recorded
  `ringedProjectionFormulaArrows` applied with exactly those arguments. In particular
  rho_n is its specified finite-total chain-map image. It is not an independently
  supplied inverse, a new choice, or an inverse defined only by an IsIso assumption.
- A specified coefficient representative Q_n ≅ P_n: `Qn` and
  `eQ : DerivedCategory.Q.obj F ≅ Qn` implement this optional identification.
  `transportTensorProjectionArrows` conjugates pi and rho by
  TR(identity,eQ) and RF(TS(identity,LF(eQ))), with the appropriate inverse directions.
  The identity isomorphism includes the untransported assertion. All the objects and
  morphisms remain in the ambient R-derived category; any prior scalar restriction
  is already part of the supplied reduction object.
- The reduction morphism phi_n is exactly
  `TS.map (Prod.mkHom phi (𝟙 (LF.obj Qn)))`; its direct image is `RF.map` of that
  map. The other displayed operator is
  `TR.map (Prod.mkHom (RF.map phi) (𝟙 Qn))`. Lean's `≫` composes left to right.
  The first conjunct is pi followed by RF(phi_n) = that operator followed by pi.
  The second is rho followed by that operator = RF(phi_n) followed by rho.
  The primed arrows allow arbitrary maps in K, and include both requested
  endomorphism equations as the specialization just described.
- Cartesian scheme square: the base-change theorem binds the four schemes and all
  four scheme arrows with exactly their displayed domains, and
  `sq : ChosenCartesianSquare g' f' f g`. Its inherited commutativity and chosen
  fibre-product identification are the recorded notion, without an extra geometric
  hypothesis such as properness or flatness.
- Four coefficient sheaves and compatible identifications: `RX`, `RY`, `RX'`, `RY'`
  and `cf`, `cg`, `cg'`, `cf'` have exactly the corresponding inverse-image types.
  `hcoeff` is HEq of the two composite coefficient identifications over the equality
  of the composite scheme arrows. This is commutativity as ringed topoi.
- Canonical derived adjunctions and exchange: the actual operations are
  `proEtaleRingDerivedPullback`, `proEtaleRingDerivedDirectImage` and
  `proEtaleRingDerivedAdjunction`; exchange is the delivered
  `proEtaleAmbientRingedExchange`, which takes the mate of the normalized composition
  comparison under these exact adjunctions.
- Arbitrary base-change K and Q: the last two binders of
  `proEtaleProjectionFormula_baseChange` are in the entire derived categories of
  RX- and RY-module sheaves. The four `ProEtaleTensorModel` arguments present ordinary
  derived tensor by its signed total tensor on flat K-flat representatives. These
  are presentations of the node's specified operations, not additional geometric,
  boundedness, perfectness, completeness, or invertibility assumptions.
- First route: the left side applies Lg to `proEtaleProjectionFormulaMate f ...`,
  then the ambient exchange at `aX.tensor.obj (K,Lf Q)`. Its last map is Rf' of
  the g' tensor comparison followed by tensor(identity,theta inverse on Q).
  Thus the target is exactly identified in the direction specified by proof step 4.
- Second route: the right side is the canonical g tensor comparison, then
  `aY'.tensor.map (Prod.mkHom (exchange.app K) (identity on Lg Q))`, then the
  projection mate for f' at Lg'K and Lg Q. Its source and target agree with the first
  route after the explicit identification. No exchange or projection map is assumed
  to be an isomorphism.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`,
  `AlgebraicGeometry.ChosenCartesianSquare`, including both projection equations.
- `Sheaf.Paper.ProjectionFormulaArrows`,
  `CategoryTheory.derivedProjectionFormulaMate` and
  `SheafOfModules.ringedProjectionFormulaArrows`, including its whole definition,
  ordinary finite-total inverse, mixed representatives, and representative transport.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullback`,
  `SheafOfModules.CanonicalRingedTensorComparison`, its total comparison, and
  `ringedTopoiCanonicalDerivedTensorPullback`/`...Comparison`, with their complete
  representative characterization and unit normalization. The general theorem
  remains publicly available through the delivered extension module.
- `Sheaf.Paper.ProjectionFormulaTotalization`,
  `SheafOfModules.ringedProjectionFormula_totalization`, for the actual pair's two
  inverse identities; imported as a proof dependency.
- `Sheaf.Paper.RingedExchangeTensorCoherence`, including
  `RingedTensorSquare.derivedComparison`, `.exchange`, `.projectionFirst`,
  `.exchangeFirst`, and `ringedExchangeTensorCoherence`; imported as a proof
  dependency. I checked the final theta inverse direction in its first route.
- The ambient exchange dependency now has a published source; the retained interface
  repair exposes its canonical pullback comparison for the target identification. Its
  module uses `ProEtaleOperationsCanonicalAdjunction` through the recorded
  `ProEtaleConstantDerivedDirectImage`, retaining the arbitrary identified-ring APIs.
  I read `proEtaleRingDerivedAdjunction` and its unique ordinary-unit normalization.
- `Sheaf.Paper.ProjectionMateExact`, `SheafOfModules.ringedProjectionMateExact`,
  read from the current server source. The published theorem and canonical-shift/unit
  helper predicates are usable unchanged, so this module is imported without a
  duplicate dependency delivery or a change to ND's record.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition`,
  `proEtaleRingCompositeCoefficients` and `proEtaleRingDerivedPullbackComposition`,
  including the normalized adjunctions, sectionwise direct-image comparison, ordinary
  conjugate, degreewise complex comparison and K-flat factorization equation.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`,
  `proEtaleSheafInverseImage`, `proEtaleBaseChange`, the original small-site/module
  transports and coefficient actions; `ProEtaleOperations` for all actual arbitrary
  coefficient derived operations. `FlatOnSite.IsFlatOnSite` is used for the flat-term
  predicate at these independent universes.
- `Mathlib.CategoryTheory.Adjunction.Mates`, `mateEquiv`; and upstream
  `WeilConjectures.CategoryTheory.Adjunction.ProjectionMap`, the existing
  `Adjunction.rightAdjointProjectionMap`, reused by `derivedProjectionFormulaMate`.
  Its full docstring and transpose/naturality interfaces were read.

Source checks: I opened the blueprint markdown for order 1274 in the local literature
copy, and read sites-cohomology.tex at `remark-base-change` (07A7),
`equation-projection-formula-map` (0B56), `lemma-projection-formula` (0944),
`remark-compatible-with-diagram` (0E48), and `lemma-pullback-tensor-product` (07A4).
The comparison of targets is precisely the final tensor-then-composition vertical
path in the Stacks diagram. The explicit proof docstrings retain the node's four
steps: adjunct naturality, inverse conjugation, identification of canonical mates,
and tensor/commutation coherence.

Edge cases checked: identity maps and identity squares, arbitrary endomorphisms
including identity and zero, zero derived objects, the zero ring sheaf, empty schemes,
zero complexes, finite free rank zero, a bounded complex with empty support, negative
and zero degrees, arbitrary shifts, and the identity coefficient-representative
isomorphism. No nonemptiness, characteristic, properness or flatness condition is added.
There is no assertion that an arbitrary perfect sheaf complex has a global
strict-perfect representative. The small pro-etale site's universes remain u+1 for
objects and u for morphisms, with coefficient/module values in u+1.

Searches performed with the prescribed wrapper and direct source reads:

- LeanFinder: "The projection formula map defined using the counit is natural in the
  source and commutes with derived base change" returned eight unrelated resolution,
  condensed-module and locally Cartesian naturality results, no exact statement.
- Loogle: `CategoryTheory.derivedProjectionFormulaMate,
  SheafOfModules.RingedTensorEdge.projection` returned no hits/unknown project
  identifier. Loogle `"rightAdjointProjectionMap"` returned no indexed hits.
- LeanSearch: "Naturality of the derived projection formula morphism" was unavailable
  (Internal Server Error); this is recorded as unavailable, not as evidence of absence.
- Mathlib grep via msearch: `projection.*(natur|[Bb]ase[Cc]hange)|[Pp]rojection.*[Mm]ate`
  in CategoryTheory returned only cokernel projection naturality.
- Direct rg of upstream WeilConjectures and project lean/Sheaf found the existing
  projection-map mate/shift tools and the project's arrows/coherence modules.
  The upstream general mate tools do not include the specified finite-total rho or
  this four-coefficient pro-etale specialization. The actual existing projection
  definition and coherence tools are reused. Searching the upstream tree for this
  node id returned no declaration.
- LeanFinder: "Canonical pullback tensor comparison for ringed topoi determined on K
  flat representatives and pure tensors" returned eight ordinary module pullback/unit
  declarations, no pro-etale derived comparison with the required normalization.
- Searches of Mathlib, upstream, and lean/Sheaf for the delivered new names found no
  published duplicate. The existing DAG nodes for tensor comparison, exchange and
  exact projection mates are used, so no new notion node is introduced.
- During the original work, `scompile.py --source` found neither the ambient exchange
  nor exact-mate module published, and both were bundled. At this return repair, the
  current server source confirms that `Sheaf.Paper.ProjectionMateExact` is published
  and usable unchanged; its duplicate module and stale node record are removed. The
  published ambient exchange still needs its internal pullback comparison exposed,
  so that authorized dependency interface repair remains in this packet.

## Dependency modules

`def-weil-pbc-ambient-ringed-exchange`: the published module does not expose its internal
canonical pullback comparison, which this item needs to identify the two targets. The
delivered interface repair keeps the fully normalized canonical composition
selection, exposes `proEtaleAmbientRingedPullbackComparison`, and defines exchange as
its actual mate using the canonical derived adjunctions. Its coefficient HEq transport
moves the scheme arrow and coefficient identification together. All three definitions
have actual bodies. The selector retains every normalization predicate; it is not
choice from mere uncharacterized existence.

`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: the recorded arbitrary-small-site
canonical comparison equated the site's Hom universe with the coefficient and object
universe. The added interface uses the actual small pro-etale site. The existing
arbitrary-small-site interface remains publicly imported. The ordinary tensor comparison
is uniquely fixed by its naturality and equation on canonical adjunction-unit sections,
which locally generate inverse image and extension of scalars. Its inverse is totaled
using the existing signed `tensorPullbackTotal`; its derived natural isomorphism is
uniquely fixed by the square on every flat K-flat pair and the exact pullback
factorization. The helper `ProEtaleTensorModel` is the representative presentation of
this same tensor notion, not another tensor construction or new independent notion.

The previously bundled `lem-weil-pbc-ringed-projection-mate-exact` dependency module and
node copy have been removed from this delivery because the current landed declaration is
usable unchanged. The item retains its public import of `Sheaf.Paper.ProjectionMateExact`.

## Return repair (2026-10-15 UTC)

Return L for immutable head a1d377dcf160 concerned the stale Lean record for
`lem-weil-pbc-ringed-projection-mate-exact`. I read the current DAG record and fetched
`Sheaf.Paper.ProjectionMateExact` with `scompile.py --source`. Its declaration list and
complete theorem signature agree with the original delivery. Its proof docstring now
correctly distinguishes alpha evaluated at P[1] from the shifted component alpha_P[1].
The landed module supplies all of the required canonical shift, unit, exactness and
counit-mate data without an interface repair. Therefore this delivery now excludes both
its stale dependency JSON and its duplicate Lean module. ND's current record, statement
dependencies and reviewed metadata are preserved by using the published import.
The two remaining dependency repairs (pro-etale tensor universes and the exposed ambient
pullback comparison) are still needed and are retained. The item's Lean statement and
all its hypotheses and conclusions are unchanged. The earlier worker and second-reader
observations below describe the original packet; this repair supersedes their claim that
the exact-mate module is bundled or unpublished. The second reader will review this
repair independently before delivery.

Repair validation: all three remaining modules passed `scompile.py` with exit 0 and
no Lean errors or warnings. Both sandbox and library forms were checked separately.
The project signature reader confirms exact `lean.statement` matches, line widths at
most 100, and only `lean` changes in the three retained node copies. The compile log
is retained in `scratchpad/repair-compile.log`. The required delivery dry run follows.

## Earlier second reading (a previous round; superseded)

I read the item JSON, its blueprint source at order 1274, the five statement-dependency
nodes, all four delivered modules, and the actual dependency declarations. The local
literature is `/home/ubuntu/weil-launcher-nt/literature/`; the checkout's literature
sources are not installed. I read sites-cohomology.tex at 07A7
(remark-base-change), 0B56 (equation-projection-formula-map), 0944
(lemma-projection-formula), 0E48 (remark-compatible-with-diagram), 07A4
(lemma-pullback-tensor-product), and 0G7E (lemma-pullback-K-flat). In particular,
0E48 assumes a commutative square of **ringed** topoi and imposes no properness
or invertibility of exchange. The node makes its reduction packages explicit;
it does not assert globally strict-perfect representatives for all perfect objects.

The following is my inventory of the node, with its Lean counterpart and verdict.

| Node object, hypothesis, or conclusion | Lean counterpart and verdict |
| --- | --- |
| Small sites and commutative ring sheaves, ordinary uncompleted derived tensor | In `ringedProjectionFormula_operator_naturality`, `C D`, `JC JD`, `R S RI`, `SheafOfModules`, and `DerivedCategory` are exactly the arguments of the recorded arrows. `TR TS` are presented by signed total tensor on flat K-flat complexes through `PR PS hPR hPS rR rS`. Matches. |
| Ringed-topos morphism with module pullback given by inverse image and scalar extension | `uInv uPush adj`, finite-limit preservation, `I`, `c`, `uStar`, `hobj hmap` give that morphism and fix pullback on objects and maps. These are the recorded `AlgebraicInverseImage` and `changeOfRings`, not independent arbitrary operations. Matches. |
| Canonical derived adjunction, left derived pullback, right derived direct image | `LF epsilon hLF`, `V am RF eta hRF`, `computeL computeR`, `adjD canonicalAdj` are the arguments of the arrows declaration. `canonicalAdj` fixes the derived counit on K-injective representatives. These presentation data introduce no new geometric hypothesis. Matches. |
| Arbitrary derived K and Q; pi the adjunct of counit tensor identity after canonical tensor comparison | `derivedProjectionFormulaMate_naturality` treats arbitrary `E E'`, `Q`, and `q`, with the existing `derivedProjectionFormulaMate`. It is valid for every natural comparison `alpha`, hence includes the canonical one. In the scheme assertion, `proEtaleProjectionFormulaMate` inserts the actual `proEtaleRingDerivedAdjunction` and uniquely normalized `proEtaleCanonicalTensorComparison`. Matches. |
| Naturality in K for every morphism | The first theorem equates `pi E Q ≫ V.map (TS.map (q,id))` with `TR.map (V.map q,id) ≫ pi E' Q`. Composition is left to right. This is precisely the node's naturality square. Matches. |
| Bounded finite-projective Q_n with chosen strict-perfect packages | `F`, `P : StrictPerfectCoefficientPackage ... F`, and `hbounded` supply exactly the chosen bounded complex and degreewise finite-free retracts. `F` is arbitrary, so the assertion is pointwise in each n; no nonempty index type is needed. Matches. |
| K_n and induced phi_n | For the reduction object `Qn`, `TS.obj (E, LF.obj Qn)` is K_n and `TS.map (Prod.mkHom phi (𝟙 (LF.obj Qn)))` is phi_n. `E` is unrestricted and `K hK repE` merely presents it by a K-injective complex. Matches. |
| Pi_n and rho_n are those of the arrows definition | The `.1` and `.2` of each displayed `ringedProjectionFormulaArrows` are the actual pair. I opened its body: the first is the counit mate; the second is `eB.hom ≫ DerivedCategory.Q.map s ≫ eC.inv`, with `s` the specified finite-total inverse. Matches. |
| Optional specified representative isomorphism Q_n to a reduction object | `eQ : DerivedCategory.Q.obj F ≅ Qn` and `transportTensorProjectionArrows` transport both ends and both arrows using that isomorphism and `LF.map` of it. The forward arrow starts with tensor of `eQ.inv`, ends with `RF` of tensor of `LF.map eQ.hom`; the reverse uses the opposite directions. Matches. |
| First operator equation Rf(phi_n) pi_n = pi_n (Rf(phi) tensor 1) | First conjunct of `ringedProjectionFormula_operator_naturality`: `.1 ≫ RF.map (TS.map (phi,id)) = TR.map (RF.map phi,id) ≫ .1`. Setting E'=E and choosing the same representative gives every endomorphism in the node. Matches. |
| Second operator equation (Rf(phi) tensor 1) rho_n = rho_n Rf(phi_n) | Second conjunct: `.2 ≫ TR.map (RF.map phi,id) = RF.map (TS.map (phi,id)) ≫ .2`. With right-to-left mathematical notation this is precisely the displayed equation, with sides exchanged. Primed representatives also express the node proof's general inverse-naturality assertion. Matches. |
| Ambient R_Y-derived category, with restriction of scalars already made when necessary | Both sides use the same `TR TS LF RF`; `Qn` is an object in the ambient R-derived category. There is no assertion that an independently supplied scalar restriction is an equivalence. Matches. |
| Four schemes and Cartesian square with chosen fibre-product identification | `X' X Y' Y`, `g' f' f g`, `sq : ChosenCartesianSquare ...`. I read its inherited `CommSq`, `isoPullback`, `hom_fst`, and `hom_snd`. No geometric condition has been added. Matches. |
| Four small pro-etale coefficient sheaves and compatible inverse-image identifications | `RX RY RX' RY'`, `cf cg cg' cf'`, and `hcoeff`. The latter is HEq of the composite identifications and transports the coefficient isomorphism together with equality of composite scheme arrows. Matches the ambient exchange node. |
| Arbitrary unbounded K and Q on those sites | The final binders are the whole `DerivedCategory (proEtaleRingModules X RX)` and the analogous Y category. No boundedness, constructibility, completeness or constant-ring condition. Matches. |
| Canonical tensor operations at four corners | `aY aX aY' aX' : ProEtaleTensorModel ...` present the ordinary derived tensor by its actual signed total tensor on flat K-flat representatives. `proEtaleCanonicalTensorPullback` characterizes its comparison uniquely on every such pair. These are equivalent presentations of the specified operation. Matches. |
| First route: Lg(pi_f), then Ex at K tensor Lf Q | The left side starts with pullback `.map (proEtaleProjectionFormulaMate ...)`, then `proEtaleAmbientRingedExchange ... .app (aX.tensor.obj ...)`. Matches exactly. |
| Identification of its target | The last map is Rf' of the g' tensor comparison followed by tensor of identity with `proEtaleAmbientRingedPullbackComparison ... .inv.app Q`. Thus it first splits Lg'(K tensor Lf Q), then changes Lg'Lf Q into Lf'Lg Q. This checks the essential theta-inverse direction. Matches. |
| Second route: t_g, Ex_K tensor identity, pi_f' | The right side has those three factors in that order, with pi_f' evaluated at Lg'K and Lg Q. Same source and identified target as the first route; no IsIso assumption on Ex or pi. Matches. |

Dependency reading:

- `def-weil-pbc-projection-formula-arrows`: read `derivedProjectionFormulaMate`,
  `tensorAdjunctionTotalInverse` and the full `ringedProjectionFormulaArrows`
  signature and body, including its mixed-representative identifications. The
  theorem uses those exact arguments and actual maps. Read the totalization
  theorem as the proof source for the inverse cancellation.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: read the node and recorded
  `ringedTopoiCanonicalDerivedTensorPullback`, its unique K-flat formula,
  `CanonicalRingedTensorComparison` and its pure-tensor normalization. Its
  equal-universe interface cannot take the original pro-etale Hom universe.
  The delivered extension publicly imports it and states the same comparison
  at object universe u+1, Hom universe u, coefficient universe u+1. I checked
  `proEtaleTensorPair` against actual tensor sheafification, the ordinary unit
  equation in `proEtaleOrdinaryTensorPullback_existsUnique`, the inverse-total
  orientation, and the derived representative square. Both selectors choose
  characterized unique witnesses; neither chooses an arbitrary Nonempty map.
  The bilinearity and naturality helper theorems have source/proof docstrings.
- `def-weil-pbc-ambient-ringed-exchange`: read the node, the delivered module,
  `proEtaleRingDerivedPullbackComposition`, and the normalized module/derived
  adjunction definitions. The selector retains normalization of units, the
  direct-image section formula, conjugation, the degreewise map, and the
  K-flat equation. The square comparison then composes the inverse comparison
  for f',g, dependent equality transport, and the comparison for g',f.
  `mateEquiv` uses the correct f and f' canonical adjunctions. The current
  server module, obtained with `scompile.py --source`, now exists. Comparing
  it with the delivery shows the repair only extracts its internal comparison
  as `proEtaleAmbientRingedPullbackComparison` and reuses it in the mate.
- `lem-weil-pbc-ringed-projection-mate-exact`: read its node, the delivered
  statement, and `RingedTensorCorner`, `RingedTensorModel`, `RingedTensorEdge`
  and `.tensorComparison`. The statement asserts triangulatedness, canonical
  integer shifts on signed-total representatives, both tensor-comparison
  shift equations, unit compatibility, the natural transformation with
  components equal to the existing mate, shift commutation and a morphism
  of triangles with all three specified components, hence its connecting
  square. `MateCanonicalUnit` fixes multiplication on summands, rather than
  permitting arbitrary unitors. No theorem conclusion is assumed as an input.
- Read `RingedTensorSquare.projectionFirst`, `.exchangeFirst`, `.exchange`,
  `.derivedComparison` and `ringedExchangeTensorCoherence`; the delivered
  base-change equality has exactly their two routes, with the same final
  theta inverse. Its docstring also gives the representative/adjunction
  argument when using the original small-site universe presentation directly.

Independent searches: LeanFinder query "Compatibility of the projection morphism
with Beck Chevalley exchange and naturality of its inverse" gave eight
exponentiable-morphism evaluation/coevaluation identities, no exact match.
Loogle `"rightAdjointProjectionMap"` returned zero hits. LeanSearch for
"Compatibility of derived tensor projection and the canonical exchange map on
ringed topoi" was unavailable (Internal Server Error); no absence inference is
made from that. Prescribed Mathlib grep for projection/exchange/counit/base-change
combinations in CategoryTheory returned no hits. Direct rg in upstream
WeilConjectures and project lean/Sheaf found the actual projection mate tools,
the project's ringed coherence, and
`Etale.rightDerivedLowerStarProjectionMap_derivedBaseChangeMap`. I opened the
last declaration: it uses a single coefficient category on small **etale** sites,
not four arbitrary commutative ring sheaves on small pro-etale sites. Thus it is
not an exact existing match. I also read the pro-etale framework note and the
actual module-object derived tensor/ordinary projection APIs in the shared
clone. Their condensed-ring module-object categories or exceptional-adjunction
orientation do not identify this statement. Existing mate and tensor-total
constructions are reused. No independent missing notion or new DAG node is needed.

Edge cases: zero E, Q and phi; identity phi and identity square; empty schemes;
zero ring sheaves; zero complex F; free rank N_r=0; bounded complexes with empty
support (the bound does not require a≤b); degrees 0 and negative integers;
identity eQ, and nonidentity specified representative identifications. All remain
admitted by the binders. Reduction is pointwise, so an empty family is vacuous
and no characteristic or nonemptiness condition appears. The categorical
naturality theorem has independent object/Hom universes. The general reduction
statement retains the exact recorded arrows' chosen small-site universe; the
pro-etale theorem separately retains the genuine site's u+1/u universes and
coefficient/module values u+1, without forcing them equal.

Mismatches repaired in this reading: the ambient exchange dependency record
still claimed there was no Lean declaration and dropped newly landed
`reviewed_lean` metadata. I restored all non-Lean node fields from the current
read-only base and changed `lean.note` to describe the actual authorized §1(B)
interface repair: exposing the existing local canonical comparison needed by
the target identification. The original worker report is retained as history;
its "no record" observation is superseded by this current-server check.
No mathematical statement or Lean declaration required rewriting. There is no
statement_change and no target/unit statement change. Every delivered theorem
still has sorry as its whole proof; definitions have real data and all public
helper names are listed in their owning node's lean.declarations. All module
and declaration docstrings carry the source and appropriate blueprint id.

Record validation: the project signature reader reports an exact lean.statement match
for each of the four owning nodes; every Lean line is at most 100 characters.
First required scompile.py attempt failed in the server overlay with OSError 28
(No space left on device) while symlinking an unrelated dependency artifact.
This was infrastructure setup, not a Lean diagnostic; local disk and inode
space were checked and remain available. A full wrapper retry is in progress.

The full retry succeeded without any Lean error or warning. Required wrapper results:
ProEtaleCanonicalTensorPullback 14.1 s; ProjectionMateExact 11.5 s;
ProEtaleAmbientRingedExchange 13.5 s; ProjectionFormulaBaseChangeNaturality 9.7 s.
Each file was compiled separately with nice 19, two threads, and a 60-second limit.
The transient server-space failure therefore did not block validation.


## Earlier second reading (a previous round; superseded)

Independent reading of the returned packet, 2026-10-16. I read the sandbox node,
all three remaining modules, the five statement-dependency node records and actual
interfaces, the two proof-dependency modules, the blueprint at order 1274, and
sites-cohomology.tex at 07A7, 0B56, 0944, 0E48, 07A4 and 0G7E. The source assumes a
morphism, or commutative square, of ringed topoi, with unbounded module derived
categories and ordinary derived tensor. It adds no geometric finiteness condition.
In 0E48 the final vertical comparison first splits tensor and then changes the
composite pullback. This fixes the inverse direction of theta in this delivery.

Inventory of the node and its Lean rendering (each verdict is a match):

| Object, hypothesis or conclusion | Lean rendering and verdict |
| --- | --- |
| Small ringed sites with commutative coefficient sheaves | The reduction theorem binds C, D, JC, JD, R, S and RI, with the exact SheafOfModules categories of ringedProjectionFormulaArrows. The pro-etale assertion uses ProEt.topology and CommRingCat on each corner. Matches. |
| A morphism of ringed topoi | uInv, uPush, adj and PreservesFiniteLimits give its underlying geometric morphism; AlgebraicInverseImage I and c give its ring map. hobj and hmap specify inverse image followed by scalar extension on objects and maps. Matches. |
| Canonical derived adjunction and ordinary, uncompleted tensor | LF, epsilon, hLF, RF, eta, hRF, computeL, computeR, adjD and canonicalAdj are precisely the recorded arrows' derived presentations. PR, PS, hPR, hPS, TR, TS, rR, rS and k fix signed total tensor and its normalized comparison on flat K-flat representatives. Matches. |
| Arbitrary K and Q; pi the specified counit mate | derivedProjectionFormulaMate_naturality binds arbitrary E, E', Q and q, and uses the recorded derivedProjectionFormulaMate. The pro-etale helper instantiates it with proEtaleRingDerivedAdjunction and proEtaleCanonicalTensorComparison. Matches. |
| Naturality in K for every morphism | The first theorem states pi(E,Q) followed by V(q tensor identity) equals tensor(Vq,identity) followed by pi(E',Q). It is valid for every comparison presentation alpha and therefore includes the canonical one. Matches. |
| Chosen bounded finite-projective Q_n and strict-perfect packages | F, P : StrictPerfectCoefficientPackage ... F, and hbounded give the chosen bounded complex and its degreewise finite-free retracts. This is pointwise for each index; no index nonemptiness or global strict-perfect existence is asserted. Matches. |
| K_n and phi_n | TS.obj (E,LF.obj Qn) and TS.map (Prod.mkHom phi (identity on LF.obj Qn)) are respectively K_n and phi_n. E and E' are arbitrary; K,hK,repE and the primed data only choose K-injective presentations. Matches. |
| pi_n and rho_n from the arrows definition | The two components are exactly ringedProjectionFormulaArrows ... .1 and .2. I read its body: rho is eB.hom followed by DerivedCategory.Q.map s followed by eC.inv, where s is the specified finite-total inverse. Matches. |
| Specified representative Q_n isomorphic to a reduction object P_n | Qn and eQ : DerivedCategory.Q.obj F ≅ Qn supply the object and that exact identification. transportTensorProjectionArrows conjugates both arrows using eQ and LF.map eQ; identity eQ recovers the original arrows. Matches. |
| Both reduction equations in the ambient R_Y-derived category | The first conjunct is pi followed by RF(phi_n) = tensor(RF(phi),identity) followed by pi. The second is rho followed by tensor(RF(phi),identity) = RF(phi_n) followed by rho. Taking E'=E with the same presentation is exactly the two endomorphism equations in the node. All terms remain in the ambient derived category; any scalar restriction is part of the reduction object. Matches. |
| Cartesian scheme square with chosen identification | X',X,Y',Y, g',f',f,g and ChosenCartesianSquare bind all four arrows with the indicated domains. The structure includes CommSq and an isoPullback respecting both projections. Matches. |
| Four commutative ring coefficient sheaves and compatible inverse-image identifications | RX,RY,RX',RY' and cf,cg,cg',cf' have the correct corners and orientations. hcoeff is HEq of the two composite identifications; the exchange construction transports the scheme arrow and coefficient identification together. Matches. |
| Actual small pro-etale unbounded module derived categories | K and Q range over DerivedCategory (proEtaleRingModules ...). The four ProEtaleTensorModel arguments specify the same ordinary derived tensor by its flat K-flat representative isomorphism. There is no boundedness, completeness, constructibility or constant-ring hypothesis. Matches. |
| Canonical ambient exchange | proEtaleAmbientRingedExchange is mateEquiv of proEtaleAmbientRingedPullbackComparison with the actual two canonical derived adjunctions. It assumes no IsIso condition on exchange. Matches. |
| First base-change route | The left side applies Lg to the f projection mate, then exchange at K tensor LfQ. Matches. |
| Identification of the first target with the second target | The last left-side factor is Rf' of the g' tensor comparison followed by tensor(identity,theta.inv.app Q). Theta goes from Lf'Lg to Lg'Lf, so its inverse is exactly required here. Matches. |
| Second base-change route and equality | The right side is the g tensor comparison, then tensor(exchange at K,identity on LgQ), then the f' projection mate at Lg'K and LgQ. Both sides have the same source and identified target. Matches. |

Dependency review and the return repair:

- Read ChosenCartesianSquare, derivedProjectionFormulaMate, the full
  ringedProjectionFormulaArrows signature and body, and the totalization theorem.
  No similarly named pullback or independently supplied inverse is substituted.
- Read CanonicalRingedTensorComparison, its generalized pure-tensor and ordinary
  unit normalization, its signed total, and the recorded uniquely characterized
  derived comparison. The pro-etale extension publicly reexports that arbitrary-site
  interface and adds the actual u+1/u small-site instance. Its ordinary comparison
  is uniquely fixed by naturality and the canonical unit-section formula; its
  derived comparison is uniquely fixed by its equation on every flat K-flat pair.
  The selectors thus choose determined data. proEtaleTensorPair uses the existing
  sheaf tensor and sheafification. The total comparison uses the existing
  tensorPullbackTotal, in the inverse orientation required by 07A4. Matches H13.
- Read the ambient exchange node and module, proEtaleRingCompositeCoefficients,
  proEtaleRingDerivedPullbackComposition, actual module pullback/direct image,
  proEtaleRingModuleAdjunction_existsUnique and proEtaleRingDerivedAdjunction.
  The composition selector retains sectionwise unit normalization, the section
  formula for direct-image composition, its adjunction conjugate, the degreewise
  complex map and the K-flat factorization equation. Exposing its square comparison
  preserves this characterization and the original exchange signature. Matches H13.
- Fetched both ProjectionMateExact and ProEtaleAmbientRingedExchange using the
  prescribed scompile.py --source. The current exact-mate declaration agrees with
  the dependency record and is usable unchanged, including its corrected shift
  explanation and naturality clause. Its duplicate module and dependency record
  are absent from the repaired packet, as required by the return. The current
  exchange keeps the needed square comparison local, so the retained repair is
  still necessary. I checked the published source against the extracted comparison
  and its mate; no uncharacterized comparison has been introduced.
- Read RingedTensorSquare.exchange, projectionFirst, exchangeFirst and
  ringedExchangeTensorCoherence. Their route order and final theta inverse agree
  with this assertion. The proof docstring also gives the representative argument
  directly for the original small-site universe presentation.

Edge cases: arbitrary zero or identity morphisms phi, zero derived objects and
coefficient complexes, finite-free rank zero, bounded complexes with empty support,
empty schemes, zero ring sheaves, degree zero and negative degrees, identity square,
and identity or nonidentity specified eQ all remain admitted. There is no a≤b,
nonempty-index, characteristic, properness or scheme-flatness assumption. An empty
family is vacuous because the reduction assertion is pointwise. The categorical
naturality statement has independent object and Hom universes. The general arrows'
chosen small-site presentation is preserved; the pro-etale base-change theorem
retains site object universe u+1, Hom universe u and module values u+1, without
forcing these universes equal.

Independent searches in this reading:

- Prescribed LeanFinder: "Tensor projection counit morphism compatible with Beck
  Chevalley transformation and inverse naturality" returned eight adjunction,
  Frobenius and exponentiable-morphism results, with no full match.
- Prescribed Loogle: `"projection", "naturality"` returned zero hits.
- Prescribed LeanSearch: "Tensor projection map and Beck Chevalley exchange
  compatibility" returned Internal Server Error; recorded as unavailable.
- Prescribed grep: `Beck.Chevalley.*tensor|tensor.*Beck.Chevalley|projection.*exchange`
  returned zero hits. Direct rg of Mathlib CategoryTheory, upstream WeilConjectures,
  and the project's lean/Sheaf using projection, baseChange, counit, naturality and
  exchange found the existing mate tools and ringed coherence interfaces.
- Opened upstream Adjunction.ProjectionMap and ProjectionMapMate. The latter's
  map_rightAdjointProjectionMap_comp_mateEquiv assumes ComparisonCompatible;
  it is a general tool, not the canonical ringed-site assertion or the specified
  finite-total inverse equations. The existing rightAdjointProjectionMap is
  already reused by derivedProjectionFormulaMate. No complete existing match.
- Read coord/pefw-upstream-framework.md and the exact shared-clone
  ModuleObject/Derived/Tensor.lean. Its tensor is for internal modules over the
  condensed coefficient ring object, whereas this node uses arbitrary ring sheaves.
  It does not replace this node or the needed representative comparison interface.

Mismatches and changes in this reading: no further mathematical mismatch was found.
The removal of the obsolete exact-mate dependency delivery is correct. I retained
all three Lean modules and three node records unchanged and appended this current
second-reading audit. Compared every sandbox node with the current read-only base:
only lean differs. There are no new nodes and no statement_change; no unit statement
is changed. All theorem bodies are sorry, all definitions have real data, and the
postponed properties have owning blueprint docstrings and are listed in the owning
node's lean.declarations. The item docstrings carry all four proof steps. No variable
or universe is left implicit (all three modules disable autoImplicit).

Additional existing-match check: opened
Etale.rightDerivedLowerStarProjectionMap_derivedBaseChangeMap in upstream
LowerStarProjectionBaseChange.lean. Its categories are Sheaf X.smallEtaleTopology A
for a single monoidal abelian coefficient category A. It does not supply the four
arbitrary ring sheaves on small pro-etale sites or the specified finite-total rho.
Thus it is not an exact existing declaration for this node.

Static verification in this reading: tools/stage2_delivery.py check_lean_text returned
OK for all three modules and exact lean.statement signatures. Every Lean line is at
most 100 characters; the three modules contain respectively zero, three and five
sorry proof bodies, and no sorry data definition. Full wrapper compilation follows.

Current validation: required scompile.py completed with exit 0, no errors and no
warnings for all three remaining files, each separately with the required limits.
Both sandbox and library forms passed: exchange 30.5/28.4 seconds, tensor comparison
30.1/34.8 seconds, and main item 13.3/18.5 seconds. Preliminary dependency compiles
also passed. The required deliver2.py dry run and delivery are the remaining steps.

Delivery validation: deliver2.py --no-push printed OK (dry run), commit
ba9e38edad, passing preflight and compilation with nothing pushed.

## Repair of return L for immutable head 9395e1d9c052

The return identified one incomplete reviewer record: the independent review ended
with the exact-snapshot scompile reproduction still pending and no final verdict.
I read that complete review and preserved it verbatim at
`scratchpad/returned-independent-review.md`. Its SHA-256 is
`21243cb16d11889d61383d7bfa0de08b698e88f6870bdb34cae3beceb1682907`.
The mathematical findings in that review report no mismatch or required correction.
This section records repair-worker validation, not a newly claimed independent reading.

I verified every delivered Lean file against the actual stored objects of commit
`9395e1d9c052cbd310b09a490a7d9e097ff481d1`, without a Git command or a repository write.
All three Lean files and all three sandbox node copies are byte-for-byte identical
to that immutable head. The Lean blob identifiers are:

| Module basename | Immutable Git blob |
| --- | --- |
| ProEtaleAmbientRingedExchange | `b34a3139998d9d353d2a38d4c0269503ab9babf7` |
| ProEtaleCanonicalTensorPullback | `377121c92affa24e864962872d9e084ac2cca6c9` |
| ProjectionFormulaBaseChangeNaturality | `6b5f3d8f2ecd66d61e0ca6be9407def54807e920` |

The identity manifest, including SHA-256 hashes, is
`scratchpad/immutable-head-files.json`. The project `check_lean_text` check again
returns no failures for all three files, including their recorded signatures;
maximum line lengths are 91, 100 and 99. The static results are retained in
`scratchpad/return-L-static-validation.json`.

Exact-input reproduction command (all three sibling modules supplied):

```text
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q12 \
  lemma-weil-pbc-projection-formula-base-change-naturality \
  lean/Sheaf/AlgebraicGeometry/ProEtaleAmbientRingedExchange.lean \
  lean/Sheaf/Paper/ProEtaleCanonicalTensorPullback.lean \
  lean/Sheaf/Paper/ProjectionFormulaBaseChangeNaturality.lean
```

Completed attempt 1 result: exit status **255**, with no Lean result. The wrapper's
server-confirmation transport reported:

```text
mux_client_request_session: session request failed: Session open refused by peer
ControlSocket /home/ubuntu/.ssh/cm/slot7 already exists, disabling multiplexing
```

Log: `scratchpad/immutable-head-reproduction.log`. Verdict for this attempt:
**RETURN (tool transport failure; compiler validation was not established)**.
A separate prescribed `scompile.py --source Sheaf.Paper.ProjectionMateExact` check
returned exit 0 and the published module; its output is retained in
`scratchpad/transport-source-check.log`. No Lean or node change was made in this repair.

## Final compiler reproduction result and verdict

The exact snapshot reproduction has now completed successfully after the earlier
SSH transport failures. The required command was rerun with all three sibling
modules supplied:

```text
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q12 \
  lemma-weil-pbc-projection-formula-base-change-naturality \
  lean/Sheaf/AlgebraicGeometry/ProEtaleAmbientRingedExchange.lean \
  lean/Sheaf/Paper/ProEtaleCanonicalTensorPullback.lean \
  lean/Sheaf/Paper/ProjectionFormulaBaseChangeNaturality.lean
```

It exited 0. The wrapper compiled every transitive dependency and each supplied
file separately, with no error or unexpected warning:

```text
ProEtaleAmbientRingedExchange.lean: 13.4 s; nice 19; 2 threads; limit 60 s
ProEtaleCanonicalTensorPullback.lean: 14.5 s; nice 19; 2 threads; limit 60 s
ProjectionFormulaBaseChangeNaturality.lean: 10.3 s; nice 19; 2 threads; limit 60 s
```

The required dry run was also rerun:

```text
python3 /home/ubuntu/weil-launcher-nt/deliver2.py Q12 \
  lemma-weil-pbc-projection-formula-base-change-naturality --no-push
```

It exited 0 and printed `OK (dry run): commit d9466dd6a4 passes the preflight and
compiles; nothing pushed`. The only note says that the dependency's
`reviewed_proof` field differed and was not delivered because it is not ours to
change. This is expected and is not a failure.

The earlier failed attempts remain recorded above as historical transport
failures. They are superseded by the successful rerun. Final verdict for the
required revalidation: **PASS**. The worker is **READY**; no statement correction,
new DAG node, proof change, or push was needed.

## Second reading by Q12

Fresh independent second reading, 2026-10-16, of the current three-module packet.
I did not write these declarations. The preceding reports and reproduction records
are retained as history; this section records my own inspection and completed checks.

I read the full item node, all three sandbox modules, every statement-dependency
node and its actual declaration, the strict-perfect package, and both proof modules
(totalization and ringed exchange tensor coherence). I read the Stacks source in the
local `sites-cohomology.tex` copy at 0G7E, 07A4, 07A7, 0B56, 0944 and 0E48.
The surrounding sections assume morphisms or commutative squares of ringed topoi;
there is no ambient properness, Noetherian, constructibility or completeness assumption.
The source's final vertical path in 0E48 splits tensor before changing the composite
pullback, so the target identification here must use theta inverse.

My inventory, with the corresponding Lean and verdict:

| Node object, hypothesis or conclusion | Lean rendering and verdict |
| --- | --- |
| Small ringed sites and commutative ring sheaves | `C`, `D`, `JC`, `JD`, `R`, `S`, `RI` in the reduction theorem are exactly the sites and rings of `ringedProjectionFormulaArrows`. PASS. |
| A ringed-topos morphism, including its structure-ring map | `uInv`, `uPush`, `adj`, `PreservesFiniteLimits`, `AlgebraicInverseImage I`, and `c : RI ⟶ S`; `hobj` and `hmap` specify extension of scalars after inverse image on objects and maps. PASS. |
| Unbounded derived categories and canonical derived operations | `LF`, `epsilon`, `hLF`, `RF`, `eta`, `hRF`, `computeL`, `computeR`, `adjD`, `canonicalAdj` are the existing arrows' presentation; `canonicalAdj` fixes its counit using the ordinary module adjunction. PASS. |
| Ordinary uncompleted derived tensor and its canonical comparison | `TR`, `TS`, `PR`, `PS`, `hPR`, `hPS`, `rR`, `rS`, `k` retain the signed total on flat K-flat representatives and the ordinary pure-tensor normalization. PASS. |
| Arbitrary K and Q and the specified projection mate | `derivedProjectionFormulaMate_naturality` binds arbitrary `E E'`, `Q`, `q : E ⟶ E'` and uses the existing `derivedProjectionFormulaMate`. That definition is the uncurried upstream right-adjoint projection transformation, with the stated counit transpose. PASS. |
| Naturality in K for every morphism | The equality is pi followed by `V.map (TS.map (q,identity))` equal to `TR.map (V.map q,identity)` followed by pi. It applies to the canonical comparison and all endomorphisms. PASS. |
| Chosen bounded finite-projective coefficient complexes with strict-perfect packages | `F`, `P : StrictPerfectCoefficientPackage ... F`, and `hbounded` supply precisely bounded support and degreewise retracts of finite free modules. `P.N`, `P.i`, `P.p`, `P.splitting` have the recorded meanings. The assertion is pointwise in an arbitrary reduction index. PASS. |
| K_n and phi_n | The relevant object is `TS.obj (E,LF.obj Qn)` and its map is `TS.map (Prod.mkHom phi (𝟙 (LF.obj Qn)))`. The K-injective representatives `K`, `K'` with `repE`, `repE'` are presentations of arbitrary derived inputs. PASS. |
| The specified pi_n and finite-total rho_n | Both conjuncts use the two components of `ringedProjectionFormulaArrows`, with the full recorded arguments. Its second component is `eB.hom ≫ DerivedCategory.Q.map s ≫ eC.inv`, for its specified finite-total inverse `s`. It is not an arbitrary supplied inverse. PASS. |
| Optional specified Q_n isomorphic to a reduction object P_n | `Qn`, `eQ : DerivedCategory.Q.obj F ≅ Qn` and `transportTensorProjectionArrows` conjugate both arrows by this isomorphism and its `LF` image. Identity eQ includes the original equations. PASS. |
| Both displayed reduction equations in the ambient derived category | The first conjunct is pi then RF(phi_n) = tensor(RF(phi),identity) then pi; the second is rho then tensor(RF(phi),identity) = RF(phi_n) then rho. Specializing `E'=E` gives the stated operator equations. No change of ambient coefficients is hidden. PASS. |
| Cartesian square with its chosen identification | `sq : ChosenCartesianSquare g' f' f g` includes `CommSq`, `isoPullback`, `hom_fst`, `hom_snd`; the arrows' domains match the node. PASS. |
| Four pro-etale coefficient sheaves and compatible inverse-image identifications | `RX`, `RY`, `RX'`, `RY'`, `cf`, `cg`, `cg'`, `cf'` and `hcoeff` are precisely the ambient exchange arguments. The dependent transport includes both the composite scheme map and its ring identification. PASS. |
| Actual small pro-etale sites, canonical adjunctions and arbitrary K,Q | `ProEt.topology`, `proEtaleRingModules`, `proEtaleRingDerivedPullback`, `proEtaleRingDerivedDirectImage`, `proEtaleRingDerivedAdjunction`; K and Q range over the entire derived categories. The four `ProEtaleTensorModel` arguments present ordinary derived tensor. PASS. |
| First base-change route | The left side is `Lg.map (proEtaleProjectionFormulaMate f ...)` followed by `proEtaleAmbientRingedExchange.app` at K tensor LfQ. PASS. |
| Canonical target identification | The last left-side factor is Rf' applied to the g' tensor comparison followed by tensor(identity,`proEtaleAmbientRingedPullbackComparison.inv.app Q`). This is theta inverse, in the required direction. PASS. |
| Second route and equality | The right side is the g tensor comparison, then tensor(exchange at K,identity), then the f' projection mate at Lg'K and LgQ. Source and identified target coincide with the first route. No IsIso condition on exchange or projection is imposed. PASS. |

Dependency-module review (H13): I fetched the current published
`Sheaf.Paper.ProjectionMateExact` and
`Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange` through `scompile.py --source`.
They agree with the shared checkout (apart from the reader's final newline).
The published exact-mate module is usable unchanged and is only imported. The
exchange repair extracts the same formerly local canonical comparison and uses its
mate; its normalized composition selector retains the section formula, normalized
ordinary adjunctions, conjugation, degreewise map and flat K-flat factorization.
These determine its chosen data. The tensor repair publicly imports the recorded
arbitrary-site API and supplies the actual pro-etale universe instance. I checked
its ordinary tensor construction against sheafification, its comparison against the
unit sections and naturality, and its unique derived comparison against the explicit
flat K-flat representative square. The signed total reuses `tensorPullbackTotal`.
Neither repair substitutes a bare Nonempty isomorphism or an uncharacterized choice.
There are no new definition nodes to review. Both repairs remain necessary.

Edge cases: zero and identity phi, arbitrary maps between distinct K objects, zero
K and Q, zero coefficient complex, degree-zero coefficients, negative cochain
degrees, rank N_r=0, empty bounded support (no a≤b), zero ring sheaves, empty schemes,
identity square, and identity or nonidentity specified eQ are admitted. Empty
reduction families are vacuous since the equation is pointwise. There is no
characteristic restriction or nonempty-index hypothesis. Generic mate naturality
has independent object and Hom universes. The base-change statement keeps the real
pro-etale site object universe u+1 and Hom universe u, with coefficients/modules in
u+1; it imposes no equality of those site universes. The general reduction theorem
retains the recorded small-site presentation without adding a size hypothesis.

Independent existing-match searches in this reading:

- LeanFinder: `The mate of tensor with counit is natural in the object and compatible
  with a commutative square of pullbacks` returned eight general mate/monoidal
  adjunction declarations, including `mateEquiv`, `frobeniusMorphism_mate` and
  `Adjunction.map_μ_comp_counit_app_tensor`; no complete match.
- Loogle: `"projection", "mate"` returned zero hits.
- LeanSearch: `Naturality of tensor counit projection under base change` returned
  Internal Server Error; recorded as unavailable, not as absence evidence.
- Prescribed grep: `counit.*projection|projection.*counit|Beck.Chevalley.*tensor`
  found only the unrelated condensed discrete counit projection.
- Direct rg of Mathlib, upstream WeilConjectures and project Sheaf used
  `projection.*(naturality|base.?change)|mate.*tensor|exchange.*tensor|tensor.*exchange`
  and the proposed names. I opened upstream `Adjunction.ProjectionMap` and
  `ProjectionMapCompat`, and the complete
  `Etale.rightDerivedLowerStarProjectionMap_derivedBaseChangeMap`. The generic
  construction is already reused; its compatibility lemma assumes comparison
  compatibility. The etale theorem uses a single coefficient category on small
  etale sites, rather than four arbitrary ring sheaves on small pro-etale sites,
  and does not supply the specified finite-total inverse equations.
- I read `coord/pefw-upstream-framework.md` and the exact shared-clone
  `ModuleObject/Derived/Tensor.lean`: its module objects over a condensed coefficient
  ring are a different notion from the arbitrary ring-sheaf modules here.

Findings and changes: no mathematical mismatch or missing clause was found, so I
kept all three Lean modules and their recorded signatures unchanged. I restored the
tensor dependency node's stale `reviewed_proof` field from the current read-only
base; every sandbox node now differs from that base only in `lean`. There is no
statement_change, new DAG node, target/unit edit, or proved theorem. All eight
theorem bodies are sorry, all definition data are constructed, the 21 declarations
are listed in their owning lean records, and source/blueprint docstrings cover them.
The item docstrings retain the four node proof steps: transpose and counit
naturality; cancellation using totalization; identification of the canonical ringed
mates; and coherence with the explicit target identification.

Static validation: the project's `check_lean_text` returned no failures for all three
modules, including exact normalized `lean.statement` matches. Maximum line lengths
are 91 (exchange), 100 (tensor), and 99 (main item). Each module disables autoImplicit;
inspection found no unbound variable or universe or file-local notation/instance.

Completed compiler validation in this reading: the prescribed `scompile.py Q12`
invocation supplied all three sibling modules and exited 0 with no errors or
unexpected warnings. Each file was compiled separately at nice 19, two threads,
and the 60-second limit: exchange 14.2 s; tensor 14.9 s; main item 10.1 s. The
wrapper also checked its required dependency modules successfully.

Current second-reader verdict: PASS. Required dry run and delivery follow below.

Completed delivery dry run: `deliver2.py Q12
lemma-weil-pbc-projection-formula-base-change-naturality --no-push` exited 0 and
printed `OK (dry run): commit dbcb391f62 passes the preflight and compiles;
nothing pushed`. No warning or rejected field was reported. The completed
source/signature/compiler/preflight review verdict is PASS; delivery is authorized
by the second-reader brief.
