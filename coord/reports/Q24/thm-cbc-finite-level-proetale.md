## Worker report

The main module is `Sheaf.Paper.FiniteLevelProEtaleCompactSupportBaseChange`.
It constructs the specified transported compact-support exchange, then states its
invertibility and invariance under an isomorphic retained witness. Every theorem
introduced in this delivery has only `sorry` as its proof. All definitions have real
data. There are no new independent notions or new definition nodes.

Clause-by-clause rendering of thm-cbc-finite-level-proetale:

- The finite commutative coefficient ring is `Λ : Type (u + 1)` with `[CommRing Λ]`
  and `[Finite Λ]`. `[TopologicalSpace Λ] [DiscreteTopology Λ]` supplies precisely
  its discrete topology, as required by the recorded coefficient presentation.
- The four arbitrary schemes are `X Y X' Y' : Scheme.{u}`. The four arrows have
  their displayed source and target; `sq : IsPullback g' f' f g` is the Cartesian
  identification, not an unstructured commutativity equation.
- Separated finite type is `[IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f]`; these last two classes together mean finite type. There is no
  assumption on `g`, on either base scheme, or on a compactifying open immersion.
- The bounded-below object is `K : FiniteCoefficientDerivedCategoryPlus X Λ`, the
  recorded derived category of modules over the sheafified continuous-function ring.
  The retained witness is `W : EtaleOriginWitness X Λ K`, with the recorded `W.L`
  and `W.alpha`; it is not replaced by mere essential-image membership.
- `D : Etale.LocalCompactSupportExtension Λ` is the simultaneous construction data
  supplied by the missing prerequisite, stated here too. It records every comparison
  and normalization of that node. It is not an assumption about this square or K,
  nor an arbitrary map, nor an assumption of base change. The theorem applies to
  every such normalized system. Its existence is the prerequisite theorem
  `Etale.nonempty_localCompactSupportExtension`. No definition chooses data from a
  bare existence theorem. Keeping the system explicit also avoids a hollow choice
  of global compact support.
- `cbcTransportedCompactSupport Λ D f` is the actual composite `B_X ⋙ D.H f ⋙ A_Y`,
  where `A` is exact derived comparison and `B` is the recorded right derived
  comparison direct image. Thus both endpoints are defined before W is supplied.
- `cbcCoefficientPullbackComparison` is made from the canonical mate comparison and
  the unit of coefficient realization. `cbcDerivedPullbackComparison` applies it
  termwise to D-plus, with the existing composition identifications.
- `cbcComparisonUnitIso` is `asIso` of the unit of the recorded derived adjunction;
  its IsIso proof is exactly `siteComparison_boundedBelow`, not an abstract choice.
  `cbcCompactSupportComparison` is the image of this unit under `H_f` and `A_Y`.
- `finiteLevelCompactSupportExchange` is explicitly the seven-factor composite:
  inverse transport through alpha; inverse endpoint compact-support comparison;
  inverse pullback comparison; `A_Y'` of the specified etale exchange; forward
  compact-support comparison; forward pullback comparison; forward transport
  through alpha. These are exactly `P(alpha)^-1`, `S_L^-1`, `A(E_L)`, `T_L`,
  `Q(alpha)` in categorical composition order. No invertible substitute is chosen.
- Invertibility is `IsIso (finiteLevelCompactSupportExchange Λ D sq K W)`.
- The second conjunct quantifies over a second witness `W'` and `e : W.L ≅ W'.L`,
  with the exact equation `A.mapIso e ≪≫ W'.alpha = W.alpha`, then asserts equality
  of the two maps with the same endpoints. This retains the compatibility condition
  on the witness isomorphism, not just an isomorphism of underlying complexes.
- There is no constructibility, boundedness above, residue-characteristic condition,
  qcqs base, global compactification, or quasi-compact-open hypothesis on the square.

The missing prerequisite's full rendering is described under Dependency modules.
Its `comparison_refinement` uses the actual proper/open arrow of the recorded
notion, including non-Cartesian proper refinements. Its `exchange_compactification`
uses the actual upstream compactification exchange, not mere existence of a map.
Naturality is built into functors, natural isomorphisms and TwoSquare.natTrans.

Dependencies used in signatures and constructions:

- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange`:
  `Etale.derivedPlusFormalism`,
  `Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`, and
  `Etale.rightDerivedLowerShriekOfCompactificationPlus`.
- `WeilConjectures.Compactification.BaseChange` (reexported):
  `Compactification.ofIsPullback` and its specified pullback construction.
- `Sheaf.AlgebraicGeometry.ProperOpenComparison`: `Etale.properOpenComparison`.
- `Sheaf.Paper.EtaleOriginWitness`: `ProEtale.EtaleOriginWitness`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules` (reexported by the recorded
  intrinsic-comparison interface): `FiniteCoefficientDerivedCategoryPlus`,
  `finiteCoefficientComparison`, `finiteCoefficientRealization` and the actual
  continuous-function coefficient sheaf. The intrinsic module does not replace
  these categories in this theorem.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived`:
  `finiteCoefficientDirectImage`, `finiteCoefficientDerivedComparisonAdjunction`,
  `siteComparison_boundedBelow`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage`:
  `finiteCoefficientPullback`, its exactness instances and canonical inverse
  coefficient realization. This is the recorded operations node; no private copy.
- The delivered `CompactSupportComparisonPullbackCoherence` supplies
  `cbcComparisonCoefficientPullbackIso`; see its dependency repair below.
- Mathlib's `Functor.mapDerivedCategoryPlus`,
  `mapDerivedCategoryPlusCompIso`, `mapDerivedCategoryPlusNatIso`,
  `Functor.isoWhiskerLeft`, `Functor.isoWhiskerRight`, `IsPullback`, `IsIso`,
  `DerivedCategory.IsGE` and the standard coefficient categories.

The item's stmt_deps additionally cites the already landed operations, pullback
comparison and derived site comparison nodes used to construct its arrow. This
changes no mathematical statement. The main proof docstring follows all seven
original proof steps: affine Nagata, etale finite torsion, stalk conservativity,
proper/open comparison, global endpoint transport, and witness naturality.

Proof imports include the recorded derived-category, extension-by-zero,
finite-torsion, exact inverse-image, finite-level comparison, Nagata and
geometric-stalk modules. Three recorded legacy proof modules
`ProEtaleExtensionZeroComparison`, `ComparisonDirectImage`, and upstream
`ProEtale.BaseChange.SmoothBaseChange` import the legacy upper/lower-star definitions
and cannot coexist with the finite-coefficient API (duplicate notation declarations).
Their mathematical roles are recorded in the proof docstring; the present statement
uses the smaller finite-coefficient API and the repaired canonical pullback comparison.
They are not imported, to keep the delivered module usable.

Edge cases checked before writing: zero ring and zero complexes; empty X or Y;
identity square and identity replacement witness; disconnected and non-qcqs bases;
arbitrary g, including an open immersion that is not quasi-compact; arbitrarily low
cohomological lower bounds. No nonempty-scheme, characteristic, finite-generation,
or constructibility restriction appears. Coefficients and modules are in universe
u+1 over schemes in u, exactly as in the recorded coefficient categories. No site
object/morphism universe equality is imposed. All variables and universes are bound
explicitly with autoImplicit false.

Searches: msearch leanfinder, query "finite coefficient pro etale compact support
base change for bounded below complexes of etale origin": eight unrelated etale
scheme/ring hits, no theorem. msearch loogle query `"lowerShriek"`: zero hits.
msearch grep query `proetale|compactSupport.*baseChange` in AlgebraicGeometry:
ten basic site/proetale/ell-adic hits, no match. rg and node-id grep in the older
WeilConjectures source and rg in current lean/Sheaf found the dependency interfaces
but no arbitrary-base theorem. The 51-module framework was searched and the full
upstream `ProEtale.Derived.LowerShriekBaseChange` signature read: its theorem needs
a global compactification, so is not an existing match for this item. Its current
server source was checked using scompile --source. The blueprint node and unit were
read in full. The two Stacks tags attached to the extension do not by themselves
assert arbitrary-base ordinary-derived gluing; its docstring explicitly retains
the enhanced descent needed by the node's extension obligation. No statement dispute
or mathematical correction is asserted.

## Dependency modules

`lem-cbc-etale-local-compact-support-extension` had no Lean declaration on the base.
Server source lookup confirmed there was no module; the delivery branch
`deliver/Q39/lem-cbc-etale-local-compact-support-extension` was checked read-only
and contains a stage-1 split, not a Lean statement. The new module
`Sheaf.Paper.EtaleLocalCompactSupportExtension` states this existing node. Only its
lean record is changed. `LocalCompactSupportExtension` holds the simultaneous H_h,
restriction isomorphisms, q_c and actual proper/open refinement equation, same-bound
preservation, global exchange, open normalization, identity, and open-pasting
localization. Open-pasting gives the nested-restriction cocycle, and its two paths
around a restricted square give exchange's localization equation. The
compactification normalization, specialized to an open base change, together with
exchange_open is exactly compatibility of q_c with the canonical derived proper
open-restriction and degreewise open-extension restriction. The global exchange
normalization specialized to a compactification on an open chart is the node's
last displayed requirement. The structure uses H on all morphisms as an ambient
indexing convenience; properties and the main theorem use only separated finite-type
morphisms. It imposes no global compactification or condition on the bases.
`nonempty_localCompactSupportExtension` is the existence statement, with the full
construction proof plan in its docstring. It does not assert exchange invertibility.

`lem-weil-pbc-comparison-pullback` has a source-level canonical interface, but its
published compiled import closure brings in
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`. Compilation confirmed the
collision with `FiniteCoefficient.UpperLowerStar.Defs` used by the recorded
operations and derived comparison. Under (B),
`Sheaf.Paper.CompactSupportComparisonPullbackCoherence` states precisely the same
node against the finite-coefficient API. It retains the actual inclusion/base-change
isomorphism of sites, right-image section comparison, adjunction-conjugate inverse
image comparison, and all identity, arbitrary-composite and specified-Cartesian-square
equations, for sets, abelian groups and finite left module coefficients. It uses the
same source formulas with distinct declaration names prefixed cbc; no object or map
is selected by Nonempty. Only this dependency's lean record is changed. Its full
source and docstrings were read, as were the recorded declarations for its statement
dependencies.

## Validation

All files are compiled separately in dependency order by the authorized scompile
wrapper. The final delivery dry run is run with --no-push; the independent second
reading and actual delivery are left to the assigned second reader.

## Earlier second reading (a previous round; superseded)

I read the item and both dependency nodes independently against their Lean files,
then read the blueprint source at order 1648, Stacks more-etale.tex, section
`section-derived-lower-shriek-compactification`, especially
`lemma-shriek-well-defined` (0F7I) and `lemma-base-change-shriek` (0F7L), and
proetale.tex, `lemma-morphism-big-small` and the comparison inclusion preceding
`lemma-describe-pullback-from-etale`. The following is my object/hypothesis/conclusion
inventory, with its Lean match and verdict.

- Finite commutative discrete coefficient ring: `Λ : Type (u + 1)`, `[CommRing Λ]`,
  `[Finite Λ]`, `[TopologicalSpace Λ] [DiscreteTopology Λ]`. Correct. Discreteness
  fixes the topology and does not impose a characteristic or a nonzero-ring condition.
- Schemes and Cartesian square: `X Y X' Y' : Scheme.{u}`, the four morphisms, and
  `sq : IsPullback g' f' f g`. Correct. A pullback cone's universal property determines
  its projection-preserving comparison with the chosen fibre product. An ambient
  S-structure adds no restriction: every such square is a square over Y.
- Separated finite-type f: `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`.
  Correct, by the recorded scheme convention. There is no condition on g, no global
  compactification binder, and no qcqs assumption on Y or Y'. The base-changed f'
  has the same properties by stability under base change.
- Bounded-below pro-etale complex: `K : FiniteCoefficientDerivedCategoryPlus X Λ`.
  Correct. I opened ProEtaleFiniteModules: these are actual module sheaves over
  the sheafification of continuous functions on connected components, localized at
  quasi-isomorphisms, with the full cohomologically bounded-below subcategory.
- Retained etale origin: `W : EtaleOriginWitness X Λ K`. Correct. I opened its
  declaration: `W.L` lies in D-plus of etale ModuleCat sheaves, and `W.alpha` is the
  specified isomorphism from the derived finiteCoefficientComparison image to K.
  Neither finite generation nor constructibility is substituted for etale origin.
- Meaning over arbitrary bases: `D : Etale.LocalCompactSupportExtension Λ` records
  the simultaneous data whose existence is the prerequisite's conclusion. Correct.
  It supplies H and the prescribed exchange, without assuming exchange is invertible.
  Quantification over every normalized system is valid for this construction-data
  interface; its existence is stated in the delivered prerequisite. No functor is
  selected from a bare undetermined Nonempty theorem. H is indexed by all maps as
  ambient data; only separated finite-type maps have the stated properties and are
  used in this theorem. Extra indices may be filled by zero functors/zero arrows.
- Compact-support endpoints: `cbcTransportedCompactSupport Λ D f` is the actual
  `Rν_X,* ⋙ H_f ⋙ A_Y`. Correct. `cbcComparisonUnitIso` is the inverse-image
  adjunction's unit made invertible by `siteComparison_boundedBelow`; mapping it
  by H and A gives exactly C_f. I opened ProEtaleSiteComparisonDerived and checked
  its adjunction, direct image, theorem, and coefficient-realization definitions.
- Pullback endpoints: `cbcCoefficientPullbackComparison` and its derived version.
  Correct; see the compiled-interface diagnosis below. The comparison is the specified conjugate of
  restriction along the same fibre products, followed by the canonical realization
  unit. I opened the operations node's finiteCoefficientPullback definition: it is
  the recorded inverse realization, canonical fixed-ring pullback, then realization.
- Specified exchange: `finiteLevelCompactSupportExchange` has precisely source
  `g_p^* F_f K` and target `F_f' g_p'^* K`. Correct. Reading its seven factors in
  Lean composition order gives P(alpha)^-1, g_p^*(C_f)^-1, a_g^-1, A(E_L), C_f',
  F_f'(a_g'), Q(alpha). This is Q(alpha) composed with T_L A(E_L) S_L^-1 composed
  with P(alpha)^-1 in functional order, exactly the node's transported map.
- First conclusion: `IsIso (finiteLevelCompactSupportExchange Λ D sq K W)`.
  Correct, for every allowed K and retained witness, with no weaker existential
  assertion and no arbitrary replacement of the arrow by an isomorphism.
- Second conclusion: every `W'` and `e : W.L ≅ W'.L`, with
  `A.mapIso e ≪≫ W'.alpha = W.alpha`, give equality of the two actual exchange
  arrows. Correct. This is precisely an isomorphism of witnesses, retaining the
  compatibility with alpha, and both arrows have identical endpoints.

Dependency review: the local-extension dependency module is
`EtaleLocalCompactSupportExtension`. Its node is an existing genuine DAG prerequisite,
not a new definition node; its absent Lean interface is supplied under the human's
nothing-waits instruction. I read every field against that node. `H`, `restriction`
and `comparison` give the functors, r and q. `comparison_refinement` uses the actual
`properOpenComparison` for every proper w, including non-Cartesian refinements, and
`pfComp'` in the required direction. I opened ProperOpenComparison and its canonical
open-restriction, extension-by-zero and clopen-section composite. The field
`preserves_lower_bound` uses the same integer a on input and output. `exchange` is
an actual natural transformation, so its components are natural in L.
`exchange_open` identifies it with r. `restriction_identity` inserts the actual
pullback identity isomorphisms. Specializing `exchange_localization` to two open
squares gives the nested restriction cocycle; comparing its two decompositions of
an open-restricted arbitrary square gives the node's exchange localization equation.
`exchange_compactification` is the actual compactification exchange normalization,
using `rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`, whose current
server source I read with scompile --source. Specializing this equation to an open
square and using exchange_open is exactly compatibility of q with canonical proper
open restriction and degreewise extension-by-zero restriction. These encode every
clause of the prerequisite. Its theorem asserts existence of these data, not base
change invertibility. All remaining postponed theorems have matching node statements
and source/proof docstrings; all three theorem bodies are only sorry.

Source generality: Stacks 0F7I and 0F7L themselves assume qcqs schemes. The dependency
node explicitly says that extension to arbitrary bases is an additional construction
obligation. Its Lean theorem retains precisely that obligation and its docstring
explains the enhanced descent step; it does not claim the cited tags already prove
this generality. The main item's previously reviewed DAG proof repairs the blueprint's
unjustified global compactification choice by this local extension. No new statement
correction, target change, or statement dispute is needed here.

Edge cases: zero coefficient ring, zero K, empty schemes, identity square, identity
witness isomorphism, disconnected schemes, non-qcqs bases, and arbitrary non-qc open
g are all included by the binders. No index set, positive level n, invertibility of a
residue characteristic, or upper bound occurs. The lower cohomological bound may
be any integer. Scheme universe u and coefficient/module universe u+1 agree with
all recorded interfaces; no equality of site object and morphism universes or extra
smallness hypothesis is introduced. Every variable and universe is explicitly bound.

Independent searches: msearch LeanFinder query "base change compactly supported
cohomology finite coefficients pro etale bounded below etale origin" returned eight
unrelated condensed-module construction and affine-limit hits. Loogle query
`"shriek"` returned zero hits. LeanSearch query "compact support base change etale
proetale complexes" was unavailable (Internal Server Error). My rg searches for
`CompactSupportExtension`, `compactSupport.*[Bb]ase[Cc]hange`,
`isIso.*LowerShriek.*BaseChange`, the item's id, and its proposed declaration names
covered Mathlib, the older WeilConjectures source, current lean/Sheaf, and the exact
pro-etale framework. I opened the framework's
`isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_app`: it requires a
chosen global Compactification and hence is not this arbitrary-base theorem. The
condensed bounded-constructible theorem likewise uses different coefficients and a
compactification. No existing declaration matches the main item or its global local
extension prerequisite.

Compiled-interface mismatch investigated (H4/H13): the worker supplied
`CompactSupportComparisonPullbackCoherence` because the recorded module's compiled
closure collides with the finite-coefficient API. Reading the current side source with
`scompile.py --source Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence` and the
shared source initially suggested a usable existing match: both show the
finite-coefficient import and the same canonical construction. I tested that possibility
by importing the recorded module directly and using its
`comparisonCoefficientPullbackIso`. The authorized compile failed locally and then
failed again in the wrapper's current-server confirmation: importing the legacy
`ProEtale.UpperLowerStar.Defs` duplicates the notation declaration already loaded by
`FiniteCoefficient.UpperLowerStar.Defs`. Thus this is an actual unusable published
compiled interface, despite the side source's import. I restored the worker's
compatibility module and original main construction, and strengthened the dependency's
lean.note with this checked evidence. Every cbc-prefixed auxiliary is the same
Kan-extension, sheafification, fibre-product restriction or adjunction conjugate as the
recorded source. Its theorem includes the identity, arbitrary composite, and specified
Cartesian-square equations for sets, abelian sheaves and finite fixed-ring modules.
This is precisely a section 1(B) dependency repair; no unrelated notion or stronger
hypothesis is introduced. The worker's construction and statement needed no mathematical
change. No new nodes are introduced and no source-based statement correction is needed.

I checked all three delivered signatures verbatim against lean.statement, the 100-character
line limit, sources and blueprint docstrings, real data in every definition, and the
main proof docstring's coverage of the node's local Nagata, finite-torsion, proper/open
comparison, stalk detection, global transport and witness-independence steps. Final
compilation and the required dry-run/delivery checks are recorded by the wrappers.

## Repair of returned delivery (L, head 4a54b8527e6a)

The single return is a packaging refusal: the reviewer's `--apply-fixes` directory
contained the whole existing dependency node at
`dag/nodes/sec-proper-base-change/lem-weil-pbc-comparison-pullback.json`. The
stage-2 fix parser permits module replacements and the item's lean-record override,
not whole existing dependency nodes. A dependency's lean record instead belongs to
the ordinary stage-2 delivery.

Repair: the dependency's complete checked lean record is supplied in its sandbox
node through `deliver2.py`, and the report is updated here. No reviewer fix to that
node is needed to merge this delivery. If a report-only reviewer override is wanted,
the sandbox's `scratchpad/reviewer-fixes` directory supplies exactly the accepted
`thm-cbc-finite-level-proetale.report.md` filename; it contains no DAG node JSON.
Do not pass the whole worker sandbox to `--apply-fixes`.

I re-read the current recorded comparison module using `scompile.py --source` and
tried replacing the compatibility import by the recorded module and its
`comparisonCoefficientPullbackIso`. The local file compile still reports the
duplicate notation declaration caused by the legacy and finite-coefficient
`UpperLowerStar.Defs` import closures. The authorized wrapper confirmed the same failure against
current server artifacts as well. The delivered main file therefore retains the
canonical cbc-prefixed dependency repair, rather than the failed direct-import
trial. Its dependency lean.note now gives the exact failed import/declaration.
The theorem signature, mathematical node statement, endpoints, prescribed
conjugation, and witness-independence conclusion are unchanged.

Every delivered module is recompiled with the required wrapper, followed by
`deliver2.py Q24 thm-cbc-finite-level-proetale --no-push`. The fresh second reader
checks this repair and delivers it; this worker does not push.

Repair validation: the final three-module `scompile.py` run exited 0 with no
errors or warnings. Each file was checked separately in dependency order, including
its sandbox and library positions. The wrapper retained the default per-file limit.

## Second reading by Q24

This is a fresh independent reading of the repaired delivery. I opened the three
sandbox node records and all three Lean files, the corresponding base records,
the original blueprint theorem and section, and the original pullback-comparison
lemma. I read Stacks more-etale.tex, section-derived-lower-shriek-compactification,
lemma-shriek-well-defined (0F7I) and lemma-base-change-shriek (0F7L), and proetale.tex,
lemma-morphism-big-small and the comparison inclusion preceding
lemma-describe-pullback-from-etale. The two compact-support tags assume qcqs schemes;
the extension node expressly adds the arbitrary-base construction obligation. I
checked that the Lean retains this obligation instead of claiming those tags already
supply the unrestricted construction. There is no new statement correction in this
delivery: the item's mathematical statement equals the base statement.

My inventory of the item's objects, hypotheses and conclusions, with the matching
Lean and verdict, is as follows.

- Coefficients are a finite commutative ring: `Λ : Type (u + 1)`, `[CommRing Λ]`,
  `[Finite Λ]`. The topology binders `[TopologicalSpace Λ] [DiscreteTopology Λ]`
  give exactly its discrete topology. PASS; no nonzero or characteristic hypothesis.
- The four objects are arbitrary schemes: `X Y X' Y' : Scheme.{u}`. The four maps
  have exactly the sources and targets in the displayed square, and
  `sq : IsPullback g' f' f g` supplies its Cartesian universal property. PASS.
  I opened `ChosenCartesianSquare` and `Compactification.ofIsPullback`: a
  projection-preserving identification with the chosen product is unique, so using
  `IsPullback` here loses none of the specified Cartesian identification. An ambient
  S-scheme structure imposes no extra condition, since the square is a square over Y.
- The only vertical-map hypothesis is separated finite type:
  `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`. PASS. I checked the
  scheme-conventions node and Mathlib's property classes. The last two classes
  together mean finite type; neither a qcqs base nor a hypothesis on g is inserted.
  The base-changed f' inherits these properties, rather than requiring extra binders.
- The input is all of D-plus on the specified pro-etale module category:
  `K : FiniteCoefficientDerivedCategoryPlus X Λ`. PASS. I opened
  `ProEtaleFiniteModules` and the currently recorded `RefinementCoefficientRealization`:
  the coefficient sheaf really is the sheafification of continuous functions on
  connected components with quotient topology, and D-plus uses cohomological lower
  bounds. This is not restricted to bounded constructible or finite module sheaves.
- The retained witness is `W : EtaleOriginWitness X Λ K`. PASS. Its opened definition
  has the actual bounded-below etale object `W.L` and the specified isomorphism
  `W.alpha : A_X(W.L) ≅ K`, with A the recorded derived comparison.
- For arbitrary bases, the functors and exchange are those of the simultaneous
  normalized extension: `D : Etale.LocalCompactSupportExtension Λ`. PASS. The supplied
  prerequisite states its existence, while no definition chooses undetermined data
  from that existence theorem. The theorem is uniform in the specified system D.
  Indexing H and exchange on all morphisms is harmless ambient data: the constraints
  and the item's theorem use separated finite-type maps; unused maps admit zero
  functors and zero transformations.
- The compact-support endpoints are fixed independently of W:
  `cbcTransportedCompactSupport Λ D f` is `Rν_X,* ⋙ D.H f ⋙ A_Y`. PASS. I opened
  `finiteCoefficientDirectImage`, its derived adjunction and
  `siteComparison_boundedBelow`. `cbcComparisonUnitIso` uses precisely that
  adjunction's invertible unit, and `cbcCompactSupportComparison` maps it by H and A.
- Scheme inverse image is the canonical one:
  `(finiteCoefficientPullback Y Λ g).mapDerivedCategoryPlus`, and similarly for g'.
  PASS. I opened the recorded operations definition: inverse coefficient realization,
  fixed-ring inverse image along base change, then realization. The latter agrees
  with the inverse-image dependency's Kan extension and sheafification. I also opened
  the actual finite-coefficient framework's upperStar and adjunction. Its Grothendieck
  and sheafification instances are available for ModuleCat, not new hypotheses here.
- The actual arrow is `finiteLevelCompactSupportExchange Λ D sq K W`. PASS. Its
  successive factors are P(alpha)^-1, g_p^*(C_f)^-1, a_g^-1, A(E_L), C_f',
  F_f'(a_g'), Q(alpha), in Lean's categorical composition order. Hence the middle
  composite is exactly S_L^-1 followed by A(E_L) followed by T_L. Its endpoints are
  g_p^* F_f K and F_f' g_p'^* K, and its E is the specified extension exchange, not
  an arbitrary map with those endpoints. The derived pullback comparison is the
  sheaf comparison transported termwise with the canonical composition isomorphisms.
- The first conclusion is `IsIso (finiteLevelCompactSupportExchange Λ D sq K W)`.
  PASS; it concerns this arrow for every square, K and retained W allowed above.
- The second conclusion quantifies over every `W'` and `e : W.L ≅ W'.L`, assumes
  `A_X.mapIso e ≪≫ W'.alpha = W.alpha`, and equates the two actual exchange arrows.
  PASS; this is precisely replacement by an isomorphic witness, with compatibility
  of its specified alpha retained and with identical endpoints on both sides.

I read both dependency modules against their own nodes (there are no new nodes).
For `lem-cbc-etale-local-compact-support-extension`, H is the simultaneous family;
restriction is r; comparison is q. `comparison_refinement` uses the actual
`properOpenComparison`, which I opened through its section, clopen restriction,
extension-by-zero identification and counit; it also inserts the correctly directed
`pfComp'` inverse. This includes non-Cartesian proper refinements. The bound in
`preserves_lower_bound` is the very same integer a on both sides. `exchange` is a
natural transformation, `exchange_open` identifies open exchange with r, and
`restriction_identity` includes the actual inverse-image identity identifications.
Taking both horizontal maps open in `exchange_localization` gives r's nested-open
cocycle. Factoring an open-restricted arbitrary square in its two ways gives the
node's localization equation. `exchange_compactification` uses exactly the opened
`rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`. For an open base change,
this equation and `exchange_open` also identify restriction of q with the canonical
proper open-restriction and degreewise extension-by-zero comparisons. Thus all
clauses of the dependency are rendered. Its existence theorem does not assume or
assert exchange invertibility. The proof docstring explains enhanced descent rather
than asserting that arbitrary ordinary-derived morphisms glue uniquely.

For `lem-weil-pbc-comparison-pullback`, I opened all four statement dependencies and
the recorded comparison source, also retrieved by `scompile.py --source`. The
replacement builds exactly the same fibre-product restriction comparison and takes
its unit-normalized adjunction conjugate. It retains the identity, arbitrary
composition, and specified Cartesian-square equations for sets, abelian groups and
finite fixed-ring modules. Comparing its text after removing the cbc name prefix
shows only author, explicit-autoImplicit and line-wrap differences from the recorded
source. The source text currently names the finite-coefficient import; that alone
cannot establish that its published compiled closure is usable. I therefore made an
independent scratch import probe using the recorded module together with the required
finite-coefficient operations; its wrapper result is recorded below. The dependency's
lean record is part of the ordinary delivery, not a whole-node reviewer-fixes packet.
This addresses the returned packaging fault without editing any other node fields.

Edge cases: empty schemes, zero coefficient ring, zero complexes, identities,
isomorphic identity witnesses, disconnected bases and non-qcqs bases are admitted.
In particular g may be a non-quasi-compact open immersion. There is no index-set or
positive-level binder, no invertibility of a residue characteristic, and no upper
cohomological bound. Lower bounds range over all integers. The universe u of schemes
and u+1 of coefficients/modules follows the opened site interfaces, without equating
site object and morphism universes or adding independent smallness assumptions.
All universes and variables in the delivered files are explicitly bound.

Independent searches used msearch LeanFinder with “invertible exchange compactly
supported proetale cohomology finite ring etale origin arbitrary base scheme”: eight
hits about etale scheme morphisms and etale loci, no match. A first two-string Loogle
query was rejected by its parser; the valid query `"shriek"` returned no hits.
msearch grep `compactSupport|lowerShriek|LocalCompactSupportExtension` returned 25
unrelated topological-support hits. LeanSearch for “proetale compactly supported
derived base change finite coefficients” was unavailable (Internal Server Error).
My additional rg searches covered the full pinned Mathlib, older source
WeilConjectures, current lean/Sheaf, and exact current lean/WeilConjectures framework,
using compactSupport/baseChange, isIso/rightDerivedLowerShriek/BaseChange, the
extension's names, cbcComparison and the item's names. I opened the apparent upstream
match `isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_app`: it requires
an actual compactification c, so does not state this arbitrary-base construction or
theorem. The existing etale qcqs theorem and condensed bounded-constructible theorems
also have different domains/hypotheses. No usable existing match replaces this item.

No mathematical mismatch was found, and I left the three Lean files unchanged.
All definitions have real data and the only postponed results are the three named
theorems, each with its own matching DAG record and source/proof docstring. The main
proof docstring covers local Nagata, finite torsion, conservative stalk detection,
proper/open comparison, global conjugation and witness naturality. Each node's
lean.statement was checked verbatim against its theorem signature; all lines meet
the 100-character limit. The dependency records differ from base only in lean; the
item adds only the interfaces used by its construction to stmt_deps. My change is
this fresh second-reading report and its validation evidence.

The independent direct-import probe failed exactly as reported, both locally and in
current-server confirmation: importing
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs` finds
`AlgebraicGeometry.ProEtale.«term(_)_*[_]»` already declared by
`FiniteCoefficient.UpperLowerStar.Defs`. This confirms that the apparent existing
comparison is an unusable compiled interface for the required operations. The
cbc-prefixed section 1(B) repair is therefore necessary and is retained. The failed
probe is scratch material outside lean/ and is not part of the delivery.

Final independent validation: the required three-module `scompile.py Q24
thm-cbc-finite-level-proetale` run exited 0, with no errors or warnings. It compiled
both dependency modules and the main theorem separately, including sandbox and
library positions, without changing the default per-file limits. Printed elapsed
wrapper times include compiler-slot waits; they are not raised Lean timeouts.

The final `deliver2.py Q24 thm-cbc-finite-level-proetale --no-push` exited 0 and
printed `OK (dry run): commit 4f1a1dfe18 passes the preflight and compiles; nothing
pushed`. The prescribed final delivery follows with this report included.
