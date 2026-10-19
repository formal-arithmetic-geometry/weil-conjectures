## Worker report

Q73 states `lem-pur-compact-product-proper-support-compatibility`. The source is
blueprint main-20261015, sec-smooth-purity/sk-prop-an, projective-bundle-formula
proof, Step 1. The item's statement is unchanged. The main theorem is
`WeilConjectures.PurityFiniteSetting.compactProductProperSupportCompatibility`.
It asserts the conjunction of the explicitly quantified proper-support, twist,
and realization laws. All theorem proofs are postponed; definition data are real
compositions of canonical arrows, except normalized data extracted from their stated existence theorems.
The compact restriction and exterior families carry a proof equating every
component with its explicit real pullback-tensor/ordinary exterior composite.
Thus these are uniquely determined data, not arbitrary maps selected from a bare
existence or nonemptiness assertion. The closed-coefficient restriction is
similarly determined by its quotient normalization.

The finite coefficient datum is the existing `PurityFiniteSetting P`: its field,
prime different from the characteristic, finite coefficient extension and positive
quotient level are retained. The coefficient ring is exactly `P.Coefficient`, the
standard universe lift of the existing quotient. `CompactProductInput P X` is
`finiteTorConstructibleEtale P.coefficients.l P.extension P.level P.level_pos X`,
not a new notion of constructibility or Tor amplitude. Every scheme has universe
`u`, the coefficient module category has universe `u+1`, and both sites retain
their recorded sizes. The generic construction helpers bind all coefficient
category universes and structures explicitly.

Clause-by-clause rendering:

* Separated finite-type schemes: every law quantifies over explicit structure maps
  `f : X ⟶ Spec (.of P.field.k)` and `g : Y ⟶ Spec (.of P.field.k)` with
  `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact`. These explicit maps are
  necessary to retain the product projections and specified compactifications.
* Bounded constructible finite-Tor complexes: the `CompactProductInput` hypotheses
  on each etale input, or on each retained witness's `complex.obj`, impose exactly
  the recorded ordinary-site predicate. No flatness assumption on an individual
  complex, ramification-divisibility condition or chosen trivialization is added.
* The exterior product is the existing `Etale.externalProduct`, the tensor of the
  total-derived projection pullbacks. Maps between exterior products use the same
  derived tensor bifunctor.
* Compact supports: `compactProductSections C c` is `j_!` followed by derived global
  sections on the proper middle scheme. `compactProductDirectImageIso` is the
  canonical Leray isomorphism to the recorded
  `rightDerivedLowerShriekOfCompactification C c ⋙ rightDerivedGlobalSections C B`.
  The product compactification has the literal fibre-product middle scheme and
  the product of the two open maps.
* The named compact arrow `compactProductMap` is the ordinary absolute
  `ordinaryGlobalKunnethMap` on the zero extensions, followed by the inverse of
  `compactProductExtension`. This latter comparison is the adjoint of the inverse
  canonical restriction isomorphism; its data are not selected from a nonempty
  collection of possible comparisons. `CompactProductProperSupportLaws.kunneth`
  asserts its invertibility for every specified compactification and input.
* Naturality in both complexes is the equality in
  `CompactProductProperSupportLaws.naturality`, for arbitrary morphisms between
  admissible inputs, using the induced tensor map on the source and the actual
  external-product map on the target.
* Proper closed supports: `i`, `j` have `IsClosedImmersion` and
  `IsProper (i ≫ f)`, `IsProper (j ≫ g)`. Named helper theorems record that they are
  closed in each proper compactification and that their product support is proper.
* The actual map `u_Z` is `compactSupportFromProperSupport`. It applies
  `compactSupportClassImage` to the counit of the existing
  `supportedCoefficientDerivedAdjunction`. The unit is that support adjunction's
  unit followed by forgetting support in the compactification, which is precisely
  the constant-section unit on the closed support. The zero-extension coefficient
  identification is the open-adjunction mate of the quotient-normalized ordinary
  restriction isomorphism. Thus the formula is the unit/counit formula in the node.
* The description on every `H^a` is
  `CompactProductProperSupportLaws.supported_classes`: for every integer `a` and
  every morphism `C_i(A[0]) ⟶ K⟦a⟧`, its support-adjunction transpose followed by
  `u_Z` is exactly `compactSupportClassImage` of that morphism. The canonical
  exact-functor single comparison identifies `C_i(A[0])` with `i_*A_Z[0]`.
* The proper-support square is `CompactProductProperSupportLaws.proper_support`.
  Its upper arrow is the dependency's `supportedExteriorProduct`; its target
  support is exactly `supportedProductImmersion f g i j`; all three lower maps
  are the explicit unit/counit maps above. The equality is in the derived category
  of coefficient modules, before taking cohomology.
* Every bounded-below extension, with every specified restriction isomorphism, is
  retained in `CompactProductProperSupportLaws.excision`: `F : DerivedCategory.Plus`
  on the compactification and `e : D(j^*).obj F.obj ≅ K`. The assertion includes
  `IsIso (compactSupportExcisionMap ... F.obj e)`. The equality says exactly that
  `u_Z` followed by `compactSupportToExtension` is inverse excision followed by
  `compactProductForget`. The second arrow is the derived-global-sections image
  of the open-adjunction mate of `e.inv`, not an arbitrary extension arrow.
* For twists, `compactProductExteriorClass` uses the dependency's actual signed
  finite twists and their multiplication, the same coefficient tensor whose
  adjunct defines the supported exterior product, and the canonical shift
  comparison. It retains the source `C_h(A[0] ⊗ A[0])` and explicitly compares it
  with the ordinary supported unit by `compactProductClassSource`.
* Arbitrary closed supports are quantified in `CompactProductTwistLaws`; there is
  no properness hypothesis there. `support_identification` asserts invertibility
  of the canonical map `compactProductIntersectionMap` identifying the
  intersection of the two inverse-image supports with the product support.
* Degrees `a,b,r,s : ℤ` retain negative degrees and negative twists. Only `Even a`
  and `Even b` are required. The `etale` field compares the exterior class with
  the recorded pullbacks and supported cup; the `proetale` field states the exact
  transported equality on the pro-etale site. Both projections use the recorded
  `ChosenCartesianSquare` pullback interface. The change of support is along the
  actual projection-normalized intersection map.
* Specified pro-etale realizations are `FixedEtaleOriginWitness` values, retaining
  both `complex` and `iso`. `CompactProductRealizationLaws.compact_kunneth` uses
  these exact witnesses and any specified bounded-below etale representative of
  their exterior product. The comparison arrow is the finite global comparison
  on the zero extensions followed by the ordinary open mate and the same
  canonical exterior comparison used by `supportComparison_exterior`.
* `proper_support_comparison` states the comparison equality for `u_Z` and proves
  invertibility of its canonical supported comparison as part of the conclusion.
  `proper_support_square` states the square on the actual pro-etale supported
  exterior map, using the canonical output isomorphism, not a chosen product map.
  `witness_independence` retains two arbitrary specified antecedents and states
  equality of the transported proper-support arrows.

Dependency declarations used (all full signatures and docstrings were read):

* `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, its
  existing field/coefficient data and `Coefficient`.
* `Sheaf.Paper.FiniteTorAmplitudeSites`:
  `WeilConjectures.finiteTorConstructibleEtale`, the ordinary-site presentation of
  the recorded intrinsic finite-Tor predicate.
* `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`:
  `AlgebraicGeometry.Scheme.FixedEtaleOriginWitness` and its retained `complex`, `iso`.
* `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `Etale.rightDerivedLowerShriekOfCompactification`; the intrinsic compact-support
  dependency supplies its realization convention.
* `Sheaf.AlgebraicGeometry.SupportedExteriorProduct`: `Etale.supportedCoefficients`,
  `supportedCoefficientQuotient`, `supportedCoefficientDerivedAdjunction`,
  `supportedSectionsDerived`, `supportedCoefficientTensorDerived`,
  `supportedProductImmersion`, `supportedDerivedTensorMap`, `supportedExteriorProduct`.
* `Sheaf.AlgebraicGeometry.SupportSiteComparison`:
  `ProEtale.supportComparisonUnbounded`, `supportGlobalComparison`,
  `supportExteriorCoefficientIso`, and the generic `supportBifunctorIso`.
* `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`:
  `ProEtale.compactSupportSiteComparison`; its ordinary open mate is
  `ProEtale.openImmersionLowerShriekComparisonUpperStarIso`, also read in
  `Sheaf.Paper.ProEtaleProperOpenComparison`.
* `Sheaf.Paper.SupportedCup` and `SupportedCupFunctoriality`:
  `ProEtale.supportedCup`, `cupSingleTensorMap`, `cupTensorShiftIso`,
  `PurityFiniteSetting.FunctorialCupH`, `functorialCup`, `functorialCupPullback`,
  `functorialCupChangeSupport`, `functorialCupCompare`, `functorialCupTwist`,
  `functorialCupTwistProduct`, `functorialCupTwistPullback`, and the normalized
  `functorialCupComparisonSource_existsUnique`.
* `Sheaf.AlgebraicGeometry.OrdinaryKunnethFiniteRing`:
  `Etale.ordinaryGlobalKunnethMap` and its finite-ring isomorphism theorem.
* The upstream exact/derived inverse-image comparisons, open-adjunction unit,
  and Leray global-sections comparison supply all canonical transports.
  `ClosedSupportHom` and `Compactification.CategoryBaseChange` are proof imports.

Edge cases checked against the definitions and quantifiers: empty schemes and
empty closed supports introduce no nonemptiness assumptions; zero complexes and
zero morphisms remain admissible; the whole scheme as a proper support gives the
usual forget-support map; arbitrary nonproper closed supports remain allowed in
the twist clause. Arbitrary shifts, including negative even shifts, remain in the
statements. Signed twists are not replaced by natural powers. The positive finite
coefficient level excludes level zero exactly as in the conventions. No condition
that the ramification index divide the quotient level is imposed.

Searches: msearch LeanFinder for compactly supported etale Kunneth and proper-support
compatibility returned unrelated condensed/tensor facts; Loogle `compactSupport,
Kunneth` returned no match. Mathlib grep for compact exterior/Kunneth returned no
match, and searching the upstream source for this blueprint id returned no match.
A further joint LeanSearch for the four canonical construction interfaces returned
only compactly supported continuous-map facts; LeanFinder returned only extension
of functions/test-function facts; Loogle on the prospective names returned zero
hits. msearch grep and rg on Mathlib, upstream WeilConjectures, shared lean/Sheaf
and DAG nodes found none of the new interfaces. `blueprint_refs.py search` found no
blueprint node for these names. The already existing relative upstream Kunneth
nonempty-isomorphism statements do not specify the arrow, proper-support square,
excision or finite-site comparisons in this node, so they are not exact matches.

## New nodes

`def-pur-compact-product-arrows` owns `CompactProductArrows.lean`: product
compactifications, exact pullback comparisons, their canonical zero-extension
exterior mate and the compact exterior arrow built from the ordinary global arrow.
Its source is Step 1 of the same blueprint proof. Existing compact-support and
supported-exterior definitions are imported. The recorded searches found no
canonical compact arrow with this normalization.

`def-pur-proper-support-compact-maps` owns `ProperSupportCompactMaps.lean`: the
normalized closed-coefficient restriction, its zero-extension mate, the constant
unit, the counit-defined `u_Z`, and the canonical excision and extension arrows.
The closedness and zero-extension properties needed by these definitions are
named theorems with explicit proof plans and matching clauses in this definition
node. The source is the proper-support and excision paragraphs of Step 1. Searches
found no existing construction of this `u_Z` or its normalized excision interface.

`def-pur-compact-product-realization-arrows` owns
`CompactProductRealizationArrows.lean`: finite comparison maps and the canonical
transport of the compact and proper-support arrows under each retained witness.
The source is the last comparison clause of Step 1. It reuses the recorded finite
compact/support comparisons and their exact ordinary open mate. Searches found
no existing transport interface retaining these particular arrows and witnesses.

`def-pur-supported-exterior-class-arrows` owns
`SupportedExteriorClassArrows.lean`: representatives of the supported exterior
class, exact coefficient and shift comparisons, projection pullbacks, the actual
cup, and its site transport. Its source is the localized Kummer class paragraph
of Step 1; no new twist or cup definition is introduced. The searches found the
underlying operations but not this exterior-class comparison construction.

The latest saved law factoring adds four further definition nodes, all sourced from
Step 1 and belonging to unit `sk-prop-an`. These name universally quantified propositions;
they do not assume any of the desired identities.

`def-pur-compact-product-twist-laws` owns `CompactProductTwistLaws.lean`: the canonical
support identification and the ordinary/pro-etale twisted exterior-class equalities,
with arbitrary closed supports and even integer degrees. Its three fields are the
three corresponding proposition definitions.

`def-pur-compact-product-proper-support-laws` owns `CompactProductProperSupportLaws.lean`:
the five propositions for compact Kunneth, naturality, the proper-support square,
shifted supported classes, and excision for every bounded-below extension.

`def-pur-compact-product-realization-core-laws` owns `CompactProductRealizationCoreLaws.lean`:
the four separate propositions for output representatives, realization naturality,
compact Kunneth and proper-support comparison. Its primary declaration is the actual
output-representative proposition, not a nonexistent aggregate structure.

`def-pur-compact-product-realization-laws` owns `CompactProductRealizationLaws.lean`:
the remaining five propositions for the actual pro-etale square, unit/counit normalization,
shifted classes, arbitrary-extension excision and witness independence. Its structure
collects all nine propositions, including the four imported core definitions.

For each of these four nodes the resumed worker ran msearch LeanSearch with
`compact product proper support law proposition definitions` (eight unrelated topology
hits, beginning with `IsProperMap.prodMap`), and LeanFinder with
`compactProductProperSupportLaws CompactProductTwistLaws CompactProductRealizationLaws`
(eight unrelated topology/measure hits, beginning with `Pi.exists_compact_superset_iff`).
Their node records contain the actual returned declaration names. `rg` of those three
names in Mathlib, upstream WeilConjectures, shared lean/Sheaf and DAG found no hits;
`blueprint_refs.py search CompactProductProperSupportLaws` returned zero nodes.
Thus no existing proposition definition was found. The records now cite exactly the
notions used in their English statements.

`def-pur-supported-class-geometry` owns `SupportedClassGeometry.lean`: the
projection-normalized support maps, pulled cup, coefficient unit, coefficient
multiplication and supported representative conversions. It serves Step 1's
support geometry and reuses the existing supported-exterior and cup interfaces.
The recorded searches found no existing construction with these normalizations.

`def-pur-supported-exterior-shift` owns `SupportedExteriorShift.lean`: the
right-shift-first exterior shift comparison, first in generic shifted categories
and then on the existing projection-pullback derived tensor. It serves Step 1's
shifted representatives. The recorded searches found no matching interface.

`def-pur-supported-twist-pullback` owns `SupportedTwistPullback.lean`: the
exact/left-derived inverse-image and single comparisons followed by the actual
signed ordinary-etale twist pullback. It serves Step 1's projection pullbacks;
the recorded searches found no matching composite, and no twist is redefined.

`def-pur-supported-twist-degree-zero-product` owns
`SupportedTwistDegreeZeroProduct.lean`: the generic single/tensor comparison and
its specialization to the existing finite signed-twist multiplication at a
variable scheme. It serves the degree-zero part of Step 1's twist product.
The recorded searches found no existing interface for this composite.

`def-pur-supported-twist-multiplication` owns `SupportedTwistMultiplication.lean`:
the defining exterior-object equality and canonical multiplication after the two
projection pullbacks. Its generic helper retains the coefficient ring and positive
annihilator before specialization to the finite datum. It serves Step 1's exterior
twist identification; the recorded searches found no matching interface.

`def-pur-supported-class-site-comparison` owns `SupportedClassSiteComparison.lean`:
the exact finite-site comparison of shifted twist-valued classes and of their
supported coefficient-tensor source, with the normalized closed-constant
comparison. It serves Step 1's finite-site agreement. The recorded searches found
no existing interface with these specified source and target comparisons.

## Dependency modules

`def-pur-supported-cup`: the recorded module imported the finite-coefficient
`TensorResolution`, while the recorded supported-exterior/site-comparison chain
imports the legacy tensor module. Both upstream modules actually declare identical
`AlgebraicGeometry.ProEtale` tensor names (the first rejected name is
`laxMonoidal_Q`), so they cannot coexist in one Lean environment. The dependency
module changes its tensor import to the upstream legacy owner. All other contents
of the module, including actual cup data, normalization, shifts, all declarations
and statement signatures, are unchanged. Its node copy changes only `lean` and
records this import-only repair in `lean.note`.

`lem-pur-supported-cup-functoriality`: the resumed dry run timed out at 60 seconds
in the transitive `PurityFrameClass` import, both in the overlay and the server
confirmation. The current server source uses only `frameConstantPullback`,
`frameKummerEtale`, and `frameKummer`; all three are defined in
`Sheaf.Paper.PurityFrameKummer`. The dependency module changes the larger
`PurityFrameClass` import to this exact declaration owner. This avoids rebuilding unrelated frame-class constructions. A subsequent
profile located expensive kernel checks in the Kummer and site-comparison
composites. The repair therefore also factors Kummer into its same Ext class and
identity direct-image unitor, gives the existing exact comparison its explicit
selected-site endpoints, and factors its single/shift Hom composite through a
generic exact-functor helper. The three supported, ordinary and open comparison
maps use precisely their previous composites through that helper. All original
law fields and proof plans remain unchanged; no hypothesis is added. The named
helpers are included in the dependency record. Compilation validation follows.


## Second reading by Q73

The dispatcher explicitly forbids starting other agents. Accordingly this is a
second self-reading, not a claim of an independent worker's review; the maintainer's
independent delivery review remains necessary. Reading the source and node beside
the draft caught and repaired: accidentally assuming properness for the twist
supports; a general class-image clause instead of explicitly retaining every
integer cohomological degree; failing to retain the actual pro-etale exterior-map
square; and missing coefficient-source multiplication in the twisted class
comparison. The final statements explicitly retain each of these. The new nodes
only supply missing canonical constructions, and the supported-cup dependency
repair only changes the incompatible import.

The final rereading also retains naturality for arbitrary morphisms of the actual
pro-etale realizations. The output representative is concluded to exist. The
realization laws identify the transported proper-support arrow with the actual
pro-etale constant-unit/counit arrow, give the formula on every supported pro-etale
class, and state excision for every bounded-below pro-etale extension, with no
etale-origin assumption on that extension. The helper interfaces derive the
ambient Noetherian instances from finite type over the field and properness of
the compactification. The proper-support construction node owns both sites' maps;
it cites the already existing pro-etale supported-exterior node.


## Recovery self-check by Q73

The saved packet was retained and first checked with the required delivery dry run.
It passed the first two module compiles but timed out in
`compactProductExteriorWitness`. A separate diagnostic compile with a reduced
heartbeat budget located the expensive definitional equality at the second
pullback isomorphism. The repair uses the dependency's existing
`ProEtale.supportedExternalProduct_eq` before and after the tensor-bifunctor
isomorphism, and gives the helper its explicit source and target. These are the
same canonical tensor/exterior identifications already used by
`supportExteriorCoefficientIso`; the item statement and all its hypotheses are
unchanged. The dependency's named equality avoids unfolding the entire derived
monoidal structure during elaboration.

The self-check also found helper declarations omitted from `lean.declarations`
in the compact-arrow and proper-support construction nodes. Their records now
list every declaration of their modules, including the normalized-family
structures and existence statements and the pro-etale unit/counit interfaces.
All seven delivered modules respect the 100-character line limit. The original
source and clause-by-clause reading above remain applicable; no mathematical
statement correction was made.

The three compact/support/realization helper modules were then checked together
through `scompile.py`, each compiled separately in dependency order. All passed
without warnings; the repaired realization module compiled in 8.2 seconds.

The resumed recovery self-check on 2026-10-18 found two stale `lean.statement`
records: the compact map now has its named family type, and the exterior-class
map has an explicit return type. Both records were regenerated with the project
signature reader from the saved modules. No Lean declaration or node statement
changed in this metadata repair.

The second self-reading of the resumed packet checked that the functoriality
repair changes no mathematical data: its three frame references still
resolve to their original defining module, and the full supported pullback,
cup, signed twist, localization and comparison clauses are retained. The new
helper nodes and the main proper-support, excision, twist and witness clauses
were reread together; no additional statement mismatch was found.

The subsequent generic-helper profile still spent about 14 and 17 seconds checking
the supported and ordinary comparison targets. Two named equality obligations now
expose their existing defining normalizations: comparison of the signed etale
twist equals the pro-etale twist, and comparison of the etale coefficient unit
equals the pro-etale coefficient unit. Their proofs are postponed with complete
unfolding proof plans. The comparison maps use `eqToHom` of these object
equalities, so the transports are uniquely determined by equality and introduce
no choice of an isomorphism. These helpers belong to the same recorded finite
comparison notion and are listed in the dependency declaration record.

The next saved-packet defect was an invalid abbreviated body for
`compactProductExteriorClass`: it called cup with incompatible supports and
indices, whereas the node and docstring require the actual tensor exterior
representative. The original canonical composite retained in the saved
`ExteriorClassDiagnostic.lean` was restored, with its explicit coefficient-tensor
source and twist-sum target. The class comparison now also names the same
existing twist endpoint equality used in the repaired functoriality module.
No DAG statement was corrected: these repairs make the implementation state
exactly the already recorded notion.

The recovery dry run on 2026-10-18 reproduced the exterior-class timeout and
reported the development profiler warning. The profiler was removed. Its saved
trace also exposed an ill-typed support-change direction: change of support
requires the map from the intersection to the product support. The module now
constructs this reverse map directly from the pullback projections and records
its ambient-immersion equality as a named theorem with its proof plan. The new
construction node records both directions and that equality. The canonical
exterior shift comparison is factored through the generic coefficient category,
using the same tensor-bifunctor isomorphism and right-shift-first comparison;
this avoids expanding the finite coefficient datum in the derived tensor.
The main node's statement and hypotheses are unchanged.

The server confirmation additionally timed out in supported-cup functoriality.
The saved profile identified the Kummer Ext target check as another repeated
unfolding of the frame twist. The dependency repair now names the two defining
frame-twist equalities and transports the existing Kummer Ext elements through
them. Each equality has a source and complete unfolding proof plan and is listed
in the dependency's declarations. This is equality transport of the same Kummer
class; its law fields and all its quantified inputs remain unchanged.

The remaining exterior timeout was in the derived-tensor/monoidal notation
conversion seen in the saved shift profile. Its defining object equality is now
a named theorem, used by eqToHom at the two tensor-shift and twist-multiplication
interfaces. The new construction node explicitly records this equality and its
unfolding proof plan. Thus the tensor functor and the signed comparison remain
the existing ones, with no chosen tensor or additional assumption.

A focused current profile found the expensive Kummer Ext target check and the
shift composite. The former now uses generic Ext target equality transport;
the latter uses a composite in abstract categories before specializing the
canonical tensor, inverse-image and shift structures. Both generic helpers are
listed in their owning nodes. The reverse support map's pullback condition is
also a named theorem, with its projection-by-projection proof plan and an
explicit matching clause in its new construction node.

The next recovery self-reading found that the saved exterior-class body had again
been replaced by the cup side of the identity and referenced a later declaration.
The tensor-of-supported-morphisms composite from the saved diagnostic was restored;
this preserves the independent exterior construction required by the node.

The 2026-10-18 recovery dry run stopped in a published transitive dependency:
the server overlay could not find OrdinaryFiniteP1Arrows.olean. The source was
retrieved through scompile.py --source and an explicit, unmodified single-file
scompile.py compile of that published module passed (46.3 s sandbox, 37.8 s
library). The full packet dry run was then restarted with the restored exterior
construction. No project or launcher source was modified to address the artifact.

The final proof-docstring check replaces the stalk-only explanation for both
proper-support zero-extension comparisons by the explicit open cover consisting
of the compactifying open and the complement of the closed support. The map is
the normalized restriction isomorphism on the first and between zero objects on
the second. This also justifies the pro-etale version without appealing to
conservativity of geometric stalks for arbitrary pro-etale sheaves. No signature
or definition data changed.

## Previous tool blocker (2026-10-18)

The resumed full dry run again failed while compiling the published
OrdinaryFiniteP1Decomposition module, whose import of
Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows resolves to a nonexistent live
OrdinaryFiniteP1Arrows.olean. The preceding dry run hit the identical missing
artifact in OrdinarySupportedKummerSystem. The source-reading wrapper finds
the published source, and explicitly compiling that unchanged source through
scompile.py passed both its sandbox and library checks. Nevertheless the next
full dry run still resolved the import to the absent live artifact. Both
server-confirmation fallbacks then timed out rebuilding the unrelated published
Sheaf.Paper.DerivedPullbackTensorHom. The packet therefore has not reached
preflight or delivery. The two latest logs are resumed-current-dry-run.log and
published-dependency-compile.log. Launcher tools, published sources and build
artifacts were not edited. The restored exterior composite and proof-docstring
repair are retained for the next run.

## Resumed packet check (2026-10-18)

The required first dry run now resolves the published OrdinaryFiniteP1 artifacts.
It compiled CompactProductArrows (15.7 s), ProperSupportCompactMaps (10.5 s),
CompactProductRealizationArrows (10.2 s), SupportedCup (18.2 s), and
SupportedCupFunctoriality (48.4 s). SupportedExteriorClassArrows timed out at
60 seconds, as did the server confirmation. This is a definition-elaboration
defect being repaired, rather than the earlier missing-artifact tool failure.

The current packet self-check reread the source Step 1 and the main law fields
with all four construction modules. It confirmed explicit retained witnesses,
arbitrary closed supports in the twist identity, every integer shift, and
arbitrary bounded-below extensions for excision on both sites. The project
signature reader confirms all seven primary signatures and declaration lists
match the saved modules; all delivered lines are at most 100 characters and
there are no diagnostic commands or profiler options in those modules.

A reduced-heartbeat diagnostic found the two omitted pullback-map projection
reductions in compactProductIntersectionMap and expensive kernel conversions
in the finite twist pullback and exterior/site comparison composites. The
new diagnostic drafts factor those same composites through generic coefficient
objects and explicitly identify the existing supported coefficient unit with
the supported-Hom source. The draft validation is recorded below when complete.

The resumed exterior repair now makes the two pullback projection reductions
explicit. It factors supported pullback and the tensor-of-representatives
composite through `compactProductClassPullbackGeneric` and
`compactProductExteriorClassCore`, retaining the same coefficient tensor,
right-shift-first comparison and twist multiplication.
`compactProductTwistPullbackCore` and `compactProductTwistMultiplicationAt`
compose the same exact/left-derived and single comparisons before the product
scheme is substituted. `compactProductCompareTargetCore` performs the same
exact-functor shifted target transport in abstract abelian categories.

The named equality `compactProductCoefficientUnit_eq` is the direct-image
constant-unit defining equality, with its unfolding proof plan; its `eqToHom`
transports make the supported-Hom endpoints explicit. The construction node's
statement now records this equality and all helpers appear in its
`lean.declarations`. These changes preserve the canonical exterior construction,
its source multiplication and every item clause. The second self-reading
checked the new helper composites against the retained pre-repair module.
Validation of the repaired delivery follows below.

The next full dry run still timed out in exterior-arrow elaboration. The repair
uses the dependency's direct `functorialCupEtaleTwistProduct` and
`functorialCupEtaleTwistPullback`, exactly the false-site defining branches,
and the defining `compactProductExterior_eq` to spell out the source of twist
multiplication. `compactProductCompareSourceCore` composes the same three
comparison arrows before finite specialization. The new object equality has
its unfolding proof plan, and the construction node records both it and all
new helper names. Diagnostic profiler options remain only in scratch files;
the delivery uses the ordinary compiler and linter settings.

## Compilation partition (2026-10-18)

The resumed compiler reached `SupportedExteriorClassArrows` after all earlier
modules compiled. A bounded diagnostic located the remaining cost in kernel
conversion of the finite selected-site interfaces. The maps still elaborate to
the intended canonical composites, but checking all of them in one file exceeds
60 seconds. The construction is now partitioned into the following five additional
new definition nodes, each with its own module and recorded declarations. They
partition the previously searched exterior construction; their copied search
records are the actual searches already reported above, not invented new searches.
A fresh `rg` on upstream, the published side library and DAG found no declarations
named `compactProductTwistPullback`, `compactProductCompareClass`,
`SupportedExteriorShift` or `SupportedClassGeometry`.

`def-pur-supported-class-geometry` owns `SupportedClassGeometry.lean`. It defines
both projection-normalized support maps, the pulled cup, the actual coefficient
unit and multiplication, the supported class/source conversions and the exact
pullback of a supported morphism. Its statement includes the two needed projection
identities and the equality of the supported coefficient unit with the recorded
Hom source. This is the support geometry and representative-source portion of
Step 1; it imports the existing cup and support constructions.

`def-pur-supported-exterior-shift` owns `SupportedExteriorShift.lean`. It defines
the right-shift-first exterior shift comparison in generic shifted categories,
then specializes to the existing derived tensor and projection pullbacks. Its
statement includes the defining derived tensor object equality. This is Step 1's
external product of shifted representatives, with no extra parity restriction.

`def-pur-supported-twist-pullback` owns `SupportedTwistPullback.lean`. It composes
the exact/left-derived inverse-image comparison, exact single comparison and the
actual ordinary-etale signed twist pullback. This is Step 1's projection pullback
of the finite twists; the twist itself is the dependency's existing notion.

`def-pur-supported-twist-multiplication` owns `SupportedTwistMultiplication.lean`.
It applies the degree-zero tensor comparison and the actual finite twist
multiplication at a variable scheme, then composes the two canonical projection
pullbacks on the product. Its statement explicitly retains the defining equality
between the ordinary exterior object and its pullback-tensor presentation.

`def-pur-supported-class-site-comparison` owns
`SupportedClassSiteComparison.lean`. It defines exact site transport of a shifted
twist-valued class and of its supported tensor coefficient source, including the
existing normalized closed-constant comparison. This is the finite-site
comparison portion of Step 1, with generic exact-functor composites first.

The original `def-pur-supported-exterior-class-arrows` now imports these five
construction nodes and owns precisely the generic exterior representative and its
finite specialization. Its original declaration signature and mathematical data
are unchanged. Each new node is reachable through its statement dependencies;
every delivered module has exactly one owner. The item itself still has no
statement correction. The second self-reading checked each moved declaration
against its original text: only imports, its source-node marker and its owning
node changed, with all signatures and composites retained.

The first partition check compiled `SupportedClassGeometry` in 12.1 seconds,
`SupportedExteriorShift` in 5.4 seconds and `SupportedTwistPullback` in 11.0 seconds.
The combined twist-multiplication module still exceeded the default 60 seconds.
It is therefore further separated without changing any composite:
`def-pur-supported-twist-degree-zero-product` owns
`SupportedTwistDegreeZeroProduct.lean`, the generic single-functor tensor composite
and its finite specialization at a variable scheme. The product-scheme exterior
object equality and its canonical multiplication remain owned by
`def-pur-supported-twist-multiplication`. This additional node is the degree-zero
portion of the same searched construction and uses the same actual search records.
Its statement lists the exact generic and finite composites, and it is cited by
the product twist-multiplication node.

The separate site-comparison check passed both sandbox (20.1 seconds) and library
(17.7 seconds) compilation. The finite degree-zero multiplication still timed out
alone; changing the backward elaboration transparency setting did not resolve it.
The repair now forms the signed-twist specialization for a variable coefficient
ring, annihilator and scheme before applying it to `P.Coefficient`. It invokes the
dependency's same `functorialCupTwistProductGeneral` and the same generic tensor
composite. The finite wrapper merely supplies the actual annihilator, its positive
exponent proof, its annihilation proof and its invertibility on the scheme.
`SupportedTwistDegreeZeroProduct` then passed its private-overlay compilation.
The node records the additional generic helper and its exact parameters.

## Recovery validation (2026-10-18)

The required first dry run of the saved packet passed the first nine modules,
including the generic finite degree-zero multiplication (29.0 s), then timed out
in `SupportedTwistMultiplication`. The repair retains its public signature and
canonical composite. `compactProductTwistMultiplicationGeneral` now assembles
that same exterior-object equality, the two root-normalized projection pullbacks,
and the degree-zero twist product while the ring and positive annihilator remain
variable. The finite wrapper supplies the existing coefficient quotient, actual
annihilator, its annihilation proof, and the three source-implied unit proofs.
No hypothesis or conclusion of the item's statement changes, and the cup identity
remains a theorem conclusion. The helper and its construction are recorded in
`def-pur-supported-twist-multiplication`.

The self-check against the current blueprint Step 1 and saved law fields retains
all proper-support, shifted-class, arbitrary bounded-below extension, arbitrary
closed twist-support and retained-realization clauses. All thirteen primary
signatures and complete declaration lists match their modules, and every delivered
line is at most 100 characters. The realization definition's English statement
already cites both `lem-pur-support-site-comparison` and
`lem-sf-class-compact-support-comparison`, as required by the maintenance note.

The focused seven-module `scompile.py` validation passed without warnings.
`SupportedTwistMultiplication` passed both sandbox (34.2 s) and library (34.8 s)
checks, replacing the 60-second timeout with the same canonical construction.

The following full dry run validated all twelve construction modules, including
both paths for the canonical exterior class (18.0 s / 17.5 s). It then reached the
main compatibility file for the first time and timed out at its 60-second limit.
A scratch profiler with a reduced heartbeat budget is being used to locate the
remaining statement elaboration cost; it is not included in the delivered module.

The main-file profiler located repeated kernel checking of the large proposition
structures and their generated declarations: the twist bundle alone repeatedly
checked its full fields, and the proper-support bundle spent 14.3 seconds on
its initial kernel check before its generated declarations. The main module now
names each of its seventeen law clauses as a proposition definition and uses that
name as the corresponding structure field type. A whitespace-normalized comparison
against the saved pre-factoring main module verified every binder and every clause
body verbatim, and the main theorem signature is unchanged. The definitions are
recorded in the owning node's `lean.declarations`; they introduce no new input or
assertion. The helper modules and the main theorem respect the ordinary elaboration transparency setting
and contain no profiler option or changed heartbeat limit. The main module imports the four
helpers and retains exactly the original conjunction theorem signature.

The realization law packet was then split at the module boundary after the saved dry run
showed its single file exceeded the 60-second check: `CompactProductRealizationCoreLaws.lean`
contains output-representative, naturality, compact-Kunneth, and proper-support-comparison;
`CompactProductRealizationLaws.lean` imports it and contains the remaining proper-support-square,
unit/counit, supported-classes, excision, witness-independence definitions and the structure.
The five law bodies and all binders are copied verbatim from the saved main packet. This is an
elaboration-only partition; the item's theorem and every recorded declaration name are unchanged.

## Final resumed self-reading (2026-10-18)

The latest saved four-module factoring had incomplete metadata: the core node named
a structure never declared, all four nodes had the ancestor theorem in their unit
field, and the main node still listed declarations moved out of its module. These
records now name the actual declarations and unit; each module owns only its own
declarations. Added source docstrings to the law structures and module headers,
and restored the four-step natural-language proof plan for the main theorem.
Each new law node now spells out its quantifiers and clauses and cites exactly its
statement dependencies. All seventeen modules and the retained canonical exterior
construction were reread with the source Step 1. Properness remains confined to
proper-support clauses, every signed twist and even integer degree remains allowed,
output representatives are conclusions, and extensions and retained witnesses remain
arbitrary as specified. No statement correction or change of theorem signature was made.

The first resumed full dry run passed all twelve construction modules and both the
twist and ordinary proper-support law modules. The realization core then timed out.
The split had left its required finite-coefficient instance in the twist-law module
without importing it. The core now publicly imports that instance's actual owner.
This supplies the source-implied finiteness proof used by the existing comparison
API; it adds no assumption or mathematical dependence on a twist identity.

The two proof-only imports inherited from the former main file (closed-support Hom
and compactification refinement) now belong to the main theorem module, rather
than the definition-only law modules. The canonical construction imports remain.

The final import reading also points the three non-twist law modules directly at
SupportedClassGeometry, the owner of CompactProductInput and the coefficient unit.
Their new nodes cite that convention explicitly. Unused realization/proper-support
imports were removed from the twist law module, and the unused realization import
from the ordinary proper-support law module. No declaration body changed.

The reduced-heartbeat profiler isolated the remaining core timeout at the raw
projection-tensor map on the right side of realization naturality (isDefEq at
the second pulled-back morphism). The core now forms exactly that naturality
proposition with variable finite coefficient ring, base field and input predicate,
then specializes to P.Coefficient, P.field.k and P.CompactProductInput. Reverse
substitution in the generated draft recovers the original quantified clause body
verbatim. Only this implicated clause was factored; the other three core clauses
retain their bodies. The generic definition is listed in the owning node.
No map, equation, hypothesis or output assertion was added or removed. The profiler
and reduced heartbeat setting remain only in scratch files.

## Current packet self-check (2026-10-18)

The saved seventeen-module packet was retained and submitted first to the required
full delivery dry run. Rereading the current node and blueprint Step 1 alongside
the construction modules and all law clauses found no missing hypothesis or clause.
The exterior class remains the independent tensor-of-representatives construction;
the cup identity remains a conclusion. Properness is required for the support-to-compact
maps, while the twist supports remain arbitrary closed immersions. Integer shifts,
signed twists, both retained antecedent isomorphisms and arbitrary bounded-below
extensions on both sites are retained. Output representatives and support-comparison
invertibility remain conclusions of the laws.

The project declaration reader found no mismatch in any of the seventeen primary
signatures or complete declaration lists; every module is owned by exactly one
node and every delivered line is at most 100 characters. The two dependency repairs
retain their recorded mathematical interfaces. The main item keeps its original
statement, proof and proof dependencies, adding only the construction dependencies.
The generic realization-naturality definition has a scoped heartbeat budget of
2000000 and its existing elaboration-transparency setting; the enforced per-file
wall-clock limit remains 60 seconds. No compiler or launcher tool was modified.

The current full dry run first reached CompactProductProperSupportLaws, then the
primary compiler repeated its dependency checks. That repeated pass compiled
CompactProductArrows (14.4 s), ProperSupportCompactMaps (10.2 s), SupportedCup
(28.2 s), SupportedCupFunctoriality (42.3 s), SupportedClassGeometry (14.6 s) and
SupportedExteriorShift (7.6 s), then failed at SupportedTwistPullback's imports:
`Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition.olean` was absent from the
published live build. The required `scompile.py --source` lookup returned that
module's current source successfully. The wrapper started its server confirmation;
no source or tool workaround was attempted.

The server confirmation successfully rebuilt the published decomposition (50.2 s)
and frame Kummer module (49.7 s), then passed all twelve construction modules,
CompactProductTwistLaws (27.5 s) and CompactProductProperSupportLaws (6.9 s).
It reached CompactProductRealizationCoreLaws and timed out after 60 seconds.
The artifact issue therefore did not stop this confirmation; the current repair
focuses on the core law elaboration. A focused seven-module scratch profiler
uses the same six construction prerequisites and a reduced heartbeat budget.

## Current naturality interface repair (2026-10-18)

The required initial dry run passed fourteen modules, then confirmed the realization-core
timeout on both compilers. The saved explicit-interface candidate passed a focused
seven-file scompile check; its profiled core took 10.2 seconds. The installed repair
gives compactProductProMap its existing explicit source and target and names
compactProductProExternalMap, the same projection-tensor map conjugated by the
recorded supportedExternalProduct_eq endpoint equalities. Naturality uses this
map at the same endpoints. No quantified input, canonical arrow or equation changes.
The helper is owned and listed by def-pur-compact-product-realization-arrows.
The core now respects elaboration transparency; all profiler options and the
previous scoped two-million-heartbeat setting were removed from delivered code.
The constant coefficient instance remains derived from the positive finite quotient.

## Final preflight metadata repair (2026-10-18)

The required initial dry run completed compilation of all seventeen files and
reached server preflight. Its nine findings were metadata-only: a stray `a` in
one new node's statement dependencies (three findings), and six construction
nodes described later in the report rather than under `## New nodes`. Removed
the stray entry and placed those six descriptions in the required section.
Refreshed the functoriality dependency's non-lean fields from the current shared
node so this repair changes only its authorized `lean` field. No Lean source,
canonical construction, hypothesis or theorem conclusion changed in this repair.
