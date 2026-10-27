## Worker report

The module `Sheaf.Paper.RationalP1UnitCounit`, namespace
`AlgebraicGeometry.ProEtale.RationalP1`, constructs the specified diagonal
isomorphism, unit, and counit. `unitCounit` packages the two natural
transformations; `unitCounit_exact` states exactness and compatibility with
shifts. The triangle identities belong to the next node and are not asserted.
All postponed assertions are named theorems with source and proof docstrings.
All definition data are actual composites, restrictions, or uniquely normalized
comparisons.

Source read: the current blueprint main-20261015,
`sec-six-functors-basics/sk-prop-p1-adjunction-rational/`:
`sk-prop-p1-adjunction-rational-unit-counit.md`, together with the twelve proof
steps in this item's node. No statement correction is needed.

Hypotheses and clauses:

| Node text | Lean rendering |
| --- | --- |
| Prime ell | `l : ℕ`, `[Fact l.Prime]` |
| Field k, characteristic p > 0 | `k : Type u`, `[Field k]`, `p : ℕ`, `[Fact p.Prime]`, `[CharP k p]`; a field's positive characteristic is prime, so this adds no hypothesis |
| p differs from ell | `hpl : p ≠ l` |
| Y a k-scheme | `[Y.Over (Spec (.of k))]` |
| Separated finite type | `[IsSeparated (Y ↘ Spec (.of k))]`, `[LocallyOfFiniteType ...]`, `[QuasiCompact ...]` |
| A finite intermediate extension E or Qbar | `c : Option (PadicAlgCl.FiniteIntermediateField l)`; `some E` selects E and `none` selects Qbar |
| Actual condensed rings | `coefficient`: `Profinite.continuousMapRingObj E.1` or `Profinite.padicAlgClRingObj l`, never all continuous Qbar-valued functions |
| Pulled-back coefficient module categories | `DiagonalCoefficients.Modules (coefficient l c).X X`, i.e. internal modules over `condensedRingObj` |
| Ordinary unbounded derived categories | `DerivedCategory (Modules ... X)` |
| Dbc with finite constant local models | `constantModelBoundedConstructible ... X` from the recorded constructibility dependency |
| Loc(Dbc), full, replete, triangulated, all small ambient coproducts | `CategoryTheory.localizingClosure` of that exact object property and its `FullSubcategory` |
| P, W, q, p1, p2, Delta | `ProjectiveLine Y`, `diagonalSurface Y`, `ProjectiveLine Y ↘ Y`, `pullback.fst`, `pullback.snd`, `diagonalImmersion Y` |
| Fixed diagonal class and trace from the coefficient family | `family : DiagonalCoefficients.Family l Y`; `diagram l c Y family` selects its actual rational or closure diagram, retaining all compatibility fields |
| Clause 1 | `diagonalTensorMap` is the canonical left-factor closed projection mate, with the canonical Delta-p1 section comparison and coefficient unitor; `diagonalTensorIso` is its inverse and `diagonalTensorIso_naturality` states its square |
| M = Rp2 RDelta M | `pushSectionIso`, conjugate to the canonical derived pullback-composition/identity isomorphism |
| Tensor the specified diagonal class | `unitComponent` uses `diagonalTensorIso.hom`, then `1 ⊗ (supportedUnitIso.hom ≫ d.delta)` |
| Tate twist followed by [2] | `twist` tensors with `line l c X` placed in degree zero and then applies `shiftFunctor ... (2 : ℤ)`; `tensorShiftIso` is the standard tensor-shift comparison used in the composites |
| Last unit arrow is inverse canonical PBC | `square Y` is the actual pullback square; `condensedAmbientExchange ... (square Y)` is the published unit/comparison/counit exchange; `unitComponent` uses its inverse, after the inverse normalized Tate projection comparison |
| Unit's Loc restriction | `UnitCounitNormalized.unit` fixes each component to `unitComponent`; `unitInversions` supplies its required invertibility, with no arbitrary map input |
| Counit's projection isomorphism | `counitComponent` moves the shift through tensor and applies the inverse left-factor `traceProjection q K` with the shifted Tate line; this published map already incorporates the canonical tensor symmetries |
| Counit tensors the specified trace | `trace` transports `d.traceq` through `d.q_canonical`, retaining the diagram's full derived-unit normalization; `counitComponent` then uses `1 ⊗ trace`, the coefficient-unit comparison and the right unitor |
| Counit's Loc restriction | `UnitCounitNormalized.counit` fixes each component to `counitComponent`, using `counitInversion` |
| Naturality | `unitCounit_existsUnique` asserts that the component formulas give a unique pair of natural transformations; naturality is carried by each `NatTrans` |
| Exact functors and shift-compatible transformations | `unitCounit_exact` supplies inherited triangulations and shift structures and states `IsTriangulated` for both restrictions and their composites, and `NatTrans.CommShift` for both transformations |

`Family` is the given preceding-node class/trace datum, not a replacement of the
trace by an arbitrary morphism. Definitions are parametric in that family; the
family constructed by `diagonalTower_coefficients` is the intended application.
`adicComparison` similarly uses the existing root-normalized comparison with its
rational scalar-extension equation and Qbar finite-stage coprojection equations.
Those equations determine its map data. `linePullIso` uses a uniquely determined
linear lift with exactly its underlying abelian adjunct. No scalar automorphism
of the Tate line, exchange, or trace is left as input.

Dependency declarations used (recorded modules are imported):

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  the standing separated finite-type setting (`compactificationOverField`).
- `Sheaf.Paper.LocalizingAdmissibleCoefficients`:
  `CategoryTheory.localizingClosure`, through its public localizing-closure import.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `CondensedRing.moduleObjectDerivedPushforward`, `moduleObjectDerivedPullback`,
  `derivedUpperStarLowerStarAdjunction`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`:
  `CondensedRing.derivedTensor`, and its monoidal closed ambient category.
- `Sheaf.Paper.ProEtaleTateTwistsOfUniverses`:
  public underlying Tate constructions `spRationalTwist`, `spQbarTwist`,
  `SpInternalCartesian` from the recorded twist module, not a new Tate line.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `constantModelBoundedConstructible`, `IsConstantModelConstructible`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `ProjectiveLine`.
- `Sheaf.Paper.DiagonalTowerTrace`: the normalized source and integration trace
  retained by the coefficient diagrams.
- `Sheaf.Paper.DiagonalTowerCoefficients`: `DiagonalCoefficients.Family`,
  `Diagram`, `unit`, `source`, `diagonalSurface`, `diagonalImmersion` through
  its public coefficient-category/diagram imports.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing` convention.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClRingObj`, with the required finite-subextension condition.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `condensedRingObj`, `coefficientRing`.
- `Sheaf.Paper.CartesianCoefficients`: `CartesianAdicComparison`,
  `cartesianCoefficients` and the rational/Qbar Cartesian assertions.
- `Sheaf.Paper.CondensedAmbientExchange`: `condensedAmbientExchange` on the
  actual `ChosenCartesianSquare`.
- `Sheaf.Paper.RationalLocalizingProjectionFormula`:
  `moduleObjectProjectionMate`, and its normalized tensor-comparison mate.
- The canonical pullback identity/composition and exact single-degree
  comparisons use `CondensedRing.upperStarId`, `leftDerivedUpperStarComp`,
  `leftDerivedUpperStarIsoMapDerivedCategory`, and the existing derived
  `singleFunctor` comparisons. No derived functor is chosen again.
- All other proof-dependency modules of the node are imported for the proof
  obligations documented in the helpers; the proof sketches specify where the
  open-closed, proper image, PBC extension, field tensor and projection results
  enter.

Edge cases checked: Y need not be proper or smooth; empty and disconnected Y
are allowed. M and K need not be bounded; the hypotheses are exactly membership
in Loc of the finite-constant-model Dbc property. The Qbar case retains
finite-subextension-valued coefficients. The unit and counit have the correct
opposite composition order. The twist is positive one, the cohomological shift
is positive two, the exchange is inverted in the stated direction, and the
counit contains the trace rather than its inverse. Degree zero objects and zero
objects introduce no extra choices. No derived-completeness condition is added.
The finite extension is arbitrary; the Qbar branch introduces no auxiliary finite
extension.

Searches performed with `msearch.py NY det-prop-p1-adjunction-rational-unit-counit`:

- LeanFinder, “rational projective line diagonal class defines unit and trace
  defines counit on localizing constructible derived categories”: eight generic
  derived-category results, no exact construction.
- Loogle, `CategoryTheory.Adjunction.mkOfUnitCounit, AlgebraicGeometry.ProjectiveSpace`:
  zero results (the second queried name is not a Mathlib declaration).
- Mathlib grep, `p1Adjunction|rationalLocalizing|diagonal.*[Uu]nit` in
  CategoryTheory: no results.
- LeanSearch, “The canonical comparison for pullback of the rational Tate line
  over finite ell-adic fields and their algebraic closure is induced by roots
  of unity and scalar extension.”: eight unrelated results.
- Loogle, `CategoryTheory.Functor.mapDerivedCategorySingleFunctor, CategoryTheory.Adjunction`:
  no results.
- Mathlib grep, `Tate.*[Pp]ull|[Pp]ull.*Tate|rational.*[Tt]wist`:
  fourteen irrelevant textual matches (the case-insensitive regexp also
  matches parts of “statement”).
- `rg` of the upstream `lean/WeilConjectures` and `lean/Sheaf` for rational
  projective-line adjunction names, diagonal units and this exact item id:
  no existing statement of this item. The affine-space module contains general localizing-category abbreviations
  and the unshifted rational twist, but not these maps. Its independent
  unshifted functor is reused; no affine-space adjunction theorem is used. The finite-coefficient P1 adjunction has
  different coefficients.
- Blueprint search for rational Tate pullback and diagonal tensor comparison:
  the present item and coefficient conventions occur, but no separate
  construction states the rational unit/counit; the finite-coefficient
  projective-line statement is different.

No `STATEMENT-DISPUTED` finding. Compilation and preflight results are recorded
below after the final verification.

## Second reading by NY

The dispatcher explicitly starts one worker and prohibits starting other
agents; its brief assigns independent review to the maintainer. This section
records a second self-reading, not a claimed independent review.

I compared all three clauses again with the blueprint and the DAG statement.
This caught and corrected the twist/shift placement: `twist` now literally means
first tensor with the positive Tate line, then shift by two, and the displayed
composites use the canonical tensor-shift isomorphism. I also separated the
residue-field `IsUnit` proof from the inverse data, which are constructed by
`IsUnit.invertible`. The fixed coefficient diagram is preserved through the
full derived-unit normalization, and the base-change arrow is exactly the
published canonical exchange on the actual Cartesian square.

## New nodes

`def-sfb-projective-ambient-unit-counit-composites` owns
`Sheaf.Paper.RationalP1AmbientComposites`. For any commutative condensed ring,
any scheme Y, the actual module family L and coefficient diagram d, and the
specified p2 line comparison e, it defines the unit composite whenever the
specified exchange and twisted projection are invertible, and the counit
composite whenever its specified left projection is invertible. Every assumption
is an explicit binder (`hb`, `hp`, `e`); every displayed arrow occurs in the
normalization structures. `trace` retains the diagram's full-unit-normalized
derived direct image. `UnitComponentHom` and `CounitComponentHom` are the literal
ambient Hom types; their uniqueness lemmas fix each entire formula. The target
supplies the inversion proofs on Loc(Dbc), so these helper binders add no target
hypotheses. The source is clauses 2--3 before their localizing restriction.
Dedicated LeanFinder returned eight generic derived-adjunction/change-of-rings
results; Loogle returned twelve general adjunction/triangle results; Mathlib grep
returned five results about projective objects. None gives these projective-scheme
formulas. Blueprint search for ambient projective unit counit returned zero;
source searches found unrelated ambient transports and no such unit/counit.
The existing exchange owner `def-weil-pbc-ambient-ringed-exchange` supplies exactly
`CondensedRing.condensedAmbientExchange`, and is cited. This separate ambient
notion permits independent compilation of the formulas and their Loc restrictions.


`def-sfb-internal-diagonal-tensor-comparison` owns
`Sheaf.Paper.RationalP1DiagonalTensor`. For any commutative condensed coefficient,
any Y and any ordinary unbounded derived internal module M, it defines the
canonical diagonal tensor map using the published left-factor projection
`traceProjection`, the Delta-p1 section comparison and the coefficient right
unitor. The projection already contains the canonical Koszul symmetries. Its inverse and naturality square are included; the
supported source and Delta-p2 composition have the separate owner described
below. The tensor map is uniquely fixed by the full displayed composite,
with its invertibility proof postponed separately. The helper
reuses `def-sfb-proetale-projection-exchange-maps` and
`def-sfb-proetale-rational-localizing-projection-helpers`; it does not choose a
new braiding or projection map. The source is clause 1 and proof steps 6--8 of
the item. The broad DAG and blueprint searches found finite-coefficient P1
statements and generic projection interfaces, but no concrete normalized
diagonal map for these internal modules.

`def-sfb-rational-tate-pullback-comparison` owns
`Sheaf.Paper.RationalTatePullback`. Its index selects exactly a finite E or the
finite-subextension-valued closure. It uses the existing positive Tate modules,
selects the existing normalized root/scalar/coprojection comparison, lifts it
uniquely to a linear map by the fixed abelian adjunct, and applies the exact
single-degree and shift comparisons. Its general f assumes precisely residue
invertibility on source and target; the projective-line second projection over
k obtains these inverses from positive characteristic different from ell.
The structural maps of P and W over k are the explicit composites q and p2 q
with Y's structural map, so no extra universe, Over instance or invertibility
assumption enters the item's statement. Selecting `diagram` retains the whole
previously supplied coefficient diagram. This is proof steps 4 and 10 of the
source. The recorded Cartesian coefficient node supplies the normalized
abelian comparisons, but not this internal-module degree-zero linear lift and
shifted derived comparison. The exact searches are in the new record.

`def-sfb-tate-twisted-projection-comparison` owns
`Sheaf.Paper.TateTwistedProjection`. For a general scheme map, the actual
coefficient modules LS, LX and their specified shifted derived pullback
comparison e, it defines T as tensor with the degree-zero line followed by [2].
`twistProjectionMap` is the inverse tensor-shift identification, the existing
canonical projection mate with LS[2], then the image of identity tensor e and
the target tensor-shift identification. This is a general helper construction;
the item always supplies e from the preceding normalized Tate comparison.
The source is clause 2, proof step 10. The existing projection interface does
not itself insert this fixed Tate-line comparison and the shift identifications.

For the diagonal and twisted-projection helpers the actual new search queries
were: LeanSearch “The canonical diagonal tensor comparison for internal derived
modules is the closed projection mate; the Tate twisted projection comparison
is induced by the normalized Cartesian Tate line.” (eight generic, unrelated
hits); Loogle `CategoryTheory.Adjunction.rightAdjointProjectionMap` (zero,
unknown Mathlib identifier); Mathlib grep
`diagonalTensor|TateTwistedProjection|rightAdjointProjectionMap` (zero).
Source/DAG/blueprint searches located the existing generic projection, native
Koszul braiding and coefficient-family interfaces, which are reused. The
additional braiding search found the already-owned
`def-sfb-native-derived-koszul-braiding`, so no new braiding node is created.
The existing `traceProjection` encapsulates those exact Koszul symmetries;
the counit now directly inverts that left-factor projection. This is the same
canonical displayed projection formula without separately re-elaborating the
symmetries at each use.

The six added nodes define the concrete canonical comparisons needed by the
source, rather than supplying new assumptions. Each module has one owning node,
all its postponed theorems are listed in that node's Lean declarations and have
proof docstrings, and the item cites all six. Only `lean` and permitted added
statement dependencies of the original item are changed. No existing dependency
record is edited.

`def-sfb-projective-diagonal-composition` owns
`Sheaf.Paper.ProjectiveDiagonalComposition`. For any Y and commutative condensed
coefficient, `pushSectionIso` is the adjunction conjugate of the exact canonical
pullback section comparison for Delta and p2, and `supportedUnitIso` is the
published single-degree right-derived comparison for the exact closed direct
image. The exactness assertion is separately named with its open-closed proof.
This is the initial identification in clause 2, source proof steps 6 and 8.
It was separated from the diagonal tensor map so both files can be checked
within 60 seconds. The actual LeanSearch query about closed diagonal,
second projection and degree-zero supported image returned eight ordinary
pullback-diagonal results, including `pullback.diagonal_snd`, which is used.
Loogle `CategoryTheory.Functor.rightDerivedFunctor, AlgebraicGeometry.IsClosedImmersion`
returned no Mathlib result, and the recorded Mathlib grep returned zero. The
source search found an unrelated private kernel-adjoint `supportedUnitIso`;
there is no duplicate of the public comparison being delivered. The blueprint
search found twelve broad, different results. This new node uses the same
coefficient source and adds no hypothesis.

There are six new definition nodes in the final packet. The clause/hypothesis
mapping above also applies to their definitions, with the general helper
hypotheses specified in these six paragraphs. In particular the composition
and diagonal tensor helpers impose no boundedness or finite-type restriction;
the target still uses their stated restrictions to Loc(Dbc).

`def-sfb-projective-diagonal-pullback` owns
`Sheaf.Paper.ProjectiveDiagonalPullback`. It constructs the canonical identity,
morphism-equality and section comparisons of derived pullback, and the canonical
single regular-module/tensor-unit identification, for the actual internal-module
categories. The section equation is supplied as an equality and used through the
existing exact pullback comparison, with no chosen functor isomorphism. The source
is clause 1 and proof steps 7--8. The dedicated LeanFinder search returned eight
ordinary scheme-module pullback identities; Loogle returned six generic exact
functor identity results, including `mapDerivedCategoryIdIso`, which is reused.
Mathlib grep found zero hits. Project searches found the generic internal-module
composition comparison and finite-coefficient specializations; blueprint search
for diagonal pullback composition found zero nodes. This concrete normalized
section composite was absent. It was separated so the section interface compiles
independently of its tensor application.

The diagonal and twisted-projection modules give unique realizations of the fixed
published comparisons in the named wrapper interfaces. The assertions
`projection_existsUnique`, `projectionMate_existsUnique` and
`tensorShift_existsUnique` require heterogeneous equality with the actual
`traceProjection`, `moduleObjectProjectionMate` or canonical tensor-shift map.
Their proof docstrings describe reduction of the existing functor and monoidal
record projections, followed by uniqueness from equality to that fixed map.
The definitions select these unique realizations, so this is precisely the
permitted deferral of a proof that determines its data, rather than selection
from a mere existence theorem or from an unspecified isomorphism. The main
counit uses the same normalized left-factor projection consistently.

The native derived tensor and its existing two-variable shift comparison are also
bundled by `nativeTensorBundle` while the abelian monoidal category is abstract.
`internalTensorBundle` specializes this genuine construction to the recorded
internal-module category, and the public instances use its fixed fields. This
implements the shared-field approach explained in the upstream implementation
notes; it does not choose another tensor. The canonical single/quotient unit
isomorphism has the same unique fixed-map characterization in this shared
interface. The right projection realization is owned by the twisted-projection
module; the left projection realization is owned by the diagonal-composition
module. Both are used by the final composites through their normalized types.

`ProjectionMateFamily`, `ProjectionFamily`, `DiagonalTensorHom`,
`DiagonalTensorIsoType`, `DiagonalTensorFamily`, `DiagonalTensorIsoFamily`,
`TensorShiftFamily` and `TwistProjectionHom` are real
Type-valued definitions of the displayed Hom or isomorphism types. Their bodies
are the original formulas, with no postponed data. Naming them keeps concrete
monoidal instance proofs out of later declared types, as required by the upstream
implementation notes; it does not change any object, morphism, or assertion.

A final dedicated shifted-tensor search found the already-owned
`def-sfb-rational-localizing-twist`. Its declaration
`CondensedRing.rationalTwistFunctor` in `Sheaf.Targets.AffineSpaceRationalLine`
is exactly the unshifted fixed-line tensor functor. The delivered `twist` reuses
that definition and composes it with the shift by two. Its definition node is
cited; no affine-line adjunction theorem is used. The other hits
`spTwistFunctor` and the intrinsic rational twisting functors use sectionwise
modules or different rationalized categories, and the shifted affine-space
pullback includes an additional morphism. The dedicated LeanFinder query on
positive Tate tensor followed by shift returned eight generic Tor/tensor hits;
Loogle returned zero (curriedTensor was unknown there); Mathlib grep returned
eleven unrelated shift-text hits; blueprint search for Tate shifted tensor
functor returned zero. No additional definition node is needed for this search.

The diagonal map likewise uses `DiagonalTensorNormalized`: the complete formula
is written out in that predicate, and pointwise equality to the fixed composite
uniquely determines its data. The inverse family is uniquely characterized by its inverse being heterogeneously equal to
that fixed forward map, preserving exactly its inverse orientation.

The fixed-map normalizations state pointwise heterogeneous equality. The
diagonal inverse is uniquely fixed by requiring its inverse to be the forward
map. Some normalizations are proposition structures whose canonical fields carry
these equations; none adds data or a hypothesis. `twistProjection_existsUnique` similarly fixes the
entire displayed composite, including the specified line comparison.

The ambient unit and counit Hom types are also named. Their normalization
structures contain the complete formulas, with only the separately supplied
invertibility proofs inserted. The uniqueness lemmas fix those exact composites;
their definitions then select the determined morphisms. This is the same
permitted unique-object construction and does not assume the adjunction triangles.

`diagonalClassMap` in the ambient module names the inner diagonal tensor/class/shift
arrow before applying Rp2. `DiagonalClassNormalized.canonical` writes its full
formula; `diagonalClass_existsUnique` determines its data by that formula. The
notation `M ◁ f` is the existing tensor-left whiskering, namely identity tensor f,
so it renders exactly the source's `1 ⊗ delta` (and likewise identity tensor trace).
The settings disabling generated size and injectivity declarations follow the
existing coefficient-diagram module and change no mathematical declaration.

The pullback helper also names `firstProjection` and `secondProjection` with
exactly `diagonalSurface Y` as their domain. Their bodies are the actual pullback
projections. All delivered formulas and the specialized Tate pullback use those
same named projections, avoiding repeated comparison of the expanded pullback
scheme. No projection, Cartesian square, site or derived category is replaced.
The Tate comparison node cites this shared projective geometry interface.

The ambient module writes the same four-arrow unit paste, three-arrow diagonal
class formula and tensor-trace contraction using `assembleUnitFormula`,
`assembleDiagonalFormula`, `assembleCounitFormula` and `assembleTraceFormula`.
These are ordinary compositions defined in abstract categories, with every map
supplied by the recorded canonical constructions when specialized. The inverse
operations explicitly use the supplied IsIso proofs. Naming the typed projections
makes all these specializations use precisely the fixed diagonal-product category.

The final localizing interface names `UnitCounitType` in universe `u + 2`,
which is the universe of natural-transformation families over these categories.
`UnitCounitNormalized` requires componentwise equality to the prescribed ambient
formulas. Its existential binders supply only `IsIso` proofs for the fixed
exchange and projection maps; proof irrelevance makes the resulting inverse
independent of those witnesses. `unitCounit_existsUnique` determines the entire
pair of natural transformations, so choosing its unique pair introduces no
undetermined data. `localizingPreservation`, `unitInversions`,
`counitInversion`, `unitCounit_existsUnique` and `unitCounit_exact` are the
postponed well-definedness assertions of this node, with its proof steps in
their docstrings. Local irreducibility settings keep fixed derived constructions
folded during elaboration and do not alter their definitions or statements.

Final searches on resumption: LeanSearch, “Canonical derived pullback section
comparison for the diagonal of a projective line and its projection”, returned
eight generic pullback/diagonal hits (`pullbackComparison`, `toPullbackDiag`,
`diagonal_pullback_fst`, `pullback.diagonal` and related identities), with no
internal-module derived section comparison. LeanSearch, “The ambient unit and
counit of the rational projective line are composites of the diagonal class
proper base change projection formula and trace”, returned eight generic
Cartesian-category, coalgebra, restriction/coextension and GammaSpec counit
results, with no matching composite. These actual results are added to the
two corresponding definition-node search records. `tools/blueprint_refs.py
ancestor` confirms that this blueprint node is its own ancestor; its new nodes
have the empty `via` required for this root item.

Final validation (2026-10-22 UTC): `scompile.py` compiled all seven modules
separately, with no errors or unexpected warnings. The final module took
39.4 seconds under the sandbox name and 30.4 seconds under its library name;
each helper also stayed within 60 seconds. `deliver2.py ... --no-push`
reported `OK (dry run): commit 12c5531dcc3 passes the preflight and compiles`.
The initial preflight found only the new nodes' root `via` metadata and two
missing LeanSearch records; these were repaired and the dry run passed.
The stage-1 repair note for this item is resolved and requests the already
completed proof re-split, with no stage-2 interface defect outstanding.
