## Worker report

The module `Sheaf.AlgebraicGeometry.TraitFlatGroupSpaceClosure` states
`AlgebraicGeometry.AlgebraicSpace.exists_trait_flat_group_closure`, with its sole proof
`sorry`. Its auxiliary real predicate `HasTraitClosureCharts` spells out exactly the
localization-kernel affine-chart condition already present in the item. This is a helper
belonging to this theorem, not another algebraic-space, closed-subspace, group, or closure
construction. No new nodes, dependency repairs, or statement corrections are needed.

Hypothesis and conclusion correspondence:

- A DVR R: `R : Type u`, `[CommRing R]`, `[IsDomain R]`, `[IsDiscreteValuationRing R]`.
- pi generates its maximal ideal: `hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}`.
  This includes no independent nonzeroness assumption: the DVR maximal ideal is nonzero.
- Its fraction field K: `[Field K] [Algebra R K] [IsFractionRing R K]`.
- S is Spec R: every algebraic space and over-category has base `Spec (.of R)`.
- G is an algebraic space: `G : AlgebraicSpace (Spec (.of R))`, the existing fppf-sheaf
  full subcategory with representable diagonal and a surjective representable etale atlas.
- Natural multiplication, identity, inverse and group laws, without commutativity:
  `[GrpObj G.obj.obj]` on the underlying presheaf. Mathlib's cartesian functor-category
  structure makes its product pointwise. A group object in this category is precisely
  natural operations with the specified identities. No commutative-group class is used.
- Separatedness: `hsep` requires the diagonal `prod.lift (𝟙 G.obj.obj) (𝟙 G.obj.obj)`
  to be `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)`. Products in
  presheaves on Sch/S are relative products over S, so this is the required diagonal.
- Local finite type on etale scheme charts: `hlft` quantifies over `G.EtaleSite` and
  requires `LocallyOfFiniteType U.obj.left.hom` for each chart's structure morphism.
- A closed subspace with its full scheme structure: `∃ C : ClosedSubspace G`, using the
  recorded subobject definition and its representable-closed-immersion requirement.
- The chart formula: `HasTraitClosureCharts R π G C` quantifies over every R-algebra B
  and every representable etale chart from Spec B to G. The ideal is literally
  `RingHom.ker (algebraMap B (Localization.Away (algebraMap R B π)))`.
  Its quotient is the actual `Ideal.Quotient`, and the bottom/right arrows of the
  `IsPullback` square are respectively the chart and C's inclusion. The left projection
  is Yoneda of Spec of `Ideal.Quotient.mk`; its map to Spec R is the composite of this
  quotient projection with the structural map of Spec B. Thus the pullback is Spec(B/J),
  with the prescribed inclusion over the chart, rather than an unrelated isomorphic scheme.
  Every affine S-scheme admits exactly the R-algebra encoding of its structural morphism;
  all B and their algebra structures are quantified, including the zero algebra.
- Uniqueness as a closed subspace: the next conjunct quantifies over every
  `D : ClosedSubspace G` satisfying the chart formula and asserts `D = C`. It does not
  assume the other conclusions for D and does not choose a presentation up to an
  unspecified equivalence.
- Equality on the generic fibre: `IsIso (Functor.whiskerLeft (Over.map ...).op ...)`
  restricts the inclusion to all schemes over Spec K. The functor `Over.map` composes
  with the canonical `Spec.map` of `algebraMap R K`, so it gives exactly the generic
  base change of the represented fppf subfunctor, retaining its embedding.
- Restricted group operations: `∃ _ : GrpObj (C.val : AlgebraicSpace ...).obj.obj,
  IsMonHom C.val.arrow.hom.hom`. The inclusion preserves unit and multiplication;
  Mathlib's group-object inverse compatibility then makes inverse its restriction too.
  Together with the group structure this is exactly a subgroup space, with no assumption
  that the multiplication commutes.
- C is separated: the same representable closed-diagonal condition is asserted for C.
- C is flat, locally of finite type, and locally of finite presentation: a conjunction
  of `Flat`, `LocallyOfFiniteType`, and `LocallyOfFinitePresentation` for the structural
  map of every object of C's etale site. C is already an algebraic space by its subobject type.
- Every flat S-scheme T and every S-morphism T to G: the last clause binds
  `T : Over (Spec (.of R))`, `a : yoneda.obj T ⟶ G.obj.obj`, and `Flat T.hom`.
  It asserts `∃! l`, with `l ≫ C.val.arrow.hom.hom = a`. Yoneda maps are exactly
  S-morphisms; this quantifies over all flat T, with no quasi-compactness requirement.
- There is no hypothesis of quasi-compactness, reducedness, smoothness, or commutativity
  anywhere in the signature or helper.

Dependency declarations read and used:

- `def-sc-discrete-valuation-ring`: Mathlib.RingTheory.DiscreteValuationRing.Basic,
  `IsDiscreteValuationRing`; its definition extends local and principal ideal ring
  structures and requires the maximal ideal to be nonzero. Its recorded
  `irreducible_iff_uniformizer` explains the equivalent generator convention, although
  the statement uses the explicit equality of ideals.
- `def-weil-affine-spectrum`: Mathlib.AlgebraicGeometry.Scheme,
  `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`.
- `def-trf-algebraic-space`: Sheaf.AlgebraicGeometry.AlgebraicSpace,
  `AlgebraicGeometry.AlgebraicSpace`, `.IsRepresentableWith`, `.IsEtale`, `.EtaleSite`.
  The imported ClosedSubspace module publicly exposes this dependency.
- `def-weil-closed-immersion`: Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion,
  `AlgebraicGeometry.IsClosedImmersion`, publicly imported by ClosedSubspace.
- `def-weil-finite-type-morphism`: Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  `AlgebraicGeometry.LocallyOfFiniteType`; the quasi-compact predicate is deliberately
  not a hypothesis, since the item only assumes local finite type.
- `def-weil-flat-morphism`: Mathlib.AlgebraicGeometry.Morphisms.Flat,
  `AlgebraicGeometry.Flat`, with its affine-local condition equivalent to stalkwise flatness.
- `def-sbc-locally-finite-presentation`: Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation,
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-sfb-space-closed-subspace`: Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace,
  `AlgebraicGeometry.AlgebraicSpace.ClosedSubspace`. Its `val.arrow` is the actual
  inclusion of the subobject, and equality identifies isomorphic presentations over G.

The additional Mathlib notions are existing `GrpObj` and `IsMonHom` from
Mathlib.CategoryTheory.Monoidal.Grp and its public imports, the pointwise cartesian
structure from Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory,
`Localization.Away`, `RingHom.ker`, `Ideal.Quotient.mk`, `IsPullback`,
`Functor.whiskerLeft`, and `Over.map`. No separate group-algebraic-space definition is needed.

The plain proof imports expose every currently recorded proof dependency's module:
AlgebraicSpaceIdealClosedSubspaceCorrespondence, SchemeZariskiEtaleQuasiCoherentEquivalence,
ChartwiseEtalePermanence, AlgebraicSpaceFibreProductsEtaleCovers, Mathlib Flat.TorsionFree,
Pullbacks, and Noetherian. Other proof dependencies' definition modules are already public
imports. The three proof nodes `lem-sfb-space-qcoh-cartesian-chart-family`,
`lem-trf-supported-kernel-flat-pullback`, and `lem-trf-supported-sections-quasi-coherent`
have no Lean record or Mathlib match on the read base, so have no module to import.
They are proof inputs, not missing objects needed to type this statement. The theorem's
nine-step proof docstring records them and every remaining proof step for stage 3.

Edge cases checked before writing: the zero affine chart is allowed and localization
and quotient still make sense; the empty flat test scheme is included; nonreduced
and nonflat G are permitted, including nonzero pi-power torsion in its chart rings;
if G is already flat, the chart kernels vanish and C is G; noncommutative group laws
are permitted; arbitrary characteristics and non-quasi-compact groups or test schemes
are included. No independent smaller universe makes the chart or test quantification
vacuous: R, K, chart rings, and schemes use the same universe u of the existing space
framework. The fraction-field and uniformizer data exclude a field base or pi=0 through
the existing DVR conditions, not through an added assumption.

Searches (msearch.py, group Q76, this item):

- leanfinder: "The generic fibre closure of a locally finite type group algebraic space
  over a discrete valuation ring is a flat closed subgroup". Eight hits on scheme
  finite type, flatness, and valuation rings; no algebraic-space horizontal closure theorem.
- leansearch: "The schematic closure of the generic fibre of a group algebraic space
  over a DVR is flat". Eight hits, including RingHom.Flat and elementary scheme
  flatness restrictions, but no matching theorem.
- loogle: `"AlgebraicSpace", "Flat"`. Zero hits.
- Mathlib grep: `AlgebraicSpace|schematicClosure|generic.*closure`, AlgebraicGeometry.
  Zero hits.
- Project rg in lean/WeilConjectures and lean/Sheaf for the item id, schematicClosure,
  horizontalClosure, flat_generic_subgroup_closure, HasTraitClosureCharts and
  exists_trait_flat_group_closure. The existing DvrFlatGenericSubgroupClosure is a
  scheme-only, quasi-compact generic-subgroup theorem; it does not state this item.
  ValuationHorizontalCurveModels has unrelated marked-curve horizontal closures.
  AlgebraicSpaceQcOpenSchematicClosure concerns a quasi-compact open subspace and
  does not state the trait/group/flat-test conclusions. No matching declaration found.
- Read RegularGroupSpace.CommutativeSpaceGroup and Mathlib GrpObj: the former
  requires commutativity; the latter already provides exactly the general natural
  group-object notion, so it is reused instead of introducing another definition.

Source checked directly in the primary scan:
https://www.numdam.org/article/MSMF_1973__33__5_0.pdf . Printed p.15 gives the
flat-source subfunctor, printed p.18 gives its group property, and printed p.20
constructs its closed algebraic-space structure on etale presentations. No source-based
correction or STATEMENT-DISPUTED finding is needed. The original node is unchanged
outside its Lean record.

Validation: the final scompile.py server check succeeded for the sandbox and the
named library module, without errors or warnings. The deliver2.py --no-push dry run
then printed OK: commit 2d2b105cad1 passes the preflight and compiles; nothing pushed.
Compilation used only the prescribed server wrapper; no global build was run.
The dispatcher explicitly prohibits subagents; the maintainer's independent review
reads the delivery. No independent second reading has been fabricated in this report.

## Second reading by Q76

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
