## Worker report

This delivery states `section_derived_tensor_normalization` in
`Sheaf.Paper.SectionDerivedTensorNormalization`. It has one postponed theorem;
all helper definitions contain actual constructions. There are no new nodes,
no dependency replacements and no statement correction.

Hypotheses and objects:

- The arbitrary commutative condensed ring is `Λ : Sheaf (coherentTopology
  Profinite.{u}) Ab.{u+1}`, `[MonObj Λ]`, `[IsCommMonObj Λ]`. This is the unbundled
  form of the recorded `Profinite.CondensedRing`; no presentation by a topological
  ring is required.
- The schemes and arbitrary morphism are `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
  The fixed `Scheme.ProEt.topology` uses object universe u+1 and morphism universe u;
  module sections have universe u+1. No equality between site universes is imposed.
- The existing `ring Λ T`, `internalModules Λ T`, `modules Λ T`, `equivalence Λ T`
  are the pulled-back ring, its reconstructed section ring, the two module categories
  and their fixed equivalence. The ordinary operations and adjunctions remain those
  of `SectionModuleOperationsData` and `ProEtaleSectionModuleFunctors`.
- `[∀ T : Scheme.{u}, HasDerivedCategory.{u+1} (modules Λ T)]` chooses the existing
  unbounded derived-category models; it is a size/model parameter already used by
  every imported section-realization comparison, not a flatness or geometric condition.

Clause-by-clause rendering (the three constraint equations are grouped by
`TensorConstraintCondition`, which has exactly the displayed associator and two
unitor equations with fully specified input tensors and maps):

1. `∀ T, TensorRepresentativeCondition Λ T (qTensor Λ T)` says that the fixed tensor
   is the canonical K-flat tensor: its localization comparison agrees, on termwise
   equivalence images, with the localized ordinary signed total and internal lax
   localization tensor map. This predicate includes invertibility when either
   complex is K-flat and identification of the unit with the regular module in
   degree zero. The existing natural isomorphism `tensorComparison` identifies the
   internal derived relative tensor with this fixed section tensor.
2. The second conjunct, expanded through TensorConstraintCondition, gives the associator, left unitor and right unitor
   diagrams for that very `tensorComparison`. The helper constraints are precisely
   `Monoidal.transportStruct (derivedEquivalence Λ T)` projections, with explicit
   endpoint types using the existing `tensor` and `tensorUnit`.
3. The third conjunct is the delta square for every derived internal `M,N`:
   apply `D(E_X)` to the existing `internalDelta`, then the target tensor comparison
   and both pullback comparisons; this equals the source pullback comparison,
   `Lf*` applied to the source tensor comparison, and the specified
   `(tensorPullComparison Λ f).hom`. Thus it compares the actual localized internal
   map with the independently representative-normalized ringed map, not merely
   asserting existence of an isomorphism.
4. The fourth conjunct is the reverse square for the actual lax arrow, the inverse
   natural transformation `normalizationDerivedInternalMu`. Every tensor and
   pullback comparison has its direction reversed and the ringed arrow is `.inv`.
5. The fifth conjunct identifies the actual internal derived unit with the
   ringed unit `normalizationDerivedSectionUnit` under `derivedPullComparison`.
   The internal helper is the existing `leftDerivedUpperStarUnitIso`. The ringed
   helper applies the exact localization factor, the canonical single-complex
   comparison, and the degree-zero image of the ordinary scalar-multiplication
   `normalizationSectionUnit`. `normalizationDerivedRegularUnit` uses the fixed
   localization factor and ordinary unit comparison; the internal derived unit
   is definitionally Q of the degree-zero regular module, and Qh's unit map is
   definitionally the identity (DerivedMonoidal, Derived.lean:298).
6. The last conjunct, expanded through TensorConstraintCondition, gives the ringed tensor-pullback associator, left unitor
   and right unitor diagrams for all section-derived inputs, with the same unit
   map. Together with the forward/reverse squares these are compatibility of the
   identified specified natural transformations. Universal componentwise equalities
   over both variables express equality of natural transformations by extensionality.

The item's seven-step proof is retained in the theorem docstring: identify the
K-flat representative categories; descend the tensor comparison; check regular
unit and constraints; totalize the actual ordinary oplax arrow with both signs;
compute the ringed representative square; identify its vertical and bottom maps
with the actual internal square and apply faithfulness; invert and descend the
unit/constraint equations. Every theorem proof in this delivery is `sorry`.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj` and its canonical coefficient morphisms.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence`.
- `Sheaf.Paper.SectionModuleOperationsData`: `ring`, `modules`, `internalModules`,
  `equivalence`, `pullback`, `adjunction`, and `pullComparison` in the shared namespace.
- `Sheaf.Algebra.Homology.KFlatModuleObject`: `ProEtale.IsKFlatModuleObject`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` (also used by the existing predicate).
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`:
  `CondensedRing.derivedHom`, and its public tensor dependency's `derivedTensor`.
- `Sheaf.Paper.SectionDerivedPushpullNormalization`:
  `sectionDerivedPushpullNormalization` and the canonical comparisons it imports.
- `Sheaf.Paper.SectionOrdinaryOplaxNormalization`:
  `section_ordinary_oplax_normalization`, `normalizationSectionUnit`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `SheafOfModules.site_derived_tensor_descent_independentCoefficients`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
- `Sheaf.Paper.SectionDerivedTensorData`: `derivedEquivalence`, `tensor`, `tensorUnit`,
  `tensorComparison`, `sectionLocalizationComparison`; and
  `Sheaf.Paper.SectionDerivedRealization`: `TensorRepresentativeCondition`, `qTensor`,
  `internalDelta`, `derivedPullComparison`, `tensorPullComparison`.
  The two already landed owning nodes are added to stmt_deps, as the statement
  directly uses their canonical constructions.
- Proof imports retain `internal_section_tensor_comparison`, `sfbSheafTensor_properties`,
  `DerivedCategory.hasDerivedMonoidalCategory`, `Localization.lift/natTrans_ext`,
  `CochainComplex.mapBifunctor`, `derivedPullback_kflat_tensor_computation`, and
  `CategoryTheory.tensorComparisonDescent` from the modules recorded by their nodes.

Edge cases checked before writing: f=id; empty schemes/sites; zero coefficient
ring and zero modules; degree-zero regular modules; odd and negative total degrees;
unbounded complexes. No nonzero, boundedness, flatness of inputs, or open/proper/smooth
hypothesis is introduced. The sign (-1)^p remains in the existing signed total,
not an unsigned replacement. The unit map and all three constraint diagrams use
exactly the same forward ringed map as the delta equality.

Searches actually made (searches.jsonl records service results):

- LeanFinder: “The section equivalence identifies the actual internal derived
  pullback oplax tensor map with the canonical ringed K-flat tensor comparison”.
  Eight hits, including ordinary pullback-unit and ring tensor facts, no match.
- Loogle: `CategoryTheory.Localization.natTrans₂_ext`. One generic two-variable
  localization extensionality theorem, not this equality of specified maps.
- Mathlib grep: `derived.*[Tt]ensor|[Tt]ensor.*[Cc]omparison` in CategoryTheory.
  Twelve hits including Tor and ordinary monoidal closed functor maps, no match.
- LeanSearch: “Derived equivalence between internal sheaf modules and section
  modules identifies derived pullback tensor comparison and its regular unit”.
  Eight ordinary sheaf-module pullback/unit/section results, no derived normalization.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `tensorPullComparison`, `TensorRepresentativeCondition`, `normalizationDerived`,
  `section_derived_tensor_normalization`, and derived tensor/monoidal declarations.
  The canonical data already exist and are reused. No existing theorem supplies
  this conjunction of actual-map equalities and constraint comparisons.

Read Stacks sites-cohomology.tex, Tag 07A4: resolve both inputs by K-flat complexes
with flat terms, take the signed tensor total, and obtain the comparison from the
ordinary tensor-pullback isomorphisms. No statement dispute or mathematical node
fault found. During work the shared dependency files temporarily disappeared and
`--source` returned unavailable; they subsequently reappeared and the wrapper
resolved them as overlays, so no replacement was delivered.

## Second reading by Q01

Author's separate reread of the node, imported data and final signature; no second
agent was started because the dispatcher explicitly forbids it. Independent review
is performed by the maintainer after delivery. Checked all diagram clauses against
the corresponding node clauses as listed above, including the reverse map's
orientation, the regular-module unit, the actual scalar-multiplication unit rather
than an arbitrary unit morphism, and the three constraint equations. Helper
constraints project the existing transported tensor and do not define a second
tensor. The canonical tensorPullComparison remains fixed by its representative
square. No mathematical statement mismatch found. Elaboration repairs made the
helper endpoint types explicit and removed a redundant identity unit isomorphism;
these changes do not change any maps.

Validation: scompile.py checks this file separately, under both sandbox and library
module names, with the prescribed 60-second limit. Constraint equations were abstracted
over their categories to avoid repeated unfolding of the concrete coefficient model.
No time limit was increased; diagnostic commands/options were removed.
