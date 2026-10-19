## Worker report

Item: prop-weil-localized-tstructure. Group: NA. Stage: 2.
The owning module is `Sheaf.Paper.LocalizedTStructure`, with main declaration
`AlgebraicGeometry.Scheme.pbc_localized_tstructure`. All postponed proofs are named
sorry theorems with source and natural-language proof docstrings. Definitions have
actual data. No change to the item's mathematical statement is proposed.

Hypotheses, individually:
- `l : ℕ`, `[Fact l.Prime]` express the prime ell.
- `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`, and
  `[FiniteDimensional (Padic l) E]` express the finite coefficient extension.
- `PbcIntegralRing l E` is the universe lift of the recorded coefficient-extension
  integers. `pbcUniformizer l E` uses their chosen uniformizer. `pbcIntegralDatum`
  supplies the actual coefficient ring, its powers and finite quotients.
- `T : Scheme.{u}`, `[hNoeth : IsNoetherian T]`,
  `[hDim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]` and
  `[hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]` express exactly the
  geometric setting. These named hypotheses are explicitly included in the theorems.
  The two Fact instances package propositions, not extra mathematical assumptions.
- The integral objects are `PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)`,
  the full subcategory of the ambient completed-coefficient derived category.
  They are not towers in place of the derived objects and carry no chosen witness.
- The rational objects are `PbcRationalCategory T (pbcIntegralDatum l E)
  (pbcUniformizer l E)`, the raw scalar localization, and Q is
  `pbcRationalization`. No idempotent completion is applied.

Conclusions, individually:
- `∃ tE : Triangulated.TStructure ...` uses Mathlib's actual t-structure axioms.
- The first two equivalences characterize `tE.le 0 X` and `tE.ge 0 X` by the
  existence of an integral L in the corresponding integral part and
  `Nonempty (X ≅ Q.obj L)`. This is the strictly full, rather than literal, image.
- `tE.bounded = ⊤` says that every object has both finite cohomological bounds.
- The two implications for every K and every integer m state t-exactness of Q.
- The two `Nonempty` natural-isomorphism types for each m identify
  `Q ⋙ tE.truncLE m` with `tA.truncLE m ⋙ Q`, and similarly for `truncGE`.
  These are isomorphisms of functors, so their naturality in K is part of the type.
- `tE.heart X ↔ ∃ H, tA.heart H ∧ Nonempty (X ≅ Q.obj H)` is precisely the
  essential image of a single integral heart object; it does not require an
  integral representative of X itself to be in the heart.
- Only the last clause assumes `PbcTruncationTorCompatible ... K.obj`. For each
  cutoff it gives integral objects L and U whose underlying derived objects are
  `IsDerivedLimit`s of the canonically transitioned normalized reduction diagram
  after ambient lower and upper truncation. Restriction of scalars is exact, so
  truncating these restricted terms is canonically the restriction of the finite
  quotient-coefficient canonical truncation. This is the source tower viewed in
  the one coefficient category needed to form its limit. It identifies rational truncations of
  QK with QL and QU. Thus the computation, unlike the preceding commutation
  assertion, explicitly carries the Tor hypothesis. The sufficient flat-cohomology
  condition is supplied by `pbc_flat_cohomology_torCompatible` in the dependency
  module. Its degree-zero K-flatness formulation expresses flatness of the actual
  module sheaf, not flatness of its underlying constant coefficient module.
- The triangulated structure is obtained from
  `ScalarLocalization.exists_triangulated_scalarLocalization`, choosing its induced
  shift and its characterized image triangles; the exported instances use those
  same choices. Exactness of Q is `pbcLocalizedQIsTriangulated`.

Dependencies and exact declarations used:
- `Sheaf.Paper.BoundedConstructibleComplete`: `PbcCompletedDerived`,
  `PbcIsBoundedConstructibleComplete`, `PbcBoundedConstructibleComplete`,
  `pbcCompletedReduction`, `PbcIntegralRing`, `pbcIntegralDatum`, `pbcUniformizer`.
- `Sheaf.Paper.PbcRationalCategory`: `PbcRationalCategory`, `pbcRationalization`,
  and the canonical completed-section scalar action and linear instances.
- `Sheaf.Paper.IntegralCanonicalTruncations`: `pbcAmbientTStructure`,
  `PbcTruncationTorCompatible`, `pbcCanonicalReductionDiagram`,
  `pbc_integral_truncations` and `pbc_integral_truncation_properties`.
- `Sheaf.Paper.IntegralTStructure`: `pbcIntegralTStructure`,
  `pbc_integral_tstructure`, the inherited triangulated-property instance and the
  linear-shift instance.
- `Sheaf.CategoryTheory.ScalarLocalizationTriangulated`:
  `CategoryTheory.ScalarLocalization.exists_triangulated_scalarLocalization`.
- Mathlib `CategoryTheory.Triangulated.TStructure` (the dependency
  def-weil-t-structure's match), `TStructure.bounded`, `heart`, `truncLE`,
  `truncGE`, and `ObjectProperty.tStructure` from `TStructure.Induced`.
- `Sheaf.Paper.SequentialDerivedInverseLimitCompleted`: `IsDerivedLimit`,
  `CountableAB4Star`, and `derivedCategory_countableProducts_core`.
- The base category module imports the recorded adic-tower, intrinsic-completion,
  witnessed-etale-origin and completed coefficient interfaces. Its normalized
  quotient maps and restriction comparisons are reused in the reduction diagram.

Sources read: the whole owning node, all statement dependencies and their records,
recorded source signatures/docstrings, the blueprint order-1432 source, order-1430
and order-1431 sources, and the unit overview. The blueprint sources were read on
the server because the local literature tree does not contain their bodies.
Pending delivery branches for the missing integral prerequisites were inspected;
they contain mathematical stage-1 work, rather than usable Lean declarations.
The complete bounded-category/rationalization packet in
`deliver/Q06/sbc-def-admissible-lattices` supplies the genuine category interfaces;
those modules are included here so this delivery compiles independently.

Edge cases checked:
- The empty scheme and zero object are admitted; there is no nonemptiness or
  nonzero-object hypothesis.
- All integer cutoffs, including negative cutoffs, are quantified. The upper
  truncation's m versus m+1 convention is explicit in the integral dependency.
- The zero quotient at tower level 0 is retained. The reduction diagram is indexed
  by all naturals and uses the prescribed adjacent quotient maps, not a chosen
  arbitrary transition. Equal-index normalizations in the base witness data are
  identities by the recorded cocycle laws.
- Uniformizer-torsion objects are retained. For example the torsion representative
  shifted by one explains why unconditional compatibility of levelwise reductions
  with truncation must not be asserted. The Tor predicate is nonvacuous and is
  imposed only on the final levelwise calculation.
- Integral representatives can differ, while the conclusion uses isomorphisms in
  the actual rational category and natural isomorphisms of actual functors.
- The site keeps object universe u+1 and morphism universe u; the lifted coefficient
  ring and completed sheaf use the established u+1 module universe.

Searches for an existing theorem:
- `msearch.py ... leanfinder`: bounded t-structure descending under scalar
  localization: eight generic t-structure/localization hits, no exact theorem.
- `msearch.py ... loogle "CategoryTheory.Triangulated.TStructure"`: twelve generic
  t-structure declarations, no scalar-localization descent statement.
- `msearch.py ... grep "TStructure.*[Ll]ocaliz|[Ll]ocaliz.*TStructure" CategoryTheory`:
  no match.
- `rg` through Mathlib, the upstream WeilConjectures tree and shared Sheaf tree
  for localized t-structures, scalar localization and truncations: the existing
  scalar-localization triangulation theorem and ambient standard t-structure are
  useful inputs, but no exact owning theorem.
- Search for the owning blueprint id in upstream WeilConjectures: no declaration.
- Checked existing DAG nodes and current server sources/delivery branches before
  supplying missing interfaces. No new independent mathematical notion was needed.

The wrong proof-dependency record for lem-weil-heart-short-exact-triangles is repaired
by an existing upstream declaration packet, as detailed below. The owning node already
contains the stage-1 correction separating the conditional levelwise computation;
that statement is preserved.

## Dependency modules

`def-weil-pbc-bounded-constructible-complete`: the shared DAG has no usable published
record for the exact completed category. `Sheaf.Paper.BoundedConstructibleComplete`
reuses the Q06 packet's full construction, including the associated-sheaf coefficient
transport, derived realization, intrinsic completeness, uniform constructible
reductions and compatible etale origins. The main record is the full-subcategory
abbreviation, with every auxiliary declaration listed. Objects are actual completed
module derived objects and the membership predicate existentially forgets witnesses.

`def-weil-pbc-rational-category`: the absent record is supplied by
`Sheaf.Paper.PbcRationalCategory`, reusing the Q06 packet. It constructs scalar sections
of the completed coefficient sheaf and their linear action and defines the exact
raw scalar localization and its canonical functor. No unspecified scalar action,
arbitrary comparison equivalence or Karoubi envelope replaces the node's category.

`thm-weil-pbc-integral-truncations`: no usable Lean declaration was recorded.
`Sheaf.Paper.IntegralCanonicalTruncations` gives the actual standard ambient
truncations and their restrictions to the full integral category, together with
the canonical reduction diagram (restriction along the completed-to-finite quotient
and its functorial comparison). The source's all-level higher-Tor condition is an
explicit predicate. The main theorem states the conditional derived-limit
identifications and finite reduction isomorphisms normalized by the actual truncation
counit and unit. Such normalization determines the comparison and hence its
compatibility with the quotient normalization maps. The accompanying properties
state surviving cohomology isomorphisms via the canonical counit/unit, vanishing,
additivity and the actual distinguished truncation triangle; using actual Mathlib
truncations supplies universality and functoriality. A named exact-countable-products
theorem supplies the required Roos product instance without any extra hypothesis.
Canonical closure is the unconditional closure also required by the cited bounded
standard integral t-structure. Only tower/reduction computation carries the Tor
hypothesis. The node's existing wording calls the sufficient flatness condition an
equivalence; no claim of the converse is used by the owning theorem or interface.

`prop-weil-pbc-integral-tstructure`: no usable Lean declaration was recorded.
`Sheaf.Paper.IntegralTStructure` uses Mathlib's induced t-structure on the actual full
subcategory, with named proof obligations for inherited triangulation and truncation
closure. Its theorem states boundedness, the degree-zero cohomological heart, natural
ambient truncation comparisons and preservation of the very same uniformizer-torsion
exponent. The canonical endofunctors are actual Mathlib truncations; on the Tor-compatible
domain the preceding dependency identifies them with the source's tower computation.
The specialized construction and every auxiliary declaration belong to this node.

`lem-weil-heart-short-exact-triangles`: repaired as existing, without writing a module.
The previous `AlgebraicGeometry.WeilSheaf.exact_map_higherLowerShriek` record describes
an unrelated Weil-sheaf functor. The existing
`WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology` publicly imports
`ShortExact`. Its listed declarations cover all five source clauses: truncation
triangle uniqueness and existence; lower/upper adjunctions and their canonical
commutation; `isLE₂`, `isGE₂` and `heart₂` for extension closure; the cone's [-1,0]
bounds and universal kernel/cokernel formulas with the specified maps; the
short-exact/distinguished-triangle equivalence and unique connecting arrow; and the
heart-valued `homology₀` homological functor, whose rotations give the long exact
sequence. These are general t-structure declarations, with no boundedness condition.
The complete signatures and docstrings were read in the upstream files. The wrapper's
existing-declaration probe imports this module and checks every recorded name.

No new definition nodes and no statement changes are made. Only lean records change.
All five delivered Lean modules passed scompile.py with no unexpected warnings.
The prescribed delivery dry run is recorded by the wrapper output.
The independent second reading is reserved for the next worker.

## Second reading by NA

I read the current owning node (including all eight proof steps), its blueprint
order-1432 source and closing Tor audit paragraph, the order-1430 and order-1431
sources, both category-definition sources (orders 1300 and 1305), and Stacks
homology.tex section-truncations (0118), derived.tex
remark-truncation-distinguished-triangle (08J5), and proetale.tex definition-Dbc
(09C1). The blueprint sources and Stacks bodies were read on the project server.
Stacks assumes an abelian category for canonical truncations and their triangle;
it does not state rational t-structure descent. The node correctly attributes that
additional assertion to the blueprint. The existing stage-1 wording, including its
conditional last paragraph, is unchanged by this stage-2 delivery.

Here is my object/hypothesis/conclusion checklist, matched to the Lean file.

1. Prime ell: `(l : ℕ) [Fact l.Prime]`. PASS; no characteristic or lower bound
   besides primality is added.
2. Finite extension E/Q_ell: `(E : Type u) [Field E] [Algebra (Padic l) E]
   [FiniteDimensional (Padic l) E]`. PASS. I opened the coefficient dependency's
   record and CoefficientExtensionFinite/its imported CoefficientExtension:
   these are the finite-dimensional extension and its valuation-ring constructions,
   rather than a field substituted for integral coefficients.
3. A=O_E and the chosen uniformizer: `PbcIntegralRing l E`, `pbcUniformizer l E`,
   and `pbcIntegralDatum l E`. PASS. The first is the ULift of the recorded
   valuation ring, the second lifts its recorded uniformizer, and the datum's
   actual ideal is `Ideal.span {pbcUniformizer l E}`. Its other fields are proofs
   of Noetherianity, finite generation, torsion, perfectness and finite quotients.
4. Noetherian finite-dimensional T with ell invertible: `T : Scheme.{u}`,
   `[hNoeth : IsNoetherian T]`,
   `[hDim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]`, and
   `[hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]`.
   PASS. The `include` command retains these hypotheses on the owning theorem.
   Fact packages exactly those propositions. There is no separation, finite-type,
   smoothness, nonemptiness or global flatness assumption.
5. The integral category C and its standard bounded structure:
   `PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)` and
   `pbcIntegralTStructure T l E`. PASS. I read BoundedConstructibleComplete,
   IntegralCanonicalTruncations and IntegralTStructure. The first category is a
   full subcategory of the actual completed-sheaf module derived category, with
   the conjunction of intrinsic completeness, uniform constructible reductions,
   and existence of compatible etale origins. Existential witnesses are in Prop,
   and its morphisms are all ambient morphisms. The t-structure is Mathlib's
   `ObjectProperty.tStructure` induced by the actual standard derived t-structure.
6. C_E is the raw scalar localization and Q its localization functor:
   `PbcRationalCategory` and `pbcRationalization` at this same datum/uniformizer.
   PASS. I read PbcRationalCategory and ScalarLocalization. Objects retain one
   integral object; Hom is `Localization.Away p ⊗[A] Hom`, with the recorded
   coefficient localization identifying the localized scalar ring with E. The
   scalar action is the canonical completed constant-section action, not a
   parameter or an arbitrary action. There is no Karoubi envelope.
7. The specified triangulation of C_E: the `pbcLocalized*` instances all project
   from the same `pbcLocalizedTriangulationData`, a specialization of
   `ScalarLocalization.exists_triangulated_scalarLocalization`. PASS. I opened
   that theorem: it specifies the induced shift, identity comparison with Q and
   exactly the isomorphism classes of images of integral distinguished triangles.
   The inherited integral shifts are linear by `pbcIntegralShift_isLinear`.
   `pbcLocalizedQIsTriangulated` supplies exactness for these very instances.
   These choices are characterized structures, not a bare unspecified Nonempty
   structure replacing the source triangulation.
8. Two strictly full image subcategories forming a t-structure:
   `∃ tE : Triangulated.TStructure ...` followed by both equivalences for
   `tE.le 0 X` and `tE.ge 0 X`. PASS. Each existential L is in the same integral
   category, has the appropriate integral degree bound, and has
   `Nonempty (X ≅ Q.obj L)`. This is an isomorphism closure, not equality of the
   representatives. I read Mathlib TStructure/Basic, including its axioms and
   indexed shifts; its formulation is equivalent to the node's degree-zero pair.
9. Boundedness: `tE.bounded = ⊤`. PASS. Mathlib defines `bounded` as the
   intersection of objects admitting an upper and a lower integral bound.
10. T-exactness of Q: for every K and m the two implications preserve `le m`
    and `ge m`. PASS. Exact triangulatedness is supplied by item 7, and no
    converse on a chosen integral representative is inadvertently asserted.
11. Both natural truncation comparisons, for every integer m: the two
    `Nonempty (Q ⋙ tE.truncLE m ≅ tA.truncLE m ⋙ Q)` and corresponding
    `truncGE` expressions. PASS. These are natural isomorphisms of functors on
    C, with components precisely at every K; the direction agrees with the
    displayed formulas. The comparison is not merely unrelated objectwise
    isomorphisms. Every negative as well as positive cutoff is included.
12. The heart: `tE.heart X ↔ ∃ H, tA.heart H ∧ Nonempty (X ≅ Q.obj H)`.
    PASS. The reverse implication uses a single integral heart object; it is
    stronger than intersecting the essential images of two possibly different
    objects, and is exactly the node. I checked Mathlib's `heart` intersection
    and the upstream heart-valued `homology₀` used in the proof plan.
13. Conditional tower computation: only the final clause binds
    `_hTor : PbcTruncationTorCompatible ... K.obj`; for every m it produces
    integral L and U whose underlying objects satisfy `IsDerivedLimit` for the
    lower/upper truncations of `pbcCanonicalReductionDiagram`, and identifies
    rational truncations of QK with QL and QU. PASS. I read the diagram's
    construction: adjacent arrows use `pbcReductionTransition` and the canonical
    restriction-composition comparison, not arbitrary maps between the levels.
    Exact restriction of scalars lets these be the finite quotient-coefficient
    truncations in the common completed-coefficient category. I retrieved the
    current server source of `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
    `IsDerivedLimit` is existence of the specified distinguished Roos triangle,
    which is the dependency node's convention, not a chosen functorial limit.
    The integral dependency uses upper cutoff m+1; reindexing gives the owning
    theorem's upper cutoff m for every integer. The flat-cohomology implication
    is explicitly supplied in the dependency module and is not imposed on the
    first twelve items.

Dependency-module audit (H12/H13): no new definition nodes were introduced. I
checked all five modules and all six delivered node records. The two category
modules faithfully supply existing, previously unrecorded DAG notions. Their
completed-ring transport is normalized on underlying additive sheafification;
its scalar-extension comparison is the mate of that normalization. Thus no
private replacement category, arbitrary equivalence or hollow chosen map is used.
I read AdicTowerLocalModel/IsUniformlyBoundedConstructibleAdicTower and
PbcWitnessedTower, including the bounds, common local-model identifications,
normalization equations, bounded-below origins and origin-compatibility equation.
These are the recorded dependency notions used by the category predicates.

The integral t-structure module uses the actual ambient standard aisle/coaisle
via the induced construction. Its theorem gives boundedness, degree-zero heart,
canonical ambient comparisons, and torsion preservation with the same exponent;
the latter entails the source's torsion-subcategory stability. The integral
truncation module supplies the conditional Roos and finite-reduction formulas,
canonical counit/unit normalizations, cohomology properties and actual canonical
triangle. The closure helper is the ambient closure needed for the full-category
t-structure of order 1431, rather than an assertion of unconditional reduction
compatibility. I found that the worker had stated only flatness implies Tor
compatibility although the dependency node also says "equivalently". I added
`pbc_torCompatible_iff_flat_cohomology` for integral objects, using the same
module-sheaf flatness encoding; its source/proof docstring explains both
implications. This theorem renders an existing clause of that dependency node,
and is listed in its `lean.declarations` and `lean.note`.

For the existing-record repair of lem-weil-heart-short-exact-triangles I opened
upstream ShortExact.lean and Homology.lean, including their actual signatures.
`triangle_hom_ext_of_isLE_of_isGE` and `exists_iso_triangleLEGE` give uniqueness
and existence, the two truncation functors/adjunctions give the canonical
comparisons, `isLE₂`/`isGE₂`/`heart₂` give extension closure, the cone-bound and
kernel/cokernel declarations give clause 3, the short-exact equivalence and
connecting-arrow uniqueness give clause 4, and `isHomological_homology₀` gives
clause 5 with rotations. No boundedness assumption is present. The old
exact_map_higherLowerShriek record is indeed unrelated; the worker's existing
packet repair is retained.

Edge cases: the empty scheme and zero objects are allowed throughout; the finite
stratification may be empty. Uniformizer-torsion objects and their shifts are
not removed from C. A free degree-zero object checks the heart; a shifted object
checks both integer-cutoff conventions. A torsion representative such as
(A/varpi)[-1] explains why the final Tor condition must not be removed. There is
no arbitrary index set in the owning theorem: its sole tower runs through all
positive powers. In particular I correct the worker report's "zero quotient at
level 0" sentence: `PbcQuotient d n` and the finite coefficient system use
A/I^(n+1), so Lean level 0 is A/I, corresponding to the source's n=1. There is
no zero quotient in this tower and no missing positive level. A hypothetical
extra A/I^0=0 level is outside the node's n>=1 tower. The site retains object
universe u+1 and morphism universe u; coefficients/modules use u+1 and the
valuation ring is transported by ULift. No equation between the two site
universes or additional typeclass assumption is imposed by the theorem.

Independent searches: I ran msearch LeanFinder with a central-element
localization/t-exactness/heart formulation (eight ambient derived t-structure or
general triangulated-localization hits), Loogle with `"TStructure",
"IsLocalization"` (zero hits), and grep for tStructure with localization or
quotient in CategoryTheory (zero hits). LeanSearch was also attempted and
returned Internal Server Error; it is recorded as unavailable, not counted as a
successful negative search. I separately searched the upstream WeilConjectures
and shared Sheaf trees by localization/rational/t-structure terminology and the
exact blueprint id, and opened Mathlib TStructure/Basic and the existing scalar
localization source. None supplies this bounded rational descent and heart
theorem. Searches for the actual category and Tor helper names find no published
competing definitions in the shared/upstream source trees. The search log remains
in searches.jsonl.

Repairs in this reading: added the proof-only Homology import to
LocalizedTStructure, added the recorded proof-only FiniteReductionReconstructionCompleted
import to IntegralCanonicalTruncations, named the heart lemma explicitly in the
main proof docstring, supplied the missing flatness equivalence clause, and
corrected the report's tower-index explanation. I preserved the owning
mathematical statement, all correct original clauses and all original report
sections. Each delivered node's lean.statement is now the exact source signature,
including its line breaks. Every new/postponed theorem still has proof `sorry`
and a source/blueprint/proof docstring; definitions contain actual data or use
uniquely characterized comparisons/proof properties, and no result was proved.
All Lean lines are at most 100 characters. Compilation and final dry-run results
are recorded below after the prescribed tools finish.

During the second reading Q06's category packet landed. I compared its
BoundedConstructibleComplete.lean and PbcRationalCategory.lean byte for byte
against the inherited sandbox copies: both are identical. I therefore removed
those two modules and their two node copies from this delivery instead of
overwriting Q06's reviewed records. The original Worker report and dependency
sections above describe the inherited packet; this note supersedes their claim
that those two modules are still being delivered here. The final delivery has
three modules (IntegralCanonicalTruncations, IntegralTStructure,
LocalizedTStructure) and four node records, including the existing heart-lemma
repair. Both category dependencies are reused from the landed Q06 packet.

Final compilation: the prescribed scompile.py completed with exit 0, no errors
and no unexpected warnings for the revised three modules and both byte-identical
category modules (the latter were removed from the delivery while that snapshot
was compiling, following their Q06 landing). All delivered files were checked
individually by the wrapper, including the added equivalence and proof imports.

Required dry run: deliver2.py --no-push printed
`OK (dry run): commit e5f999a097 passes the preflight and compiles; nothing pushed`.
The final push is submitted with the same three checked modules, four node records,
and this completed second-reading report.
