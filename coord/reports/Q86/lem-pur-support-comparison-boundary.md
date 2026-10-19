## Worker report

Repair of the return at immutable head `17548e9ecadc` (H13 and H9/H4).
The prescribed first dry run of the saved packet passed at `a5a3ab1b13`.
The required self-check nevertheless confirmed the independent review: its dependency
record omitted clauses and its separate module duplicated the original owner.
This delivery implements correction (b) in the return: repair the original
`SupportSiteComparison.lean` import chain and canonically transport its global-section
kernel to the restriction-kernel model. The item module is retained, with only its
import changed from `SupportSiteComparisonCanonical` to `SupportSiteComparison`.
The natural-language statements, hypotheses, dependencies and proofs of both nodes stay.

`Sheaf.AlgebraicGeometry.SupportComparisonBoundary` states
`AlgebraicGeometry.exists_support_comparison_boundary`. Its comparison maps are fixed
constructions, rather than existential variables. Only the two connecting transformations
are existential, and both must equal the snake boundary on every injective complex.
All postponed theorems have whole proofs `by sorry`; every definition has actual data.

Clause-by-clause rendering:

- Algebraically closed field: `(k : Type u) [Field k] [IsAlgClosed k]`.
- Finite commutative coefficient ring: `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)` is the recorded ordinary
  constant-ring-module encoding, with no condensed coefficients.
- Separated finite-type scheme over the field: `(T : Scheme.{u})`,
  `[T.Over (Spec (.of k))]`, `[LocallyOfFiniteType (T ↘ Spec (.of k))]`,
  `[QuasiCompact (T ↘ Spec (.of k))]`, `[IsSeparated (T ↘ Spec (.of k))]`.
- Closed immersion: `(C : Scheme.{u}) (i : C ⟶ T) [IsClosedImmersion i]`.
  The open complement is the actual `i.openComplement.ι`. The two canonical
  `supportRestrictionArrow i` declarations represent its arrows to the terminal objects.
- Ordinary sheaf in degree zero: every ladder square quantifies over
  `F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)` and applies
  `DerivedCategory.Plus.singleFunctor ... 0`. Its pro-etale coefficient is obtained by
  composing with `(ProEtale.comparisonUpperStar ... T).mapDerivedCategoryPlus`.
- The supported comparison `c_C` is `ProEtale.supportComparisonHypercohomology A i q`:
  integer homology of `ProEtale.supportComparison A i`. The latter derives
  `supportComparisonUnit`, uniquely determined by its inclusion equation with the actual
  comparison adjunction unit. It cannot be replaced by an arbitrary zero map.
- The terminal comparison `c_T` is `ProEtale.finiteComparisonGlobalHypercohomology T A q`.
  Its body applies homology to the recorded `finiteComparisonGlobalSections T A`, with
  only the canonical identity-functor unitors and associator inserted.
- The open comparison `c_V` is `ProEtale.finiteComparisonSectionHypercohomology T A
  (Scheme.Etale.mk i.openComplement.ι) q`. It derives the actual comparison unit
  evaluated over this open object. `supportBoundaryOpenCoefficientIso` is the recorded
  `supportSiteComparisonCoefficientPullbackIso`, transported by the canonical
  `upperStarIsoOpenImmersionRestriction` isomorphisms in both topologies. These are the
  precise coefficient identifications whose coherence is recorded by
  `supportSiteComparison_pullback_coherent`.
- The additional `SupportBoundaryOpenUnitNormalized A i.openComplement.ι` clause spells
  out the unit equation under this identification: restrict the unit on `T`, or take
  the unit on the restricted sheaf on `V` and then the direct image of the specified
  coefficient isomorphism. Deriving evaluation of this equation identifies the open
  evaluation comparison used in the ladder with the global comparison on `V`.
  Evaluation on the open object is the support-sequence model of cohomology on `V`;
  this is the published `sectionHypercohomologyFunctor` interface, not another cohomology.
- The two `supportBoundaryNormalization` clauses require, on every bounded-below
  termwise injective complex `I`, that the transported boundary
  `supportSequenceModelBoundary ... δ I ... (Iso.refl _) q` equals
  `hS.δ q (q + 1) rfl` of the short exact kernel/inclusion/restriction complex.
  Here `w` and `hS` are proofs about those fixed arrows, not choices of arrows.
  This pins down the cochain/snake sign, beyond mere exactness.
- The two `SupportSequenceExact ... δ` clauses give the two exact support sequences.
  Each boundary is already a natural transformation in all derived coefficients.
- The first ladder equality is `δₑ(q) ≫ c_C(q+1) = c_V(q) ≫ δₚ(q)`. This is exactly
  the displayed connecting square in categorical composition order. Integer degrees
  include every `q ≥ 0` and the rest of the full long exact sequences.
- The second equality is the forgetting-supports square, using the actual
  `supportHypercohomologyInclusion`. The third is the restriction square, using the
  actual `sectionHypercohomologyRestriction`. No equation includes a negation.
- The last three equalities give naturality of `c_C`, `c_T`, and `c_V` for every
  `f : F ⟶ G`. Together with naturality of the boundaries this gives naturality
  of the ladder squares. All arrows belong to `ModuleCat A`, hence are A-linear.
- There is no constructibility, freeness, finite-generation or nonzero assumption on `F`.

Dependency declarations read and used:

- Mathlib: `AlgebraicGeometry.Scheme` and its morphisms; `LocallyOfFiniteType` and
  `QuasiCompact` from `Morphisms.FiniteType` / `Morphisms.QuasiCompact`;
  `IsSeparated` from `Morphisms.Separated`; `IsClosedImmersion` from
  `Morphisms.ClosedImmersion`; `IsOpenImmersion` from `OpenImmersion`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `Scheme.proEtaleSiteComparisonModules`,
  with the actual upstream `ProEtale.comparisonUpperStar`, `comparisonLowerStar`, and
  `comparisonAdjunction`. This supplies the fixed constant-coefficient adjunction.
- The recorded derived-category interface uses `DerivedCategory.Plus`, its
  `singleFunctor` and `homologyFunctor` on the module-valued sheaf category.
- `Sheaf.AlgebraicGeometry.SupportCohomology`: `Sheaf.supportedSectionsFunctor`,
  `Etale.supportRestrictionArrow`, `ProEtale.supportRestrictionArrow`, and
  `ProEtale.supportSections`.
- `Sheaf.AlgebraicGeometry.SupportLongExact`: `Sheaf.supportedSectionsInclusion`,
  `sectionHypercohomologyFunctor`, `supportHypercohomologyFunctor`,
  `supportHypercohomologyInclusion`, `sectionHypercohomologyRestriction`,
  `SupportSequenceBoundary`, `SupportSequenceExact`, `supportSequenceModelBoundary`.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`:
  `ProEtale.supportSiteComparisonCoefficientPullbackIso`, used in the explicit
  open coefficient isomorphism and unit-normalization clause. The import is used.
- `Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized`:
  `ProEtale.finiteComparisonGlobalSections`, used directly for the terminal comparison.
- The repaired dependency owner `Sheaf.AlgebraicGeometry.SupportSiteComparison`:
  `ProEtale.supportComparisonUnit_existsUnique`, `supportComparisonUnit`,
  `supportComparison`, and `supportComparison_isIso`.
- The ordinary open restriction and its canonical inverse-image identification are
  the existing etale and pro-etale `LowerShriek.OpenImmersion.Defs` declarations.
  Derivation uses `Functor.rightDerivedFunctorPlusBaseChange` and canonical homology.

Source checked: `literature/stacks-project/etale-cohomology.tex`, Tag 09XP,
`section-cohomology-support`, especially the injective restriction sequence and its
long exact sequence. The specified adjunction-unit refinement is the node's six-step
agent-formulated proof, not a claim that Tag 09XP already states etale/pro-etale naturality.
The theorem docstring now contains those six steps in full, including their node citations.

Edge cases rechecked with the node and definitions open: identity immersion `C = T`
(empty open complement), empty closed support (open complement all of `T`), empty `T`,
zero sheaf, zero coefficient ring, `q = 0`, and negative integer degrees.
No edge case requires an extra hypothesis. On injective models the same snake boundary
is fixed even when it is zero. In a nonzero situation the previous substitution
`c_C = c_T = c_V = 0` is unavailable, because the comparison maps are fixed definitions.
The existential `w`/`hS` cannot encode another sign: proof irrelevance fixes the short
complex and its homological boundary once the canonical inclusion and restriction are fixed.

Searches (repeated for this repair):

- `msearch.py ... leanfinder "site comparison preserves the boundary map in cohomology
  with supports"`: eight group-cohomology comparison/functoriality hits; no sheaf-site
  support-boundary comparison.
- `msearch.py ... loogle '"cohomology", "δ"'`: twelve group/Tate-cohomology
  connecting-map hits, including `groupCohomology.δ_naturality`; no matching theorem.
- `msearch.py ... grep 'supportComparison|SupportSequenceBoundary|supportBoundaryNormalization'
  AlgebraicGeometry`: zero Mathlib hits.
- Direct `rg` over upstream `WeilConjectures` and side `lean/Sheaf` for
  `supportComparison|supportBoundaryNormalization|exists_support_comparison_boundary`:
  the existing support-comparison owner was found, but no boundary comparison theorem.
  Direct `grep -rn lem-pur-support-comparison-boundary` in upstream returned no matches.
  Existing generic support-sequence and comparison definitions were reused.

No statement dispute and no new DAG node. The node's natural-language statement is unchanged.

## Dependency modules

`lem-pur-support-site-comparison` is repaired in its original owning module
`Sheaf.AlgebraicGeometry.SupportSiteComparison`, implementing the reviewer's option (b).
`SupportSiteComparisonCanonical.lean` is removed from the packet. Thus the five names
reported under H9/H4 have one owner: the existing module being replaced in place.
The record's main declaration is again `ProEtale.supportComparison_exterior` and its
`lean.declarations` lists the entire repaired interface, including every old export.
Only the dependency node's `lean` changes; `lean.note` describes the import failure,
the kernel transport and preservation of the whole statement.

The recorded module imported retired lower-shriek/global and monoidal owners alongside
finite-coefficient owners. The original exterior product itself can be imported together
with the normalized finite global comparison (probe compiled clean, 7.2 s / 17.1 s).
The legacy `Derived.ComparisonMonoidal` probe fails on duplicate
`upperStarIsoLowerStarInv`; replacing it wholesale by the finite version fails on duplicate
`laxMonoidal_Q`, because the existing supported exterior product uses the original
pro-etale tensor owner. The repaired import family therefore keeps that existing tensor
and exterior product and uses the general `Functor.leftDerivedTensorComparison` directly,
with the canonical exact/left-derived identifications. No tensor structure is redefined.
The ordinary comparison monoidal/flat declarations come from their current published
modules. All currently stated proof-dependency modules are imported non-publicly when
not already public statement imports, including the four quotient/support proof lemmas. The global comparison comes from `finiteComparisonGlobalSections`.

The timed diagnostic isolated expensive fixed-ring categorical unfolding in the derived
pullback and monoidal composites. `supportDerivedCoefficientPullbackIso` and
`supportDerivedComparisonTensorIso` now assemble those same existing canonical APIs for
abstract coefficient categories, then specialize to `ModuleCat A`. This changes neither
coefficient universes nor the maps. A diagnostic compile with a reduced per-helper
heartbeat bound accepted the complete construction; no diagnostic option is delivered.

The full clause correspondence for this dependency is:

- Ordinary finite commutative coefficients: `(A : Type (u + 1)) [CommRing A] [Finite A]`
  with `Sheaf ... (ModuleCat A)` in both topologies. Field, separatedness and finite-type
  binders are unchanged in the isomorphism, open and exterior theorems.
- The canonical D+ support map is `supportComparison A i`, the right-derived map of
  `supportComparisonUnit`. Its unique-existence equation fixes it by the actual
  comparison unit and the kernel inclusion. `supportComparison_isIso` asserts its
  invertibility. Its natural-transformation type gives naturality in every `M`.
- The kernel for this D+ map is the one in `SupportLongExact`, so the accepted boundary
  module still uses the same fixed support comparison and snake normalization.
- `supportKernelEvaluationIso_existsUnique` specifies the isomorphism from the existing
  `Etale.supportedEtaleSections` kernel by the exact inclusion/evaluation equation.
  `supportKernelEvaluationIso` chooses this uniquely determined object. It has actual
  data, and introduces no extra coefficient or finiteness hypothesis.
- `globalEtaleSupportKernel` abbreviates the existing global-section support functor.
  `supportComparisonUnbounded` first applies the right-derived kernel transport and
  then the canonical D+/unbounded compatibility maps around `supportComparison`.
  Its domain is exactly the published exterior-product and open-restriction domain.
- `supportComparison_forget` retains the commuting forgetting-supports square.
  `supportGlobalComparison` is explicitly the already recorded
  `finiteComparisonGlobalSections`, conjugated only by terminal evaluation and the
  canonical D+/unbounded compatibility. It is a construction, never an arbitrary map.
- `fullSupportForget_isIso`, together with that square at `i = 𝟙 T`, retains the C=T
  normalization to the adjunction-unit global comparison.
- `supportComparison_open` retains the square for every actual open `U : T.Opens` and
  every D+ `M`. Its etale restriction is the existing
  `Etale.derivedSupportOpenRestriction`; its pro-etale restriction is the canonical
  supported-counit transpose normalized by `supportOpenConstantIso_existsUnique`.
  The last coefficient map is the recorded `supportSiteComparisonCoefficientPullbackIso`
  derived in `supportDerivedPullbackIso`. The locally Noetherian instances required
  by the pro-etale closed-support construction are supplied from finite type over k.
- `supportExteriorCoefficientIso` is the specified theta: exact versus left-derived
  projection pullback, canonical derived monoidality of comparison, the two recorded
  comparison-pullback identifications, then the inverse exact/left-derived projection
  identifications. It lands in the existing pro-etale exterior product.
- `supportComparison_exterior` retains the full displayed equality in unbounded D(A),
  using `Etale.supportedExteriorProduct` and `ProEtale.supportedExteriorProductOverField`.
  The separate `(F : DerivedCategory.Plus ...)` and `(eF : F.obj ≅ ... K.obj L.obj)`
  retain exactly the assumption that the actual exterior product is bounded below.
  `eF.inv` before comparison and `eF.hom` inside its coefficient transport cancel the
  presentation choice; no automatic boundedness or Kunneth assertion is added.

Additional repair searches: LeanFinder query "terminal evaluation isomorphism cohomology
with supports kernel restriction comparison" returned eight complex-restriction/evaluation
hits, no support-kernel interface. Loogle query `kernel.mapIso, kernelIsIsoComp` returned
unknown identifier; direct Mathlib reading located both in `Limits/Shapes/Kernels.lean`.
The msearch grep query `supportKernelEvaluationIso|supportComparison_forget|supportComparison_exterior`
under CategoryTheory returned zero hits. Direct upstream and side-source rg found neither
`supportKernelEvaluationIso` nor `supportGlobalComparison`; both are transports in the
existing node, not independent new notions. The original support, exterior, pullback,
global-comparison, exactness and derived constructions are reused.

Dependency edge cases: full support/empty complement, empty support, empty ambient scheme,
zero sheaf/zero ring, zero K or L, and the case where the actual exterior product is not
bounded below. The first cases retain the same kernel inclusion and normalized comparison;
the last is correctly excluded only by the node's explicit boundedness hypothesis on F.
For a general ring, K and L bounded below do not force their derived tensor bounded below;
the `F,eF` binders must and do remain.

## Second reading by Q86

Reopened the saved packet, the return, current node records and the original owner.
This self-check is not an independent review; the dispatcher prohibits another agent.
The saved packet passes mechanical validation but does not satisfy H13: only its first
support isomorphism clause was recorded. The repaired record restores the exterior equality
as main theorem and every original clause. H9/H4 is repaired by replacing the original
owning module, rather than placing its five names in a second module. The old extra module
is absent from the packet. No other owner is imported or duplicated.

Compared the item module with the accepted returned version: only its import changes.
In particular the fixed c_C/c_T/c_V constructions, the actual-unit equations, both exact
rows, both injective ShortExact.δ normalizations, connecting square, forgetting square,
restriction square and coefficient naturality all remain verbatim. All hypotheses are
still present: algebraically closed k, finite commutative A, separated finite-type T/k,
closed immersion, actual open complement, ordinary module sheaf F in degree zero, and
F_p obtained by the fixed comparison inverse image. No constructibility or freeness.

Read the entire repaired dependency separately, matching every clause above. Its new
kernel isomorphism is uniquely pinned by the inclusion equation, and the unbounded
comparison uses its right-derived map in the correct direction. Global forgetting is
therefore on the original supported-section model, while the boundary remains on the
restriction model. The full-support comparison uses the same actual finite global unit.
Open restriction retains its specified pullback coefficient identification. Exterior
compatibility still compares the two actual supported products using the canonical theta,
including the boundedness hypothesis. The general derived monoidal comparison is used
as a concrete composite of existing APIs, with no replacement tensor or arbitrary iso.
Every postponed theorem is a whole `by sorry` with source, blueprint tag and proof docstring;
definitions contain constructions or uniquely determined choices only.

Final validation: the two delivered files compile clean through the prescribed
`scompile.py Q86 lem-pur-support-comparison-boundary` invocation. The dependency owner
compiled in 12.6 s and the retained boundary module in 11.2 s (private overlay 38.0 s,
all within 60 s); no errors or warnings. Exact signatures, explicit auto-implicit policy,
100-character lines, all original dependency exports, and unchanged non-Lean node fields
were rechecked. The item source differs from the saved returned module only in its import.
Direct searches for the two generic transport helper names in upstream and side sources
returned no matches.
