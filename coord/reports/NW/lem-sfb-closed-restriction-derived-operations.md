## Worker report

Item: lem-sfb-closed-restriction-derived-operations. Delivery module:
Sheaf.Paper.ClosedRestrictionDerivedOperations. The only postponed proof is
AlgebraicGeometry.ProEtale.CondensedRing.closed_restriction_derived_operations.
Every helper is a transparent definition or abbreviation with actual data; no
independent mathematical prerequisite or new definition node is introduced.
The accepted statement, statement dependencies and seven-step proof are unchanged.

The inherited BLOCKED ending concerned a stage-1 re-split refusal. The current
coord/brief-stage2.md §0 explicitly distinguishes that situation: this stage-2
assignment records Lean and validates with deliver2.py, preserving the accepted
split. This delivery does exactly that. There is no released repair note for this
item. The current queue lists the item at stage 2 with no usable Lean record.

Sources read: the item's complete current node, all its statement-dependency
nodes and their lean/mathlib records; HRS, Constructible sheaves, Lemma 5.3 and
its proof, printed page 14 (PDF extracted in the sandbox); Stacks proetale.tex,
lemma-closed-immersion (09AA), clause (1); derived.tex,
lemma-product-K-injective (0BK6); and the current blueprint latest
sec-six-functors-basics/sk-prop-sf-comp-coherence/
det-sf-comp-coherence-refinement.proof.md, (2), closed-fibre paragraph.
HRS provides bounded filtered continuity, not the entire combined statement.
The module preserves that distinction and reproduces the node's seven-step
agent assembly in the theorem docstring.

Hypotheses and objects, matched clause by clause:

- Arbitrary commutative condensed ring: `Λ : Sheaf (coherentTopology
  Profinite.{u}) Ab.{u + 1}`, `[MonObj Λ] [IsCommMonObj Λ]`. This is the
  underlying-object presentation of the recorded `Profinite.CondensedRing`
  abbreviation, with no topological presentation or coefficient finiteness.
- Coefficients Λ_V = p_V^*Λ: the existing `condensedRingObj Λ V` appears in
  every internal module category. Its implementation is the pulled-back
  coefficient of the recorded `coefficientRing` construction. No coefficient
  sheaf, module category or tensor structure is recreated.
- Ordinary uncompleted D(A_V): `DerivedCategory (Mod (Sheaf
  (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V))` throughout.
  These use the live framework's chosen derived categories, not a completed
  or constructible subcategory.
- Small sites and indexing categories: explicit universe `u`; schemes are
  `Scheme.{u}`, coefficient abelian groups are in `u+1`, sites have objects
  in `u+1` and morphisms in `u`, and indices are arbitrary `Type (u+1)`.
  Filtered diagrams use `[SmallCategory J] [IsFiltered J]`. No equality of
  site object and morphism universes is imposed.
- Closed immersion of qcqs schemes: `{T₀ T : Scheme.{u}} (t : T₀ ⟶ T)`,
  `[IsClosedImmersion t]`, `[CompactSpace T] [QuasiSeparatedSpace T]`, and
  the same two classes for T₀. There is no complementary-open parameter or
  hypothesis and no Noetherian, affine or constructibility hypothesis.
- Canonical coefficient isomorphism and exact inverse image: existing
  `upperStar Λ t`, whose definition is mapMod followed by extendScalars
  along `condensedPullbackHom Λ t`. The latter is the existing canonical
  isomorphism, so the existing exact `mapDerivedCategory` is used for D(t^*).
- Phi: `closedRestrictionPhi Λ V` abbreviates precisely
  `(condensedModuleSections Λ V).rightDerivedFunctor`, valued in D(Ab).
  The imported sections definition forgets the internal module action and
  evaluates at `Scheme.ProEt.mk (𝟙 V)`.
- Psi: `closedRestrictionPsi Λ t` abbreviates
  `(upperStar Λ t).mapDerivedCategory ⋙ closedRestrictionPhi Λ T₀`.
- Actual restriction rho: `closedRestrictionSections` is the whiskered
  existing module adjunction unit followed by restriction along the
  canonical morphism from id_T₀ to the base change of id_T. Its body uses
  `pullback.lift`, not an arbitrary map or a choice of a natural isomorphism.
  `closedRestrictionRho` is `Functor.rightDerivedPullback` of that map.
- Two-resolution normalization: the theorem quantifies over every complex
  K, every K-injective I and quasi-isomorphism s : K → I, every K-injective
  H and quasi-isomorphism j : t^*I → H. Its equality uses RF(Qs), the
  existing `rightDerivedFunctorObjQIso I`, the exact-pullback factorization,
  RG(Q(t^*s ≫ j)), and `rightDerivedFunctorObjQIso H`. It identifies rho
  under these isomorphisms with Q of beta_I followed by Gamma(j).
  Because s and j are arbitrary, both resolution choices are covered.
  No claim that t^*I is K-injective occurs.
- Additivity and triangulatedness: the first four conjuncts are exactly
  `Phi.Additive`, `Psi.Additive`, `Phi.IsTriangulated`, `Psi.IsTriangulated`.
  Shift comparisons are the existing canonical integer-shift structures;
  `NatTrans.CommShift rho ℤ` states commutation with all of them.
- Every distinguished triangle, including its connecting arrow: the next
  triangle conjunct quantifies over `Δ ∈ distTriang _` and gives a morphism
  `Phi.mapTriangle.obj Δ ⟶ Psi.mapTriangle.obj Δ` with its three components
  equal to the three rho components. A Mathlib triangle morphism includes
  the third commuting square with the shifted first component.
- All small products and the original projections:
  `ClosedRestrictionProducts` quantifies over every small J and family K.
  It asserts a limiting fan c and that both image cones are limiting.
  Consequently the comparisons induced by the original projection legs
  to ANY selected target products are isomorphisms. The displayed equality
  uses `IsLimit.lift`; postcomposition by the whiskered rho forms exactly
  the product of its components. It says `comparisonPhi ≫ productRho =
  rhoProduct ≫ comparisonPsi`. These are the node's specified comparisons,
  with no unnormalized choice of product isomorphisms.
- Strict filtered diagrams with one common termwise bound:
  `ClosedRestrictionFilteredRepresentatives` quantifies over actual
  `D : J ⥤ CochainComplex ... ℤ` and `a : ℤ`, with
  `∀ i, (D.obj i).IsStrictlyGE a`. The complex C is `colimit D`, and
  `colimit.ι D i` are its actual termwise cocone legs.
- Existence of functorial bounded section representatives:
  `HasClosedRestrictionFilteredModel` asserts simultaneous diagrams P,R,
  target complexes L,M and natural derived identifications eF,eG,εF,εG,
  preserving the same bound a. The chain cocones α,γ and transformation
  η,m are tied to the original cocone and to rho by four explicit derived
  equations; their chain squares commute before localization. This makes
  the convention nonvacuous and does not replace restriction by an
  arbitrary chain map.
- Both filtered comparisons invertible: for ALL normalized representatives
  and their cocones the remaining clause asserts `IsIso (Q.map
  (colimit.desc P (Cocone.mk L α)))` and the corresponding statement for R.
  These are precisely the termwise-colimit section-complex comparisons.
- Filtered compatibility and replacement independence: its final equality
  is `Q(colimMap η) ≫ Q(desc γ) = Q(desc α) ≫ Q(m)`; the normalized maps η
  and m represent respectively the diagram of rho and rho at QC.
  Universal quantification over representatives and identification
  isomorphisms gives independence under quasi-isomorphic replacements.
  The universal clause allows even unbounded quasi-isomorphic chain
  representatives, as exact filtered colimits in Ab preserve their
  quasi-isomorphisms. The supplied simultaneous model is bounded below.

Dependency declarations and signatures were read in the following source modules:

- Sheaf.Topology.ProfiniteCondensedRing: `Profinite.CondensedRing`;
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic:
  `coefficientRing`, `coefficientRing_X`, `condensedRingObj`,
  `isCommMonObj_condensedRingObj`, and the canonical coefficient comparison.
- Sheaf.Paper.CondensedModuleDerivedPushpull: the named ordinary total
  module-object derived functors and its imported general derived framework.
  Exact inverse image in this item is the recorded `upperStar.mapDerivedCategory`.
- Sheaf.Paper.CondensedQcqsPushforwardContinuity:
  `condensedModuleSections`, `condensed_qcqs_globalSections_continuity`, and
  `condensedContinuityComparison_representatives`. In particular its latter
  signature allows every normalized representative choice, not just one model.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs:
  `upperStar`, `lowerStar`, `upperStarLowerStarAdjunction`, the exactness
  instances and canonical coefficient change.
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback:
  `rightDerivedPullback`, its unit equation and its K-injective computation;
  ...RightDerivedFunctor.Triangulated: the canonical shift and exactness instances.
- Sheaf.CategoryTheory.ExactInputDerivedTransformation:
  `exists_unique_exactInputDerivedTransformation`, including its unit-normalized
  shift structures, universal transformation and two-resolution formula.
- Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence:
  `InternalAbelianSheafModule.sectionModuleEquivalence`;
  Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses:
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`.
- Sheaf.Algebra.Homology.KInjectiveProductsTermwise:
  `CochainComplex.termwise_product_isKInjective_and_isLimit`;
  Sheaf.AlgebraicGeometry.ProEtaleProductsDerived: `Scheme.ProEt.products_derived`;
  Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation:
  `Scheme.proEtale_immersion_inverseImage_preservesLimits`.
- Sheaf.Algebra.Homology.FunctorialBoundedInjectiveResolution:
  `CochainComplex.exists_functorial_bounded_injective_resolution`;
  Sheaf.CategoryTheory.KInjectiveComputes: `Functor.kInjective_computes`.
- Mathlib.AlgebraicGeometry.Sites.Proetale: `Scheme.ProEt`, `ProEt.topology`;
  Mathlib.AlgebraicGeometry.Scheme: `Scheme`;
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`;
  Mathlib.Algebra.Homology.DerivedCategory.Basic: `DerivedCategory`, `Q`;
  ...DerivedCategory.ExactFunctor: `Functor.mapDerivedCategory`;
  Mathlib.CategoryTheory.Triangulated.Functor: `IsTriangulated`, `mapTriangle`;
  Mathlib.CategoryTheory.Limits.Shapes.Products: `Fan`, `IsLimit`, product legs;
  ...Limits.HasLimits: `colimit`, `colimit.ι`, `colimit.desc`;
  ...Filtered.Basic: `IsFiltered`. The size and scheme-conventions nodes are
  metatheoretic conventions with no separate Lean declaration.

Searches run, with actual results:

1. msearch.py leanfinder, "Derived global sections restriction along closed
   immersions commutes with products and bounded below filtered colimits":
   eight hits, chiefly Scheme.Modules.restrictFunctorComp and restrictAdjunction
   for OPEN immersions; no exact combined module-derived assertion.
2. msearch.py loogle, `"rightDerivedFunctor", "prod"`: zero hits.
3. msearch.py leansearch, "Derived global sections restriction natural transformation
   closed immersion products filtered colimits": eight hits, chiefly
   Sheaf.natTransΓRes, ΓRes_naturality and pointwiseProductCompEvaluation;
   these are separate underived operations, not this statement.
4. msearch.py grep, `rightDerived.*(restriction|product)|restriction.*rightDerived`:
   zero hits in Mathlib.
5. rg of WeilConjectures, Sheaf and dag/lean_names_upstream.json for closed
   restriction, section restriction, derived sections and the proposed names;
   grep by the exact item id in WeilConjectures: no existing full statement.
   The existing supportedModelDerivedRestriction in
   Sheaf.Paper.SupportedImageRigidityFromModelComparisons uses exactly this
   adjunction-unit construction, precomposed with a degree-zero support-chain
   functor. It does not state the operations lemma and cannot be imported here:
   its node depends on this lemma. The shared generic rightDerivedPullback is
   reused directly; there is no second construction of right-derived descent.

Edge cases checked against the signatures: J empty is allowed for products,
so the zero/terminal product is included. Filtered J is nonempty exactly as
required by IsFiltered. Singleton diagrams and identity closed immersion are
included. Empty schemes, the zero coefficient ring and zero complexes are not
excluded. The lower bound a is any integer, with no strict positivity restriction;
vanishing refers to terms, not merely to cohomology. No upper bound is imposed
on complexes in the product or triangle clauses, and both resolutions in the
normalization may be unbounded. The filtered clause uses precisely a common
termwise lower bound. No extra coefficient, model, rigidity or complement
condition is introduced. No statement dispute or correction is needed.

Validation: scompile.py compiled the final module both in its isolated sandbox
and under its library module name, each within 60 seconds; no errors or
unexpected warnings. The sole theorem has proof `by sorry`; all definitions
have actual bodies. Diagnostic commands were removed. No live repository file,
launcher script, build setting or published artifact was edited.

## Second reading by NW

A separate side-by-side rereading of the current node and completed module checked
the actual maps, not just their sources and targets. The first draft needed a
public import for the canonical right-derived shift instances; this was repaired.
The filtered universal representative clause also needed an explicit existence
assertion to prevent a vacuous normalization contract. The final module adds
HasClosedRestrictionFilteredModel with natural isomorphisms, the same common bound,
the two actual cocones, the actual rho components and commuting chain squares.
The revised module compiled cleanly on the server.

The rereading checked that the two-resolution equality quantifies over arbitrary
s,j and that the exact pullback factorization is oriented from D(t^*)QK to Q(t^*K).
The triangle morphism includes its connecting square. Product comparisons are
uniquely induced by the original projection legs, and the product-of-components
map is the limit lift of the rho-postcomposed target cone. The filtered comparisons
are Q-images of colimit.desc on complexes; colimMap η appears on the correct side
of the square. The four normalization equations identify every arrow with the
canonical restriction and the original input cocone. Empty products, identity t,
zero objects, arbitrary integer bounds, site universes and coefficient generality
remain present. The node copy differs only in lean. This rereading was performed
by this worker; the dispatcher forbids starting another agent, and the delivery
is supplied for the maintainer's independent review as required by the prompt.
