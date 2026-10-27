## Worker report

The module `Sheaf.AlgebraicGeometry.FlatObjectFppfDerivedSections` states the
small-etale / big-fppf comparison in the derived category, together with compatible
resolution models before taking cohomology. It contains two postponed theorems,
`flat_object_fppf_section_extension` (the sheaf clause) and
`flat_object_fppf_derived_sections` (the comparison and diagram clauses). Their
proof docstrings reproduce the node's six-step proof and name its inputs. All
helper definitions have real data; no construction chooses an arbitrary comparison.

Clause-by-clause rendering:

- A scheme S and an algebraic space X/S are `{S : Scheme.{u}}` and
  `(X : AlgebraicSpace S)`. `M : X.Modules` is precisely the recorded original
  small-etale module category, with the same carrier universe u.
- Quasi-coherence is `hM : M.IsQuasicoherent`, the Mathlib local-presentation
  predicate supplied by `AlgebraicSpaceQuasiCoherentModule`; it is not replaced
  by a private notion, a condition on cohomology, or finite presentation.
- The choice of a small big site, all its objects and fibre products, and its
  jointly surjective flat locally finitely presented covers is the existing
  `(B : SpaceFppfSite X)`. Its fully faithful essentially surjective inclusion is
  made into `B.presentationEquivalence`. Thus a chart is represented in the same
  B, and its counit specifies the isomorphism with that chart; no new site is used.
- The ring with its actual regular-function sections and tensor restrictions is
  `(R : SpaceFppfRings B)`. In particular neither the ring nor its restrictions
  is an unconstrained parameter. `IsSpaceFppfSectionExtension R M Fa` identifies
  Fa at every object with Gamma of the actual `moduleTensorPullback`, including
  addition, scalar multiplication and its restriction/composition formulas.
- The assertion that this presheaf is a sheaf is
  `flat_object_fppf_section_extension`: existence of the module sheaf and the
  normalized section-extension data. No data are extracted from this sorry.
  The main theorem quantifies over ANY Fa and section normalization eFa, hence
  does not restrict the comparison to a conveniently selected extension.
- The given injective resolution is a Z-indexed `CochainComplex`, with
  `[J.IsStrictlyGE 0]`, `[∀ q : ℤ, Injective (J.X q)]`, and a `[QuasiIso ι]`
  augmentation `Fa[0] ⟶ J`. This is the stated notion of a nonnegative injective
  resolution; it uses Mathlib's existing predicates and does not copy them.
- Every flat h:T→X is an arbitrary T in B with
  `MapIsFlat (B.inclusion.obj T).hom`. This is the existing chartwise predicate
  using Mathlib `Flat` on schemes. The full site presentation includes X/X.
- The model's `complex`, `nonnegative`, `presheafIso`, `augmentation` and
  `quasiIso` give the actual nonnegative enlarged-etale acyclic resolution.
  `presheafIso` identifies every term on EVERY enlarged etale space V with J(V),
  not only its cohomology and not only values at scheme charts.
- The third per-object property conjunct (`augmentation_sections` in the returned
  version) specifies that its augmentation agrees with ι and
  tensor pullback: the required section s has on every compatible chart q the
  actual tensor `1 ⊗ x` transported by `moduleTensorComposition` and the triangle
  of the presentation counit. Its image under ι is exactly the displayed
  augmentation. The recorded enlarged/small equivalence's counit accounts for
  the coefficient section on V. Thus the augmentation is fixed, not an arbitrary
  quasi-isomorphism to the right complex.
- `sectionsIso` identifies the complex of global sections with the defined
  `flatObjectSectionComplex R J T`. the fourth per-object property conjunct says that all its
  projections to charts are the original restrictions of J. This determines the
  isomorphism as the usual global-sections identification.
- The derived functor in each model has a universal right-derived pair
  `derivedData.derived`, `derivedData.unit`, `derivedData.universal` for the EXISTING `Sheaf.Γ`, using the exact
  localization `DerivedCategory.Q`. This names RGamma without creating a new
  notion or assuming the comparison theorem. `comparison` is an isomorphism in
  `DerivedCategory AddCommGrpCat`, not merely an H^q isomorphism.
  `derivedData.comparison_normalization` fixes its inverse by applying the universal unit
  to the quasi-isomorphic resolution and the normalized sections isomorphism.
  Since Q(augmentation) is invertible, that equation uniquely determines it.
- For every flat arrow a:U→T, the main theorem returns ONE FUNCTION `transitions`
  of arrows and the flatness witnesses. Each value is a `FlatObjectFppfTransition`, a subtype of actual map data
  satisfying all seven conditions. Its `.val.coefficientMap` is the map F_T→a_*F_U. The first conjunct of its required property fixes it
  on every scheme chart by `moduleTensorSection ... 1 x`, followed by
  `flatObjectArrowTensorIso`: exactly the chosen tensor associator and Over triangle.
  The counit of the existing enlarged/small equivalence and the faithful ULift
  identify original sections, so no arbitrary coefficient map is permitted.
- The second conjunct of its required property is the degree-zero augmentation square: the augmentation of F_T
  followed by the transition equals coefficientMap[0] followed by a_* of the
  augmentation of F_U. The standard `singleMapHomologicalComplex` isomorphism
  accounts for applying a_* to a degree-zero complex.
- The third conjunct specifies the transition on every enlarged etale object V as
  restriction in the one J along the actual second projection U×_T V→V.
  `sectionTransport` identifies Gamma_T a_* with Gamma_U. The fourth conjunct, its projection formula, fixes the ordinary identification on every V.
  The fifth conjunct defines `sectionMap` as Gamma_T of the transition, followed by
  this specified identification. The sixth conjunct says this SAME sectionMap corresponds
  to J(T)→J(U) under the two `sectionsIso` maps.
- The seventh conjunct, derived naturality, is the fully expanded predicate
  `FlatObjectDerivedRestrictionSquare`. It states existence of Rf, its universal
  derived unit eta_f, and kappa: Rf then RGamma_T ≅ RGamma_U. Kappa's equation
  on EVERY complex normalizes it by the two RGamma units, eta_f, and the
  projection-normalized sectionTransport. The displayed naturality equation
  uses RGamma_T applied to Q(coefficientMap[0]) followed by eta_f, then kappa:
  precisely the canonical derived restriction, as in the recorded
  `ringedAcyclicResolutionDerivedMaps` interface. It says that arrow then the U
  comparison equals the T comparison then Q of J restriction. This is an
  equality of arrows in D(Ab), before cohomology; Rf and kappa are part of the
  asserted square, not extra assumptions supplied by the caller.
- `flatObjectSectionDiagram` retains exactly J's restrictions, including identities
  and composites. Every small diagram D with flat objects AND flat arrows hA
  receives a `FlatObjectFppfDiagramModel` predicate parameterized by the SAME transitions
  function. Its existential `identification` is a family of isomorphisms to the actual
  Gamma resolution complexes, with the first final conjunct pinning them to
  the comparison natural isomorphism. the final arrow equation requires that each
  diagram arrow, under these identifications, is precisely the `sectionMap` of
  `(transitions ... (hA a)).val`. This hA is used; it is no longer a discarded binder.
  The diagram thus uses Gamma of the coefficient-compatible derived transitions.
  the nonnegativity conjunct gives degree zero uniformly. The natural `comparison` gives a
  one-step zigzag of componentwise quasi-isomorphisms, including every face and
  any augmentation object and its arrows.
- In particular T=X, identity maps, composites, and arrows to X are covered by
  the same model and normalization. There is no quasi-compactness,
  quasi-separatedness, separatedness, finiteness or dimension hypothesis.

Universe convention: B is small in u+1, its section carriers are u+1, and the
original module remains in u. The recorded small/enlarged module equivalence
extends it with the same carrier size FIRST; then the existing
`AddCommGrpCat.uliftFunctor.{u+1,u}` transports the abelian coefficient sheaf.
This is the standard faithful common-universe realization of the same coefficients.
No equality of site object, morphism, original module, or derived Hom universes
is imposed. `HasDerivedCategory.{w}` binders select the localization universe,
as in def-weil-abstract-derived-category; they add no geometric hypothesis.
The independent diagram universe v allows empty, infinite, and arbitrarily
large small diagrams, including unboundedly many faces.

Recorded dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` (locally ringed
  space with local affine charts) and its morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `etaleTopology`, `structureSheaf`, `Modules`; structureSheaf is literally
  the presheaf of regular functions, with its sheaf-condition proof.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and the
  slice instances used by Mathlib `SheafOfModules.IsQuasicoherent`.
- `Sheaf.AlgebraicGeometry.SpaceCotangentRingMap`, the current recorded module
  of lem-trf-space-enlarged-etale-ringed-site-model, publicly exposes the original
  `EnlargedEtaleRingedSite` and `SmallEnlargedEtaleModules` interfaces:
  `enlargedSchemeInclusion`, `enlargedBaseChange`, `enlargedDirectImage`,
  `smallEnlargedModuleEquivalence`, and their specified restriction counits.
  The commutative structural ring-map addition is not needed by this theorem.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules` is transparently
  `SheafOfModules`, so the displayed module categories are the recorded ones.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic` and `.Resolution`:
  `Injective` and `InjectiveResolution`; the main statement writes the equivalent
  Z-indexed nonnegative resolution data using their constituent predicates.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q` and `QuasiIso`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`; and
  `.FinitePresentation`: `LocallyOfFinitePresentation`. Their chartwise
  space versions and covering families are reused through the existing site.
- `Sheaf.AlgebraicGeometry.SpaceFppfRingedComparison`: `SpaceFppfSite`,
  `SpaceFppfRings`, `IsSpaceFppfSectionExtension`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsFlat`.
- `Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange`:
  `moduleTensorComposition`, with its uniquely tensor-normalized signature.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `moduleTensorPullback`, `ModuleChart`, `moduleTensorSection`.

The last four owning DAG nodes have been added to stmt_deps, as authorized for
already landed notions. They name constructions already used by the mathematical
statement; no statement text, proof, proof dependency or other metadata is changed.
No new definition node or dependency repair was needed. Proof-only imports include
`SpaceFppfQCohHigherVanishing`, `RingedAcyclicResolutionDerivedMaps`,
`AlgebraicSpaceModulePullbackQuasiCoherent`, `LocalizedModuleExactForSystems`,
`SmallModuleDiagramsGrothendieck`, the existing exact-adjoint injective theorem,
and Mathlib's Grothendieck enough-injectives theorem. The two proof prerequisites
without usable records, lem-sfb-space-fppf-qcoh-descent and
lem-sfb-injective-pushforward-totally-acyclic, have no module to import; the
postponed proof docstring names them explicitly, as the accepted split does.

Edge cases checked mathematically before writing: zero M; empty algebraic space
and its empty coverings; T=X and identity arrows; maps from or to the empty
space whenever such a map exists; an empty index category; infinitely many
objects/arrows with no uniform finite face count; disconnected or nonseparated
spaces. None requires a nonempty index or additional geometric restriction.
The uniform lower bound is degree zero even for an infinite diagram.

Searches made with the prescribed msearch.py wrapper:

- LeanFinder: "quasi coherent algebraic space etale fppf derived sections
  comparison". Eight hits concerned etale scheme categories and their
  forgetful functors, not this comparison.
- LeanSearch: "derived sections of quasi coherent modules on algebraic spaces
  agree on the etale and big fppf sites naturally in flat morphisms". Eight
  hits were the existing quasi-coherence predicate and its local data.
- Loogle: `SheafOfModules, InjectiveResolution` returned no hit (its search
  endpoint did not recognize InjectiveResolution). Retried with `"fppf"`:
  ten hits gave the scheme fppf precoverage/topology and basic covering facts,
  with no derived-section theorem.
- msearch grep `fppf|Fppf` in AlgebraicGeometry: scheme fppf precoverage,
  quasi-compact covers and fpqc descent only.
- rg on lean/WeilConjectures for this node id: no hit. Concept search for
  fppf comparison and derived sections: scheme etale derived sections and
  unrelated comparison maps, no algebraic-space flat-object theorem.
- rg on lean/Sheaf finds the reusable SpaceFppfRingedComparison and
  SpaceFppfQCohHigherVanishing modules. They give the normalized site and
  higher direct-image vanishing, not this theorem or its simultaneous models.
- rg on Mathlib's ModuleCat sheaf/Presheaf, global-sections and homological
  functor files supplied evaluation, toSheaf, ULift, Gamma, universal derived
  pairs and complex functoriality, all reused rather than copied.
- rg on dag/lean_names_upstream.json, lean/WeilConjectures and lean/Sheaf for
  the new `flatObject` names: no existing declaration with these names.

Sources read: Stacks spaces-more-cohomology.tex lemma-review-quasi-coherent
(0DGN), including its proof and all clauses, and
lemma-cohomological-descent-etale-fppf-modules (0DGP). The unit text and direct
image proof were read in literature/blueprint/latest, the 2026-10-24 snapshot.
The derived and flat-diagram strengthening is the accepted node's explicit
resolution argument, not a different claim quoted verbatim from Stacks.
There is no statement dispute and no correction to the node or its unit.

Original delivery validation (before this repair): scompile.py compiled both
forms cleanly in 39.0 and 36.3 seconds. Repaired-source validation is below.
All compile attempts used the prescribed wrapper. The structures suppress unused
SizeOf and constructor-injectivity generation to stay within the 60-second budget;
no limit was raised and no field was removed. Standard sheafification, abelian and
global-sections instances are named to avoid repeated instance search.

## Second reading by Q129

This reading reopens the node and the repaired module together, including all
transition and diagram fields. It is a direct in-thread reading: the dispatcher
forbids starting other agents. It does not claim independent agent review.

1. The node's scheme S and algebraic space X/S are the explicit Scheme and
   AlgebraicSpace binders. Its original small-etale O_X-module is M:X.Modules;
   hM is the existing IsQuasicoherent predicate. No extra geometric condition
   occurs in the signature or structures.
2. The chosen small big-fppf site and regular-function ring are precisely B and R
   from SpaceFppfRingedComparison. The presentation equivalence and its counit
   supply representatives of all relevant objects. The added helpers do not
   replace this site or change its flat-lfp covering families.
3. The formula Fa(T)=Gamma(T,h*F) and tensor restrictions are eFa's existing
   normalized equivalences. The separate section-extension theorem asserts the
   sheaf clause. The comparison theorem still accepts every Fa/eFa and every
   given nonnegative injective resolution: J.IsStrictlyGE 0, Injective(J.X q),
   and QuasiIso of Fa[0]→J. This hypothesis match remains unchanged from the
   accepted per-object part of the returned delivery.
4. Every flat T→X is a model argument with MapIsFlat of its structural map.
   The model subtype's val.complex/val.presheafIso give the actual enlarged-etale restriction of J;
   the third property conjunct retains tensor pullback in degree zero. sectionsIso
   and its projection normalization identify its sections with J(T).
   derivedData contains derived/unit/universal for RGamma, comparison as an
   isomorphism IN D(Ab), and comparison_normalization fixing it. The maintainer explicitly accepted
   this part; its equations are preserved in the generic categorical record
   FlatObjectSectionDerivedComparison; the remaining per-object properties are
   required by FlatObjectFppfSectionModelConditions. No equation is weakened or dropped.
5. The naturality clause was missing in the returned head. The repaired
   FlatObjectFppfTransition now contains coefficientMap with the explicit
   1-tensor chart normalization and augmentation square as conjuncts 1 and 2
   of FlatObjectFppfTransitionConditions, required by the returned subtype. Its
   seventh conditions conjunct unfolds to FlatObjectDerivedRestrictionSquare, asserting
   Rf, a universal eta_f and kappa normalized by all the derived units. Its
   explicitly written composite is the canonical derived restriction and its
   equation is exactly the
   commuting D(Ab) square with the two accepted comparisons and Q(J restriction).
   This equation cannot be satisfied merely by producing a chain restriction
   map: its other side is independently fixed by the tensor coefficient map
   and the derived units. This directly repairs H3's first finding.
6. For all small augmented flat diagrams, the theorem returns a single
   transitions FUNCTION before quantifying over the diagram. The diagram model
   uses it in its final map equation for EVERY arrow, with hA passed to that function.
   Under identification, the arrow is sectionMap, which the fifth conditions conjunct defines
   as Gamma of that very transition, transported by the projection-normalized
   sectionTransport. The natural comparison and identification equation
   retain all face relations. The diagram may still be represented by J's
   strict section diagram, as the node's proof intends, but now that choice
   carries equations identifying every arrow with canonical derived restriction.
   It is no longer a substitute for stating that identification. This directly
   repairs H3's second finding and supports the consumer's face-column use.
7. Augmentations are included as objects and arrows of the arbitrary I. Their
   maps obey the SAME final map equation, degree-zero augmentation square,
   tensor formula, and derived naturality equation. In particular identity
   arrows and T=X use the usual small-etale/big-fppf comparison; no separate
   unspecified augmentation map is introduced.
8. The node's uniform lower bound is nonnegative on both the per-object
   resolution and every diagram complex. The empty diagram, infinite diagrams,
   zero coefficient module and empty spaces remain allowed. No finite face
   count, quasi-compactness or separatedness was added. The original module
   universe u, faithful abelian lift u+1, independent diagram universe v and
   derived Hom universe w are retained.

This section makes the clause match itself and records the actual mismatches
found and changed, rather than deferring it to the worker report (H11).

## Returned delivery repair

Compared with immutable returned head a2cbd3d72e1c, H3 is repaired by the new
coefficient-map normalization, augmentation square, derived-pushforward and
composition units, derived naturality equation, one transitions function, and
Gamma-of-transition map equation on diagrams. H11 is repaired by the explicit
hypothesis-and-clause reading above. The accepted per-object comparison equations are retained.
The node's mathematical statement is unchanged; only its Lean binding is updated.
The current shared main has no landed module for this item; the node was compared
with its current main record and retains that mathematical statement verbatim. The delivery wrappers
will rebase this repaired content on current main; no direct Git operation is used.

The relevant consumer lem-sfb-fppf-face-heart-derived-unit was read: its step 2
requires augmented face-compatible DERIVED section identifications, and its
step 5 uses those identifications for the actual augmentation unit. The added
augmentation square, the derived square and final diagram-map equation supply precisely
those requirements for every face arrow and augmentation, with no degeneracy
flatness requirement.

The diagram's data and equations are now expressed by an explicit existential
predicate rather than a structure, avoiding generated induction principles. It
retains the same comparison, identification family, degree-zero bound and arrow
equations. No clause is removed by this factoring.

Generic categorical helpers factor the types for elaboration:
A fresh rg search for all new helper names in both lean/Sheaf and
lean/WeilConjectures returned no matches.
FlatObjectSectionDerivedComparison retains the accepted per-object normalization.
FlatObjectFppfSectionModelData (an instance of generic FlatObjectSectionModelDataCore) stores the per-object maps and comparison data;
the model subtype property requires nonnegativity, the augmentation quasi-isomorphism,
the full tensor augmentation formula and section-projection normalization.
FlatObjectFppfTransitionData (an instance of generic FlatObjectTransitionDataCore) stores four actual maps, while its seven explicit
conditions are factored into FlatObjectFppfTransitionConditions and required by
the returned transition subtype's property. No condition is dropped.
The predicate FlatObjectDerivedRestrictionSquare expands to the new Rf/kappa
unit normalization AND the explicit derived naturality equation. The latter is a
predicate defined in full with existential functors and maps, not a hollow choice
or an assumption on geometric input. These belong to this node's comparison notion
and introduce no independent site, tensor functor or derived-functor definition.
The helpers flatObjectCoefficient, flatObjectCoefficientSection and
flatObjectArrowTensorIso use only existing coefficient extension, its counit,
and moduleTensorComposition. The general acyclic-resolution derived-map theorem
was read and its RG/Rf/kappa formulas reused.

Repair compile: scompile.py exited 0. Its overlay attempt reached the time limit;
the wrapper then confirmed against current server sources, which compiled cleanly
in 33.9 seconds with no errors or warnings. The compiler limit was unchanged.
An earlier repair dry run returned OK at 947e5f10209. Its subsequent push
attempt timed out in compilation and pushed nothing. The diagram predicate was
then factored to reduce elaboration cost; final validation follows below.

The two actual data records are factored through generic category parameters to
avoid repeated kernel checking of expanded geometric categories. Their specialized
interfaces are transparent abbreviations; all maps and all conditions are unchanged.

Final transition data projection key (the named components above use these actual
product projections): coefficientMap = d.1; chain map = d.2.1;
sectionTransport = d.2.2.1; sectionMap = d.2.2.2. The returned transition subtype
requires all seven conditions on this product. In the final diagram arrow equation,
`(transitions ...).val.2.2.2` is precisely that sectionMap; conjunct 5 specifies it
as Gamma of d.2.1 followed by d.2.2.1. The product replaces generated constructor
machinery and does not replace or omit any of the specified maps.

Transitions now parameterize the underlying per-object model data. The theorem
still returns models satisfying every per-object property, and passes their .val
to each transition. This avoids repeating the full validity predicate in every
map type; it does not drop the validity of any returned model.

Final clause names: per-object Nonnegative, QuasiIso, TensorAugmentation and
SectionProjections, prefixed FlatObjectFppfSectionModel, are the four explicit
conditions. The seven transition predicates, prefixed FlatObjectFppfTransition,
are TensorCoefficient, Augmentation, Restriction, SectionTransport, SectionMap,
SectionIdentification and DerivedNaturality. The two Conditions predicates conjoin
exactly these lists. DerivedNaturality unfolds to FlatObjectDerivedRestrictionSquare;
its formula is the RG/Rf/kappa derived square described in the second reading.

Final repaired-source compile: scompile.py compiled both forms without any error
or warning: sandbox 38.7 seconds; library module 40.6 seconds. All declarations
and the theorem signature in the node record were refreshed from this source.

Final repair dry run: deliver2.py --no-push returned OK at 11516089142,
passing preflight and compilation with nothing pushed.
