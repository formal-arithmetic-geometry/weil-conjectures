## Worker report

Group NH, item `lem-sfb-proper-scheme-deformation-hull`, stage 2, 2026-10-24.
The item is stated in `lean/Sheaf/AlgebraicGeometry/ProperSchemeDeformationHull.lean`
as `AlgebraicGeometry.ProperSchemeDeformation.exists_hull`. Its only postponed
proof is `sorry`; the complete six-step DAG proof, including the dependency names,
is in the theorem docstring. All helper definitions have real data. The original
statement, proof, source and proof dependencies are unchanged. Four definition
nodes supply the missing normalized interfaces, rather than assume them.

Hypothesis and clause correspondence:

- A field is `{k : Type u} [Field k]`. The scheme and its structural morphism are
  `{X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]`. An explicit morphism is
  used because the recorded marked-lift/cotangent declarations take that morphism.
  No smoothness, reducedness, characteristic, rational-point or separability
  assumption is introduced. `C : Coherence` and `D : SheafCotangent.Comparison C`
  are the existing coordinate models of the standard cotangent resolution, not
  assumptions that the deformation functor has a hull or a tangent equivalence.
  Their existence is already stated by the cotangent framework. Derived-category
  instances choose presentations of the actual derived categories; the sheaf Hom
  universe `w` remains independent of the small ring Hom universe `u+1`.
- `ArtinDeformation.TestCategory k k` is exactly the recorded Artinian local
  augmented k-algebra category. Its `IsArtinianRing` is Mathlib's descending-chain
  condition on ideals. The surjective augmentation kernel is the maximal ideal,
  and arrows commute with the specified residue map and are local. There is no
  added finite-length assumption.
- `ProperSchemeDeformation.Deformation f R` is the proper-object full subcategory
  of the existing `SchemeDeformation.Lift f (reduction R)`. The latter records
  flatness and the cartesian marking square. `Classes f R` quotients by marked
  isomorphisms, retaining precisely the required marking. `ClassFunctor` requires
  actual cartesian base changes to exist and fixes the class map on EVERY such
  representative. Its identity and composition fields give the stated functor.
- `Hull.algebra : CompleteLocalAlgebra k k` records Noetherianity, locality,
  maximal-ideal completeness and the specified residue-field equivalence. `eta`
  is defined on the existing `LocalMap` type. These are k-algebra maps preserving
  the residue marking. Every such local map is automatically adically continuous:
  it sends m_B^n into m_R^n, for every n. Thus omitting a separate topological
  proof field removes no continuity condition.
- `Hull.naturality` is the naturality equation under composition. `Hull.lifting`
  quantifies over EVERY surjection `q : R' ⟶ R`, every element over R and every
  deformation over R' with matching reduction, and produces a compatible lift.
  `Hull.tangent` is bijectivity at the actual square-zero algebra k ⊕ k.
  This is the required hull definition, not merely existence of a versal point.
- `HullConclusion.functor` and `.hull` assert existence of exactly that functor and
  hull. `.properTangent`, `.transport_exists`, and `.transport_class` identify
  its dual-number class set with the existing ordinary marked-lift class set.
  The two framework models of dual numbers have different recorded right-module
  instances. `dualRingIso` is the explicit coordinate identity (a,b) ↦ (a,b),
  and `IsTangentTransport` fixes projection and marking through its Spec iso;
  no untyped identification of those models is used.
- `TangentExt C D f` is the existing full standard sheaf cotangent complex in
  nonpositive degrees, in derived Hom to the SINGLE structure sheaf shifted by 1.
  It is not a bounded cotangent complex, cotangent homology, Zariski cohomology of
  an unrelated sheaf, or Ext with an arbitrary coefficient object.
  `coefficientUnit f` is the canonical tensor-pullback unit map, and `extModule`
  is the existing derived structural k-action on that Hom group.
- `TangentIdentification.split_normalization` now pins the split class map on
  EVERY marked lift and every finite-dimensional coefficient module to
  `SchemeDeformation.extensionClass sheaf (extension M Y).extension a` for EVERY
  normalized conormal representative `a`. Its fields `sheaf`, `kernel`,
  `coefficient`, `coefficient_sections` and `extension` supply the sheaf
  classification, actual lift kernel, section-normalized coefficient isomorphism,
  and `SplitLiftExtension`. The sheaf classification's `cl_normalization`
  guarantees representatives exist; their polynomial-relation and differential
  formulas fix the extension class and its sign. Origin, addition and coefficient
  naturality alone did NOT pin the earlier split class map: they left a linear
  automorphism ambiguity. `TangentIdentification.normalization` now composes
  this pinned class map with the canonical coefficient-unit map.
  `HullConclusion.properVector` and `.proper_normalization`
  transport this identification to the PROPER class set. `.hullVector` and
  `.hull_normalization` transport it to h_B(k[epsilon]); this is relative to the
  CHOSEN hull eta. Each is an actual k-linear equivalence with the canonical Ext
  module. `.finite` is `Module.Finite k (TangentExt C D f)` for that canonical
  action, hence finite-dimensionality over the field.
- `.tangent : TangentNaturality` simultaneously supplies the global and EVERY open
  tangent identification. Each `opens U` is itself a `TangentIdentification`, so
  the same sheaf-extension normalization pins EVERY open map independently of
  the restriction square. `restrict_exists` gives actual cartesian restrictions;
  `restrict_class` specifies the map on every such representative. `commutes` is
  the derived open cotangent restriction equation, with the existing coefficient
  restriction and the canonical coefficient-unit map. The open scheme need not
  itself be proper, as required for this clause.
- `.completion : ClosedCompletionCompatibility ... tangent.global` uses the SAME
  global tangent identification. At each closed point, `localAlgebra f x` is the
  ACTUAL scheme stalk with its existing structural field map. `StalkComparison`
  supplies the exact stalk functor, full cotangent derived comparison normalized
  on every standard section, and structure-module comparison normalized on germs.
  Its `.ext` is the actual derived functor applied to the Ext morphism, with the
  fixed shift and coefficient maps. This prevents an arbitrary comparison map.
- `IsStalkDeformation` is a ring isomorphism to the actual deformation's stalk at
  its marked point, fixing structural scalars and the marking map. `stalk_exists`
  guarantees these representatives exist. Completion is the actual inverse limit
  at the inverse image of m_x, with coordinate, scalar and EVERY finite-quotient
  marking equations (`CompletionOf`). `Comparison.completion_class` specifies
  its class map on every such completion.
- The lower completion arrow is `CompletedSchemeTangent.extMap`: exact extension
  of scalars to the completion, not an arbitrary function. The completed complex
  is the scalar completion of the actual two-term localized polynomial conormal
  complex. With finitely many polynomial variables its degree-zero module is
  precisely the completed polynomial differential module (continuous
  differentials); it is NOT ordinary Kaehler differentials of the completed ring.
  `Representative.relations` says that the cocycle on a relation is its epsilon
  coefficient, fixing both the class and the sign. `Comparison.representatives`
  and `.normalized` pin the completed class equivalence on all such representatives.
  `ClosedCompletionCompatibility.commutes` equates this completed class to the
  scalar-extended Ext representative of the stalk of the global class.
  `ext_representatives` guarantees representatives exist, so the square is not a
  conditional assertion with a possibly empty premise. `.localNoetherian` and
  `.localPresentation` provide the actual Noetherian and finite-presentation data
  needed to use these continuous models at every closed point; these follow from
  properness over k and are auxiliary to the completion construction.
- `.rigidity` assumes every relative sheaf derivation is pointwise zero on every
  open and section. Relative to `tensorPullbackRingMap f`, this means precisely
  k-linear sheaf derivations O_X → O_X. The conclusion is bijectivity of THIS
  hull's `eta A` for EVERY Artin algebra A. Together with `.naturality`, this is
  the requested natural isomorphism and prorepresentation, not just existence of
  some other prorepresenting hull.

Dependency declarations used (module and name):

- Mathlib `Field`, `AlgebraicGeometry.Scheme`, `IsProper`, `Flat`, and the scheme
  pullback machinery, in `Mathlib.AlgebraicGeometry.Scheme`,
  `.Morphisms.Proper`, `.Morphisms.Flat`, and `.Pullbacks`.
- `Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory`:
  `ArtinDeformation.TestCategory`, `ring`, `residue`, `map`, `squareZeroTest`,
  `CompleteLocalAlgebra`, `LocalMap`. `ArtinRSTangentTensor.squareZeroMap` is part
  of the coefficient-direction interface imported by the class-functor module.
- `Sheaf.AlgebraicGeometry.MarkedSchemeLifts`:
  `SchemeDeformation.Lift`, `Classes`, `IsBaseChange`, `IsRestriction`,
  `cotangentComplex`, `Ext`, `directionReduction`, `directionModule`, and the
  recorded opposite coefficient module. These are used rather than copied.
- `Sheaf.AlgebraicGeometry.SchemeCoefficientExtensionProblems`:
  `SchemeDeformation.SplitLiftExtension` and `extensionClass`.
  `Sheaf.Topology.ZariskiSheafAlgebraExtensionExt`:
  `TopCat.SquareZeroSheaf.Classification`, `ConormalClass`, and the sectionwise
  conormal normalization `Classification.cl_normalization`. These pin the split
  map directly at the definition level; the full scheme torsor theorem is not
  supplied as a new hypothesis.
- `Sheaf.AlgebraicGeometry.SchemeLiftClassificationData`:
  `SchemeDeformation.SplitClassification`, `extMap`, and the existing sheaf
  `Derivation'` type. `SchemeCotangentOpenRestriction`: `OpenComparison`, its
  `.ext`, and `directionRestriction`.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`:
  `Scheme.Modules.tensorPullbackObjUnitToUnit`.
  `Sheaf.AlgebraicGeometry.ProperSchemeCoherentExtFinite`:
  `Scheme.Hom.coherentExtModule` (the actual scalar action), with the recorded
  proper Ext finiteness theorem imported for the proof plan.
- `Sheaf.RingTheory.NaiveCotangentComparison`:
  `Naive.Presentation`, `complex`, `conormalIso`, `kernelClass`,
  `IsLocalizedPolynomial`, `Comparison`, and its normalized comparison map.
  `SchemeDeformation.affineArrow` comes from the recorded
  `Sheaf.AlgebraicGeometry.AffineSchemeDeformationComparison` interface.
- `Sheaf.RingTheory.MarkedFlatAlgebraDeformations`:
  `Algebra.FlatDeformation.Groupoid`, `algebra`, `scalar`, `marking`, `ideal`,
  `IsCompletionMap`. No private replacement algebra-deformation groupoid is used.
- `Mathlib.RingTheory.AdicCompletion.Basic`, `.AsTensorProduct`, `.LocalRing`:
  `AdicCompletion`, its canonical scalar map and flatness over a Noetherian ring.
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` supplies the actual
  derived exact-functor comparisons; `ModuleCat.extendScalars` and its exactness
  are the existing scalar-extension functor and Mathlib instances.
- `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`:
  `RingedSpace.moduleStalkFunctor`.
  `Sheaf.AlgebraicGeometry.IsolatedCurveFormalLifting`:
  `isolatedCurveScalarToStalk` (general structural scalar map, no curve hypothesis).
- The remaining Mathlib leaves of the original `stmt_deps` are used through these
  interfaces: `IsNoetherianRing`, `IsAdicComplete`, `KaehlerDifferential`,
  `DerivedCategory`, `HasDerivedCategory`. The recorded `Abelian.Ext` applies to
  degree-zero objects; the node explicitly defines complex Ext as derived Hom,
  which is used directly rather than changing its domain.
- Recorded proof modules imported in the item are
  `PointwiseFlatnessBaseChange`, `SchemeSquareZeroLiftTorsor`,
  `ProperSchemeCoherentExtFinite`, plus the Mathlib Artinian/Noetherian and
  proper-base-change leaves. Unstated proof dependencies remain named in the
  proof docstring; none is smuggled in as a hypothesis of the hull theorem.

Sources were read locally, especially examples-defos.tex 0DY9/0DYA/0ET5,
open restriction 0DYW and completion 0DYV/0DZM, and the existing normalized
cotangent, split classification and continuous-completion interfaces. The current
blueprint search has no separate exact item unit; `blueprint_refs.py ancestor`
returns `None` for the inherited support-node chain. New nodes preserve that
inherited `from.node = null` and the item's full source place and ancestry.

Edge cases checked before finalizing the statement:

- X empty: proper class sets are singletons, Ext-one is zero, no closed-point
  completion requirement remains, and B=k is possible.
- R=k and identity arrows: the marking rigidifies the residue fibre; all naturality
  and lifting equations specialize correctly. Lifting is not restricted to small
  extensions. The kernel-zero presentation is allowed.
- Singular/nonreduced X and inseparable residue fields are allowed. No assertion
  that the full cotangent complex is bounded below is made. Finiteness uses its
  good truncation only in the proof plan, as the source does.
- An arbitrary open U can be nonproper or empty; ordinary marked lifts are used
  for restriction. Closed x need not be k-rational, and the base field is never
  replaced by its residue field.
- For A=k[t]_(t), the completed differential module is k[[t]] dt, rather than
  ordinary differentials of k[[t]]. A= k is also allowed, with zero conormal Ext.
  Finite polynomial variables are explicit; infinite localized polynomial models
  are not used to define continuous completion.
- A flat dual-number deformation of complete Noetherian local A is itself local,
  Noetherian and complete: its epsilon kernel is A, nilpotent with the induced
  finite module filtration. Marked isomorphisms between such rings are local and
  automatically adically continuous. Thus use of the existing flat algebra
  groupoid introduces no extra noncontinuous isomorphism classes.
- Completion and stalk coordinates are constrained on actual scalar maps,
  markings, germs and relations. No arbitrary map, unrelated nonempty choice or
  stronger input assumption supplies the required compatibility square.

Searches (recorded by msearch.py in searches.jsonl; verbatim structured results
also appear in each new definition node):

- Loogle `IsArtinianRing, IsAdicComplete, IsLocalRing`: one Artinian completeness
  hit, no deformation-hull interface.
- LeanFinder `A proper scheme over a field has a hull for its deformation functor
  with tangent space cotangent complex Ext one`: eight unrelated scheme/moduli
  hits, no exact declaration.
- LeanSearch `Marked proper flat scheme deformation functor isomorphism classes
  Artinian local algebras and hull`: eight unrelated hits, no class-functor/hull.
- Mathlib grep `Schlessinger|deformationHull|versalDeformation`: zero hits.
- LeanFinder `Continuous cotangent complex classifies first order deformations of
  completed local algebras by conormal Ext one`: eight ring cotangent/module hits,
  no continuous completed marked-deformation comparison.
- Mathlib grep `continuous.*cotangent|completed.*cotangent|[Cc]onormal.*[Dd]eformation`:
  zero hits.
- LeanSearch `The cotangent tangent identification of a proper scheme commutes
  with taking stalks and continuous completed local rings`: eight localization,
  local-ring and stalk hits. Those basic objects are reused; no full comparison.
- LeanFinder `Canonical cotangent complex stalk comparison and continuous
  completion of a local scheme deformation tangent class`: eight ring cotangent
  localization hits, no scheme/global-completion tangent compatibility data.
- Mathlib grep
  `StalkComparison|ClosedCompletionCompatibility|TangentIdentification|ProperSchemeDeformation`:
  zero hits. The corresponding searches of lean/WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json also have no matching interface.
- DAG text searches found the existing test/lift/classification frameworks used
  above; `lem-sfb-completed-local-deformation-tangent` has no Lean record and
  states the theorem, not the definition of the comparison data. The existing
  `lem-sfb-naive-cotangent-stalk-comparison` concerns a two-term stalk theorem,
  while this item uses the full standard cotangent complex. Finite-power-series
  Jacobian nodes concern presentations of smooth/lci calculations, not this
  general class-functor/hull or continuous tangent equivalence.
- Blueprint searches for deformation hull, marked deformation and continuous
  completion tangent found no duplicate definition. Source, Mathlib, DAG and
  project searches precede the four new data definitions.

Validation: all five delivered modules passed scompile.py on the live server,
with no errors or unexpected warnings. The final preflight/delivery checks are
recorded below after running the prescribed wrapper.

No STATEMENT-DISPUTED finding and no statement correction.

## New nodes

`def-sfb-proper-scheme-deformation-data` defines the actual proper marked
isomorphism classes, their cartesian class functor and the complete-local hull
with all-surjection lifting and tangent bijectivity. Sources: Stacks 0DY7, 0ET5,
06IX and 06JL. Existing test algebras and marked lifts are used. The existing
framework does not define the proper class functor or the hull of that functor.
The three kinds of searches above found no such interface.

`def-sfb-completed-scheme-tangent-data` defines finite localized polynomial
presentations, completed conormal complex/Ext and the actual completion relation,
with epsilon-relation-normalized tangent comparison. Sources: 0DYV, 0DZM, 0GPZ,
07ED and 07NJ. Existing completions, naive complexes and marked algebra
deformations are reused. The theorem node for completed-local tangent
compatibility has no Lean definition of these normalized data. Ring cotangent
homology and continuous Jacobian presentation hits are not this class comparison.

`def-sfb-proper-scheme-tangent-data` defines the explicit transport between the
framework's two dual-number models and the normalized global/open linear tangent
identifications. Sources: 0DY9, 0DYW, 0GPZ and 0GQ1. The repaired identification
requires the section-normalized sheaf classification, actual kernel, coefficient
isomorphism and SplitLiftExtension, and pins SplitClassification.classes by the
extensionClass equation on every conormal representative. It reuses these data,
OpenComparison and tensor-pullback unit rather than creating alternative notions
of cotangent complex, deformation, restriction or scalar action. None of the
three search kinds supplied this combined normalized tangent interface.

`def-sfb-proper-scheme-stalk-tangent-data` defines the normalized full cotangent
stalk comparison, actual deformation-stalk relation, and continuous closed-point
compatibility square. Sources: 0DYV, 0DZM, 08SF, 08UW and 07NJ. It reuses the actual
stalk functor and the existing structural scalar-to-stalk map. The two-term stalk
theorem and ring localization results found by the searches do not define this
full global-to-completed class square. These are data types with explicit
normalizations; their existence is asserted only by the item's theorem.

Final prescribed dry run: `deliver2.py NH lem-sfb-proper-scheme-deformation-hull
--no-push` printed `OK (dry run): commit 3f61504cee3 passes the preflight and
compiles; nothing pushed`. All five files compiled against the live server build;
no errors or unexpected warnings remained. Preflight metadata repairs corrected
signature extraction at a named argument and removed a local-instance inventory
entry; neither repair changed the mathematical statement.


## Repair of returned delivery aa39769fd87c

H3: repaired the missing canonical normalization of the global and open tangent
identifications. The previous claim that vector operations and coefficient
naturality determine the canonical split map was incorrect: those laws permit
composition with a k-linear automorphism of Ext-one. No appeal to open or
completion compatibility resolves this ambiguity in general.

`TangentIdentification` now directly carries `sheaf`, `kernel`, `coefficient`,
`coefficient_sections`, `extension`, and `split_normalization`. These reproduce
the defining normalization used by `Classification.split_normalization` in the
existing scheme torsor interface, without assuming that whole theorem as a
hypothesis or choosing an arbitrary class map. `LiftKernel.base` fixes the
inclusion using structural sections; `coefficient_sections` sends the actual
base-kernel epsilon section to the corresponding tensor direction;
`SplitLiftExtension` fixes its ring, quotient, inclusion and k-action against
the actual marked lift. Finally `split_normalization` requires the split class
to equal the concrete `extensionClass` computed using the polynomial-conormal
representative. This condition is inhabited for each extension by
`sheaf.cl_normalization`; it cannot be evaded by supplying no representatives.

The repair applies equally to `global` and every `opens U`, including U = top
and nonproper U. The existing `proper_normalization` and `hull_normalization`
then pin the proper and hull tangent maps by composition with this canonical
map. For a smooth projective curve of genus at least two, even when affine
completed Ext targets vanish, a GL twist must now satisfy the extension-class
equation on every lift, so that former ambiguity is removed. Empty X and the
trivial lift still give zero, and coefficient modules include M = 0 and M = k.

Compared the retained delivery packet with current main: all four helper nodes
and five Lean modules remain unlanded; the item's main-branch node differs only
by the delivered Lean record and the added definition dependencies. The wrapper
will build this repaired packet on current main. The repair changes the tangent
data module and its new definition node, plus this report. The original item
statement, six proof steps and theorem hypotheses are unchanged. No statement
correction is needed.

Validation of this repair: scompile.py compiled all five delivered modules on
the live server with no errors or unexpected warnings, including the consuming
stalk-completion data and hull theorem modules. The prior dry-run result above
belongs to the returned packet; this repair receives a fresh dry run below.

Fresh repair dry run: `deliver2.py NH lem-sfb-proper-scheme-deformation-hull
--no-push` printed `OK (dry run): commit 9045e8c2248 passes the preflight and
compiles; nothing pushed`. This validates the repaired definitions and all
five delivered modules against current main and the live server build.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
