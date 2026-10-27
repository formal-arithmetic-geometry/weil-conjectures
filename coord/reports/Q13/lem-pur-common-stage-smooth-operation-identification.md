## Worker report

The theorem module states `commonStageSmoothOperationIdentification`, with its full conclusion
in `Result`. The only postponed proof is that theorem. All helper definitions have
real data or are explicit Prop-valued specifications of the owning node's conclusions.
The item gains only the definition dependency described below; its mathematical statement
and proof plan are unchanged.

Hypothesis and clause correspondence:

* The global geometric datum is `D : FiniteFieldDatum`, the coefficient prime is
  `l` with `[Fact l.Prime]` and `hl : l ≠ D.p`, and the fixed coefficient closure
  is `Ω` with its field, Padic algebra and algebraic-closure instances. These are
  the global part of `PurityFiniteSetting`; a fixed finite level is not used by
  this node, which quantifies over every finite coefficient field.
* `X` and `Y` are schemes over `Spec D.k`, with `LocallyOfFiniteType`,
  `QuasiCompact` and `IsSeparated` structure maps. `f.IsOver` is the k-morphism
  condition. `IsSeparated f`, finite type, `d : ℕ` and
  `SmoothOfRelativeDimension d f` give exactly the stated geometric hypotheses.
  The explicit Noetherian, finite-dimension and stalk-unit instances are the
  consequences needed to type PBC categories; the residue-field invertibility
  instances type the actual derived pullback and twist functors. The coefficient
  comparison dependency proves these consequences for the given schemes; they
  impose no additional geometric condition. Scheme and closure universes are
  `max u v` and `v`, as required by the recorded exceptional System interface;
  arbitrary scheme and closure sizes are covered by enlarging the ambient size.
* The framework categories are `GeneralAlgebraicallyClosedCoefficients.Stage`
  and `generalAlgebraicallyClosedConstructibleCategory`, the PBC categories are
  `pbcStageCategory` and the pair category of `pbcScalarSystem`. `JX,JY` are the
  recorded `FdCoefficientComparison` data, with normalized integral identity,
  finite rational functors, scalar chi comparisons and exact common equivalences.
* `finiteOperation false` is `RationalSmoothPurityCanonical.rationalSource`:
  actual pullback with the shifted Tate line and the specified tensor symmetry
  and shift identifications. `finiteOperation true` is the rational right
  adjoint of the specified exceptional `System` at the fixed compactification.
  `commonOperation` uses the actual `commonSource` and the closed operation of
  that same System. No arbitrary operations are parameters.
* `pbcOperation` transports the same localized integral operation through the
  recorded finite coefficient equivalences; `finiteComparison` is r, fixed by
  their unit. These equivalences are identity on the common integral presentation.
* `strictComparison` is the actual pullback/tensor/twist/shift comparison or the
  coefficient-passage exceptional comparison of S, with both stage-to-tensor
  endpoint maps. The typed j components are identified by HEq with the inverse recorded
  chi-normalized family beta maps. `OperationSpec`'s mixed-square
  equation uniquely pins the ordinary PBC comparison to these specified maps.
  `CoherentExactMorphism` retains its unit/associator/shift coherence.
* `Result` existentially states both descended exact families `H,G` and both
  isomorphisms `RH,RG`. `OperationSpec` fixes their stage functors and every
  component. `objectComparison false` is the existing
  `commonSourceComparison`, retaining scalar completeness and tensor unitors;
  the exceptional normalization is the inverse System common comparison.
  The common component is the image of that normalization followed by the
  class of r. No repeated-field transition is set equal to the identity.
* `RepresentativeSpec` gives the explicit beta/finite-map/beta-inverse formula
  on every representative and the enlargement identity. Here beta is
  the node's a or b. `FrameworkRepresentativeSpec` gives precisely
  j_target J(u) j_source inverse, using beta = inverse j. Naturality of RH/RG
  supplies agreement with the actual framework arrow actions.
* `DescentSpec` gives exactness, representative independence, components of
  descended transformations and all equation, identity and composition clauses.
  `TransformationSpec` repeats the particular inverse equations and their
  actual single-stage representatives to expose the last paragraph of the node.
* `TransportSpec` states existence of theta^s and theta_E^s, pins the finite maps
  by r_G inverse theta r_H through the fully faithful finite J, fixes the common
  components by `objectComparison`, and states the conjugation equation through
  RH,RG. For a compatible inverse psi it gives both inverse framework equations.
* The final clauses of `Result` state exactness of the two actual operations
  and their descents, shift compatibility of RH/RG and descended exact natural
  transformations, and the descended shift maps normalized at every stage
  with both finite-stage inclusion shift maps retained.

Dependency declarations read and used:

* Sheaf.Paper.PurityFiniteSetting: WeilConjectures.PurityFiniteSetting, its
  FiniteFieldDatum/coefficient fields (through the public dependency imports).
* Mathlib.AlgebraicGeometry.Morphisms.Smooth: SmoothOfRelativeDimension.
  The morphism-properties node is explicitly a convention with no declaration.
* Sheaf.Paper.SfRationalizationKaroubi: sfRationalConstructibleCategory and its
  raw localization; GeneralAlgebraicallyClosedCoefficients supplies Stage,
  stageSystem and the literal framework pairs.
* Sheaf.Paper.PbcRationalCategory, PbcScalarExtension, PbcQbarCategory: the
  actual PBC raw stages, scalar system and literal pair-category carrier.
* Sheaf.Paper.PurFrameworkPbcCoefficientCategoryComparison and its public
  FdCoefficientComparison: canonical normalized J, stage functors, family beta,
  pair equivalence, finite_functor and shifts.
* Sheaf.Paper.DerivedPullbackTensorHom and
  IntrinsicCoefficientTwistsUnrestricted: the actual operations used publicly
  by PuritySourceTransports.rationalSource/commonSource/sourceScalar and
  commonSourceComparison; operationStageTransitionIso retains scalar endpoints.
* Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients: System,
  ring.operation, fields.rationalComparison and common.commonComparison.
* Sheaf.Paper.RationalScalarComparisonIdentification: the specified ordinary
  comparison identification, used in the proof plan. Its actual source and
  exceptional construction interfaces are publicly imported and used above.
* Sheaf.Paper.PbcDescentFunctors: CoherentExactMorphism, DescentSpec;
  WeilConjectures.CategoryTheory.StageSystem.Functor supplies Morphism.functor,
  Hom, descNatTrans, mapAt, and the literal representative construction.

Proof-only dependencies are recorded in the theorem proof docstring. The still-unstated integral-coefficient-model comparison
has no module to import; its mate calculation is retained verbatim in the
owning theorem's proof docstring rather than replaced by an assumption.

Searches (2026-10-25): msearch LeanFinder query "Identify strict completed and
ordinary tensor common-stage descended smooth pullback twist shift and exceptional
functors by canonical coefficient conjugation" returned eight generic shift
calculus results, no match. msearch LeanSearch query "Descent of natural
transformations through equivalences of filtered stage coefficient categories with
prescribed representatives" returned generic Equivalence and quotient-natural-map
results, no actual smooth-operation identification. Loogle "CategoryTheory.NatIso,
CategoryTheory.Functor" reported unknown NatIso; the repaired query
"CategoryTheory.Functor, CategoryTheory.Equivalence" returned twelve generic
functor/equivalence declarations, no match. Mathlib grep
"commonStage.*[Ii]dentification|[Ss]moothOperation" in CategoryTheory returned
zero hits. Ripgrep of lean/WeilConjectures and lean/Sheaf for the item id,
commonStageSmoothOperation and smoothOperationIdentification returned no match.
The existing upstream generic StageSystem descent was read and reused, rather
than restated. The finite presentation and normalization definitions are isolated in a definition node
to respect the per-file compilation limit; all pre-existing operations and categories are reused.

Edge cases read before drafting: d=0 is represented by the actual zero twist
and zero shift; no positive-dimension hypothesis occurs. Empty schemes and
zero complexes are admitted by every binder. Finite-stage fields E,F and the
representative common field M need not be equal; the representative formula
and enlargement equation quantify over arbitrary endpoint fields. For E=F
strict tensor is retained and removed by its completeness unitor. Ramified
finite extensions are allowed; no flatness of quotient coefficient maps or
faithfulness of scalar transitions occurs. Inverse equations descend at a
single field and are reflected only through the actual common equivalence.

## Second reading by Q13

Self-check against the complete node and file, without delegating (the worker
brief forbids other agents). Checked both operations, both presentation
categories, every component, the order of j/r factors, both transformation
conjugations, and both inverse equations. The initial shift display omitted
the finite-stage inclusion shift maps; corrected it to compare the full
composites on both sides. The initial match branches referred to the unreduced
boolean operation parameter; replaced it with true/false in the respective
branches. Checked that smoothness and separated structure-map hypotheses are
explicitly included in the theorem despite being used only in its postponed
proof. No statement correction or disputed mathematical claim is needed.

## New nodes

`def-pur-smooth-operation-coefficient-models` defines the two actual finite and common
operations, the same finite PBC operation in the coefficient equivalence presentation,
the unit-induced r, and the actual strict and common-object normalization maps. Its
module is `Sheaf.Paper.SmoothOperationCoefficientModels`. It is extracted from the
owning node's Step 2 finite-presentation normalization and from the coefficient-change
transport in the latest blueprint. There are no new axioms or postponed theorems in it.
`stageEquivalence` is just the recorded rational equivalence on the named framework
stage; `conjugate` and `conjugateIso` give the displayed conjugation and its unit map.
These constructions do not choose replacement functors from a bare existence theorem.

Searches for this definition: blueprint_refs search "smooth operation" returned zero
nodes. DAG keyword search found only the later specialized theorem
`lem-pod-rational-weil-common-stage-descent`, not these definitions. Project rg for
smoothOperation / operationIdentification returned zero matches. Mathlib grep with
that pattern in CategoryTheory returned zero. LeanFinder "Data for conjugating finite
smooth pullback and exceptional inverse image operations through coefficient
presentation equivalences" returned eight unrelated manifold/smooth algebra results.
LeanSearch "A specification of common stage smooth operation comparisons through
coefficient equivalences" returned eight unrelated coefficient/smooth algebra results.
The actual tool responses are recorded in the new node's mathlib_searches.

Compile diagnosis: the coefficient wrappers and the named framework Stage are made
locally reducible for their identity adapter. The actual operations and comparison
maps are kept irreducible in later specifications, avoiding expansion of the entire
derived-category construction. A generic equivalence-conjugation definition avoids
repeated inference through those operations. The large finite-model portion is split
into its own module; the 60-second compilation limit is unchanged.

`def-pur-smooth-operation-coefficient-comparisons` isolates the actual strict scalar
comparison and common-object normalization of the preceding finite models. It reuses
the actual `sourceScalar`, `commonSourceComparison`, exceptional field comparison and
exceptional common comparison. It has the same source and search evidence as the
finite models; the split keeps each delivered module below the fixed compile limit.
Its module is `Sheaf.Paper.SmoothOperationCoefficientComparisons`. The helper formulas
include arbitrary field inclusions and repeated fields, so the split drops no case.
The second reading includes all four definition modules and their node records.

The temporary imported proof-call adapter was removed after a module-mode probe
confirmed the mandatory dependency is usable from its published build. The missing
source/object was only reached when recompiling that unrelated consumer override.
No consumer module is delivered.

The finite comparison has an objectwise accessor `finiteComparisonAt`, evaluating the
same isomorphism. The final mixed-square specification uses typed j components with
HEq to the recorded inverse beta components; the component equality pins these maps
uniquely and avoids an unnecessary category-instance conversion. `FrameworkRepresentativeSpec`
is `RepresentativeSpec J.family` together with `J.equivalence.functor = J.family.functor`,
so it is exactly the earlier displayed representative formula with the pair-functor
identification. These changes preserve the source's canonical maps and all field labels.

Verification: all five final modules compile cleanly through scompile.py, in both
sandbox and library mode. The library runs took 51.9, 25.0, 35.0, 46.3 and 10.1 seconds,
respectively; no warning remained. The first complete monolithic file elaborated but
exceeded the fixed 60-second limit, so its definitions were split with their own node
records. The final dry run returned OK: preflight and per-file compilation passed.

`def-pur-smooth-operation-descent-specification` names the representative,
transformation, framework-equivalence and mixed-square specifications, using the
existing StageSystem definitions. `def-pur-smooth-operation-identification-specification`
names the finite/common transformation transport and complete result predicate.
Their source and searches are the same common-stage interface described above;
these are the explicit clauses of this item, split into modules because the complete
file elaborated successfully but took 83 seconds in the dry run. No conclusion or
hypothesis is removed by this split. Each definition has its full Prop data.
The theorem module imports the complete predicate and contains only the source proof
plan and the one postponed theorem. The four implicit shift-instance names were
prefixed with underscores to resolve the dry-run warnings.

Final second-reading check: reread the theorem, the four definition modules and all
five node records together. The specifications retain the two actual operations,
canonical r/j comparisons, both endpoint fields, arbitrary enlargement, both inverse
identities and normalized shift composites. `OperationSpec` takes the underlying
Morphism; the final Result quantifies over CoherentExactMorphism and supplies its base,
so exactness and scalar-shift coherence remain in the statement. The split adds no
new mathematical assumption. All definitions have real bodies; the sole sorry is the
named theorem and has the source proof plan. No statement dispute or correction.
