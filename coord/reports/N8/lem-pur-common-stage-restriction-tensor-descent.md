## Worker report

The delivery states `WeilConjectures.CommonStageRestrictionTensor.descent` in
`Sheaf.Paper.CommonStageRestrictionTensorDescent`. Its proof is `sorry`, with the
complete eight-step DAG argument in the declaration docstring. All other declarations
are real expressions naming the published operations or their endpoint transports.
No new coefficient category, tensor, pullback, scalar comparison, or completion is
introduced. No statement correction, new DAG node, or dependency repair is needed.

I read the item statement and all eight proof steps; every statement dependency's
statement and Lean record; the signatures/docstrings of the operations used in
DerivedPullbackTensorHom, GeneralAlgebraicallyClosedCoefficients,
SfRationalizationKaroubi, IntegralOperationsScalarComparisons,
SfScalarExtensionComposition, IntegralDerivedOperationsOnSlices,
ConstantCoefficientScalarNormalization, PurityFiniteSetting and FiniteCoefficientFields;
and Mathlib's finite-type and small pro-etale definitions. I also read the current
blueprint `main-20261015/blueprint/sec-six-functors-basics/sk-def-purity-conv/def-pur-section-invariant.md`.
That definition states the section invariant's invertibility, not this auxiliary lemma;
the detailed argument is correctly marked agent-written in the item's proof_origin.
The withdrawn CompactObject example contains no declarations, so the live modules'
module/public-import/expose conventions are followed instead.

Hypotheses, clause by clause:

* The fixed algebraic closure of a finite field is `D : FiniteFieldDatum.{u}`;
  `l : ℕ`, `[Fact l.Prime]`, and `hl : l ≠ D.p` render the coefficient convention.
  `Ω : Type v`, `[Field Ω]`, `[Algebra (Padic l) Ω]` and
  `[IsAlgClosure (Padic l) Ω]` allow the closure universe to be independent of the
  scheme universe. No finite coefficient field is selected or excluded.
* `X Y : Scheme.{u}`, their `Over (Spec (.of D.k))` instances, and
  `LocallyOfFiniteType` plus `QuasiCompact` on both structure maps give the two
  finite-type k-schemes. `f : Y ⟶ X` and its `IsOver` instance give the k-morphism,
  with the direction in the item. No separation, smoothness, nonemptiness, or
  full-faithfulness hypothesis is added.
* `Index l Ω` is the recorded finite-intermediate-field indexing type.
  `Stage l Ω W E` and `Pair l Ω W` are the recorded raw rational and common-stage
  categories, using small pro-etale sites. Their imports retain object universe u+1
  and morphism universe u for the sites. No Karoubi envelope is used.
* `r`, `t`, `rOmega`, `tOmega` are aliases for the recorded rational/common-stage
  pullback and tensor functors. Their only local instances are the residue-field
  inverses obtained by mapping the existing `finiteFieldDatumPrimeUnit` along the
  structure morphism. Thus the source-implied invertibility is constructed rather
  than requested as an extra assumption.
* `b` is precisely `rationalPullbackScalarComparison`; `theta` is precisely
  `rationalTensorScalarComparison`; `transition` is the existing completed scalar
  extension. These are the rationalizations of the normalized integral maps.
  Their identity/tower laws use IntegralOperationsScalarComparisons and
  SfScalarExtensionComposition; they are not arbitrary supplied comparisons.
* `mu` is a family of natural isomorphisms between the two product-category
  functors `t_E ⋙ r_E` and `(r_E.prod r_E) ⋙ t_E`. Thus naturality includes
  arbitrary morphisms in both entries, not only isomorphisms.
* `unit` is `constantWeilRationalObject`, the localization of the completed
  regular coefficient object. `epsilon` is the displayed family of unit
  isomorphisms. `upsilon` is exactly `constantCoefficientRationalScalarIso` with
  the actual coefficient-inclusion algebra homomorphism.
* `mixedTensor` is the first displayed equation, with Lean composition written
  left to right: `S(mu) ≫ theta_Y ≫ t_Y.map(b_M,b_N)` equals
  `b_(M tensor N) ≫ r_L.map(theta_X) ≫ mu_L`. It quantifies over every inclusion,
  including identity inclusions, and every M,N. `mixedUnit` is the second
  displayed equation, using the normalized upsilon on both sides.

Conclusions, clause by clause:

* `muOmega` is a natural isomorphism of the actual common-stage product-category
  functors. It therefore includes invertibility and naturality for all raw
  quotient arrows, including their prescribed tensor conjugations.
* `source` is the literal pair `r_H(M_H tensor N_H)` at the compositum H=EF;
  `target` is the tensor of the two literal common-stage pullback pairs at H.
  The first conjunct gives the component as `ofHom` at **every** L above H,
  using `sourceComparison.hom ≫ mu_L ≫ targetComparison.inv`.
  `sourceComparison` is the scalar/pullback comparison followed by pullback of
  the tensor comparison. `targetComparison` is the tensor comparison followed
  by tensor of the two scalar/pullback comparisons. All their scalar tower
  identifications are those of `commonStageTensorComparison` and
  `commonStagePullbackComparison`; no objects at different stages are equated.
  At H the canonical identity-extension normalizations give the stated
  `(b_(H/E,M)^(-1) tensor b_(H/F,N)^(-1)) mu_H` representative. The use of the
  normalized `ofHom` constructor includes its identity-transition unit maps.
  Quantification over every L gives equality of the enlarged representatives'
  classes; two unrelated common fields are compared through their compositum.
  `HEq` accommodates the existing functors' propositional object formulas
  without imposing new object equalities as hypotheses.
* `unitPair` is the coefficient unit over the least field Q_l, `unitSource`
  is its literal pullback pair, and `epsilonOmega` is an isomorphism from the
  **actual** `rOmega.obj unitPair` to the target `unitPair`. Its class at every E
  is `ofHom` of `unitSourceComparison.hom ≫ epsilon_E ≫
  unitTargetComparison.inv`. These endpoint comparisons use the specified b
  and canonical upsilon. This expresses independence of the unit stage and
  compatibility with its scalar identifications, without choosing an arbitrary
  unit or an arbitrary scalar identification.
* The final conjunct quantifies over finite paths of arbitrary stage arrows,
  and says that equal composites have equal composites after common-stage
  inclusion. This is the general finite structural-equation clause: the path
  edges may be the prescribed mu/epsilon/structural-map representatives, and
  the preceding two conjuncts identify their classes with the comparisons just
  constructed. Empty paths give identities and concatenation gives composition;
  intermediate endpoint comparisons cancel. The quantification does not assume
  a particular monoidal coherence equation that the node did not assume.

Dependencies used (module: declarations):

* `Sheaf.Paper.PurityFiniteSetting`: the published convention's FiniteFieldDatum,
  supplied through its public import of FiniteFieldFiber; no positive torsion
  level is added to this rational-only statement.
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: LocallyOfFiniteType;
  its imported QuasiCompact class gives the other finite-type condition.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: Scheme.ProEt, ProEt.topology,
  used by all recorded derived coefficient categories.
* `Sheaf.Paper.SfRationalizationKaroubi`: sfRationalConstructibleCategory,
  sfRationalScalarExtension and sfRationalConstructibleLocalization, through the
  recorded Stage, transition, and constant coefficient object.
* `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: Stage, Pair, transition,
  stageSystem, ofHom, inclusion, and the published representative calculus.
* `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`: Padic.FiniteCoefficientFields,
  finiteCoefficientCompositum, finiteCoefficientBase and finiteCoefficientFields_properties.
* `Sheaf.Paper.IntegralOperationsScalarComparisons`: the normalized integral maps
  rationalized by the recorded b/theta; scalarOperationsOrdinary_tower and
  scalarOperationsOrdinary_unit give the proof's specified tower/identity laws.
* `Sheaf.Paper.SfScalarExtensionComposition`: sfRationalScalarComp,
  sfRationalScalarUnit, sfRationalScalar_coherence; these fix the associators
  already built into the recorded common-stage comparison formulas.
* `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: the completed integral
  operations convention, retaining its global construction by public import;
  the unit used here is the global completed regular coefficient module.
* `Sheaf.Paper.ConstantCoefficientScalarNormalization`:
  constantCoefficientRationalScalarIso and its normalization theorem;
  constantWeilRationalObject through ConstantWeilStructure.
* `Sheaf.Paper.DerivedPullbackTensorHom`: rationalDerivedPullback,
  rationalDerivedTensor, rationalPullbackScalarComparison,
  rationalTensorScalarComparison, commonStageDerivedPullback,
  commonStageDerivedTensor, commonStagePullbackObject, commonStageTensorObject,
  commonStagePullbackComparison, commonStageTensorComparison,
  operationStageTransitionIso and their published object/representative specifications.
* `Sheaf.Paper.DirectImagesConstructible`: existing finiteFieldDatumPrimeUnit,
  used only to supply the source-implied residue-field inverse.
* `Mathlib.CategoryTheory.PathCategory.Basic`: finite Quiver.Path, composePath,
  and prefunctor mapPath for the structural-equation conclusion.

Edge cases checked before finalizing: X or Y empty; zero objects or zero arrows;
E=F; E=L; L=H; the least coefficient field; incomparable E,F and incomparable
larger common fields; identity arrows; empty paths; arbitrary sums of rational
arrows rather than just pure tensors; unrelated closure/scheme universes. The
all-L representative statement uses canonical comparisons even for identity
extensions, so it does not silently assume a chosen scalar extension is literally
the identity. No full-faithfulness is assumed for any stage inclusion.

Searches actually run: msearch.py leanfinder with “Natural tensor and unit
isomorphisms descend to raw common stage coefficient pair categories with prescribed
scalar extension comparisons” found ordinary ModuleCat scalar associators and
polynomial-law base change, not this statement. The shorter common-stage query
found free monoidal normalization and graded tensor comparisons, not this descent.
Loogle `CategoryTheory.NatTrans.IsMonoidal` returned the monoidal natural-transformation
predicate and its identity/composition instances; those neither construct the raw
pair-category comparison nor prescribe its common-stage representatives. The first
Loogle query containing `CategoryTheory.NatIso` was a query error, not a negative
search. msearch.py grep `IsMonoidal|FilteredColimit.*NatTrans` in CategoryTheory
returned monoidal-localization and monoidal natural transformation files, no exact
match. The sandbox searches.jsonl retains the actual tool outputs. Earlier searches
in that log include LeanSearch for compatible natural isomorphisms on filtered
colimits of categories, which returned ordinary colimit isomorphisms, not this item.
Local rg searches in lean/WeilConjectures and lean/Sheaf for the item id and
commonStage/tensor/descent found no exact theorem. The existing canonical
DerivedPullbackTensorIso is only the prescribed canonical comparison, not descent
of arbitrary mu and epsilon with the two mixed squares. No duplicate declaration
was found in dag/lean_names_upstream.json or the two source roots.

Compilation: every compile used the prescribed scompile.py wrapper. An initial
elaboration timeout was diagnosed to unfolding the actual rational functors while
checking the mixed square. Explicit helper return types and local irreducibility
of those published functors fixed it without mathematical or universe changes.
The server then compiled the sandbox and final library module without warnings.
Synchronous elaboration (`Elab.async false`) keeps the per-file work within the
fixed 60-second limit without profiler diagnostics. The required dry run printed
`OK (dry run): commit a3c87d010d3 passes the preflight and compiles; nothing pushed`.
The final delivery result is recorded by deliver2.py.

## Second reading by N8

A separate rereading in this sole dispatched worker checked the complete node against
the final file; no second agent was started, as the dispatcher explicitly prohibits
it. The maintainer performs the independent delivery review. This is not represented
as an independent-agent review.

The rereading checked direction f:Y→X, both finite-type structure morphisms, the
independent Ω universe, naturality of mu in the product category, each of the three
factors on each side of mixedTensor, and all three factors in mixedUnit. It checked
that b/theta/upsilon are the recorded normalized comparisons. It also checked the
all-L representatives against the eight proof steps, including the tensor-arrow
conjugations and scalar associators inside the two endpoint comparisons. One
mismatch found in the partial draft was that its unit conclusion used only the
literal `unitSource`; the final isomorphism instead has the actual
`rOmega.obj unitPair` as its source, with HEq used only for its representative.
Diagnostic #eval commands and profiler settings were removed. Local opacity fixes
only elaboration; it introduces no hypotheses or mathematical restrictions. All
definition bodies contain data, and descent is the only postponed theorem.
