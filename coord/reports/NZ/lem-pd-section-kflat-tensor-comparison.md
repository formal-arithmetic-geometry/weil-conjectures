## Worker report

This is the dispatched stage-2 statement, not a reopening of Q11's accepted
stage-1 split. The maintenance stage-handoff paragraph in brief-stage2 §0
explicitly resolves the inherited stage-1 refusal. The live item has no Lean record. This packet repairs returned immutable
head `7b60a441a311` and retains its checked theorem statement.

The module is `Sheaf.Paper.SectionKFlatTensorComparison`; its namespace is
`AlgebraicGeometry.ProEtale.ModuleRingedComparison.KFlatSectionComparison`.
The only postponed theorem is `section_kflat_tensor_comparison`. Its docstring
carries all seven proof steps, their dependencies and the source tags. Helper
abbreviations and predicates have actual data and introduce no new choice.

Hypothesis and clause correspondence:

* The arbitrary commutative condensed ring is the existing abelian-sheaf object
  `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}`, with `MonObj Λ` and
  `IsCommMonObj Λ`. It need not come from a topological ring. `T : Scheme.{u}`
  is unrestricted.
* `internalModules Λ T`, `ring Λ T`, `modules Λ T`, and `equivalence Λ T`
  are the exact SectionModuleOperationsData aliases: the internal coefficient is
  `condensedRingObj Λ T = p_T^* Λ`, and the section ring is reconstructed from it.
  The site is `Scheme.ProEt.topology T`, whose object universe is `u+1` and
  morphism universe `u`; the two are not identified. Module sections are `u+1`.
* The existing chosen-universe derived categories are retained by
  `[∀ X : Scheme.{u}, HasDerivedCategory.{u+1} (modules Λ X)]`, exactly the
  convention of the fixed derived-tensor-data and derived-realization interfaces.
  This chooses localization sizes, not extra mathematical hypotheses on schemes.
  `derivedEquivalence` and `sectionLocalizationComparison` are D(E) and kappa.
* `complexes` is termwise E. The first conjunct is preservation and reflection
  of every quasi-isomorphism, with all cochain maps quantified.
* `internalResolving` spells out the internal acyclic-total-tensor test and
  exactness of tensorRight on each term. Symmetry makes the latter the flatness
  test in the node. `sectionResolving` aliases the existing cochain representative
  property: `IsKFlatIndependentCoefficients` and `IsFlatOnSite` in every degree.
  The second conjunct identifies these full subcategories under termwise E.
  Essential surjectivity of the original termwise equivalence then gives the
  asserted equivalence of representative categories, not just preservation.
* The third conjunct supplies the internal homotopy representative property P
  with its exact membership characterization. It supplies an equivalence from
  its quasi-isomorphism localization to the internal derived category, including
  the factor isomorphism to the restricted Qh. Its final clause is bijectivity on
  natural transformations after restriction on both resolving arguments, for
  arbitrary `A : Type e` and `Category.{z} A`. Neither target universe is fixed.
* All cochain tensors use `CochainComplex.mapBifunctor` or the existing
  `totalTensor`, the signed direct-sum cochain totals. There is no boundedness
  predicate or choice of a different totalization.
* `TensorRepresentativeCondition Λ T (qTensor Λ T)` retains the fixed section
  localization map, its specified ordinary-total normalization, invertibility
  on K-flat inputs, and regular-unit identification.
* `nativeTensor` aliases `siteDerivedTensorIndependentCoefficients` at the actual
  pro-etale site and reconstructed ring. The existential native q is a natural
  map on all complex pairs. `NativeLocalizationCondition` requires it to be the
  inverse of the published `tensorDescentPair` comparison on every flat-term
  K-flat pair. Thus it is pinned to the independent descent model.
  The natural isomorphism `v : tensor Λ T ≅ nativeTensor Λ T` satisfies
  `whiskerLeft (Q.prod Q) v.hom ≫ q = qTensor Λ T`, identifying localization
  maps on all complexes as well as identifying the bifunctors.
* `RepresentativeCondition` is the displayed theta equation with inverse
  representative maps: E(mu_internal) followed by localizedTotalComparison
  equals theta, tensor(kappa,kappa), then qTensor. On resolving pairs mu and
  qTensor are invertible, so multiplication by their inverses gives exactly
  `(kappa tensor kappa) theta D(E)(r_i) = r_s q(t) kappa_total`.
  `∃! θ, RepresentativeCondition ... θ` gives normalized uniqueness. The next
  conjunct asserts this for the fixed `tensorComparison`; hence the unique theta
  is that comparison. Composing with v reads this same comparison in the native
  model; it is not an independently chosen derived isomorphism.
* The regular internal module in degree zero is explicitly required to satisfy
  `internalResolving`. The final existential e is pinned by equality to kappa,
  the canonical termwise/single-complex comparison, and localization of
  `ordinaryUnitComparison`. Its target is the section regular module in degree zero.
* `ConstraintCondition` uses Mathlib's existing `Functor.OplaxMonoidal` structure
  for the fixed derived equivalence and `Monoidal.transport` of its internal
  structure. Its η is required to be the identity into `tensorUnit`; its δ is
  required to be the fixed `tensorComparison` on every derived pair. The fields
  `oplax_associativity`, `oplax_left_unitality`, and `oplax_right_unitality`
  are exactly the requested associator and both unitor equations. Naturality
  adds no condition: theta is already a natural isomorphism. The explicitly
  localized e identifies this transported unit with the section regular module
  in degree zero. Transporting the unitors along e gives the diagrams with e
  itself as unit comparison. This reuses Mathlib's notion of coherence instead
  of defining a second version of the same three constraint equations.

Dependency declarations used, read from the recorded modules:

* Sheaf.Topology.ProfiniteCondensedRing: `Profinite.CondensedRing` (its unbundled
  MonObj/IsCommMonObj input form is the fixed tensor framework's input).
* Mathlib.AlgebraicGeometry.Sites.Proetale: `AlgebraicGeometry.Scheme.ProEt` and
  `Scheme.ProEt.topology`.
* WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic: `coefficientRing`,
  `condensedRingObj`, and preservation of commutativity under inverse image.
* Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence:
  `InternalAbelianSheafModule.sectionModuleEquivalence` and `sectionRingSheaf`.
* Sheaf.Paper.SectionModuleOperationsData: `internalModules`, `ring`, `modules`,
  `equivalence`, `ordinaryUnitComparison` (the last is reexported from the
  ordinary comparison module).
* Mathlib.Algebra.Homology.DerivedCategory.Basic: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.Qh`.
* Sheaf.Algebra.Homology.KFlatIndependentCoefficients:
  `CochainComplex.IsKFlatIndependentCoefficients`.
* Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite: `SheafOfModules.IsFlatOnSite`.
* Mathlib.Algebra.Homology.BifunctorShift: `CochainComplex.mapBifunctor`.
* WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom and Derived.Tensor:
  the existing internal derived monoidal structure and `CondensedRing.derivedTensor`.
* Sheaf.Paper.SectionDerivedTensorData: `derivedEquivalence`, `tensor`,
  `tensorUnit`, `tensorComparison`, `totalTensor`, `sectionLocalizationComparison`,
  `localizedTotalComparison`.
* Sheaf.Paper.SectionDerivedRealization: `TensorRepresentativeCondition`, `qTensor`.
* Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients:
  `siteDerivedTensorIndependentCoefficients` and its defining descent witness.
* Sheaf.CategoryTheory.InternalSectionTensorComparison:
  `internal_section_tensor_comparison` and the fixed ordinary total comparison.
* Sheaf.Paper.SiteDerivedTensorRestriction: `CategoryTheory.TensorFlatRepresentative`
  and `CategoryTheory.tensorDescentPair`, owned by the already-landed definition
  node `def-weil-pbc-tensor-descent-representative-comparison`. The former is the
  conjunction of the recorded K-flat and flat-term predicates. The latter is the
  specified four-arrow comparison from localized total tensor to native tensor.
  No conclusion of either the tensor-rigidity or scalar-restriction theorem is used.

The modules of all stated proof dependencies are imported. The localization
universal-property node is a Mathlib leaf; its `mathlib_match` records
`Localization.lift`, `fac`, `liftNatTrans`, `liftNatIso`, `natTrans_ext`, and
`fullyFaithfulWhiskeringLeft` in Mathlib.CategoryTheory.Localization.Predicate.

Edge cases checked against the definitions before writing: the zero ring and
zero module category are allowed; no nonzero or nonempty assumption occurs.
The empty scheme is allowed. Every complex is integer-indexed and unbounded.
Zero complexes and degree-zero regular modules have the stated flat/K-flat
interpretations. The actual small-site universes u+1/u are retained, while the
transformation target uses arbitrary independent e/z. No bounded-above,
finite-dimensional or termwise-flat hypothesis is imposed on derived objects.
The resolving conditions apply only where representative computations need them.

Searches made: msearch leanfinder query “The fixed internal to section equivalence
uniquely compares K-flat derived tensors and their unit and associativity
constraints” returned eight ordinary Module.Flat results, none this comparison.
The preserved msearch loogle query `CategoryTheory.Functor.mapDerivedCategory`
returned twelve generic derived-functor declarations, not this assertion.
msearch grep `siteDerivedTensor|KFlatTotalTensorModel|tensorComparison` in
Mathlib CategoryTheory returned no match. Direct rg of both project source roots
for the item id returned no declaration. Concept searches found the fixed
SectionDerivedTensorData and SectionDerivedRealization interfaces, the downstream
SectionDerivedTensorNormalization theorem, and CochainTensorModelRigidity. The
first two are used directly; the downstream theorem has additional pullback
clauses and is a consumer, so it cannot be used to assert this prerequisite.
The cochain representative comparison is reused from its existing definition node.

The source read is the local Stacks sites-cohomology.tex definition-derived-tor
and lemma-symmetric-monoidal-derived, together with Q11's complete accepted
seven-step extracted comparison proof. No statement correction or disputed statement is required. The dependency-ownership
repair is recorded below; no new node or dependency module is necessary because
the exact definition owner already landed.

Validation before this ownership repair: the retained complete module passed `scompile.py` in module mode:
16.8 seconds for the sandbox compilation and 16.1 seconds for the library-path
compilation, with no errors or warnings. The retained initial delivery log records
a timeout from an earlier module revision; the current helper-predicate factoring
and product-valued representative binder avoid the repeated large elaborations.
All helper predicates, including `ResolvingLocalizationCondition`,
`NativeComparisonCondition` and `UnitCondition`, are listed in `lean.declarations`.
The node signature is copied verbatim from the current theorem declaration.

Fresh search verification on this continuation: msearch leanfinder query
“An exact internal to section module equivalence identifies the fixed K-flat
derived tensor comparison and its localization maps and monoidal constraints”
returned eight ordinary module-flatness lemmas, with no exact comparison theorem.
msearch loogle `CategoryTheory.Localization.lift₂NatIso` returned the generic
localization-lift isomorphism and its hom/inv lemmas; these do not assert the
specified sheaf comparison. msearch grep
`section_kflat_tensor_comparison|KFlatSectionComparison` returned zero Mathlib hits.
Direct `rg` with those names and section/K-flat concept patterns on both project
source roots found other scalar-change and ordinary comparison interfaces, but
no theorem stating this conjunction; grep of the item id in WeilConjectures also
returned no declaration. These searches confirm the retained earlier search
conclusion without treating its logs as a new execution.

## Returned delivery repair

The return of immutable head `7b60a441a311` identifies one required correction:
the additional stmt_dep `lem-sf-cochain-tensor-model-rigidity` is a theorem,
while the item used only its helper definitions. The saved packet first passed
`deliver2.py --no-push` at `ee530832bd4`; this mechanical pass did not discharge
the independent review finding.

Before creating a node I searched the DAG and found the already-landed
`def-weil-pbc-tensor-descent-representative-comparison`. Its statement and all
seven recorded helper declarations were read in
`Sheaf.Paper.SiteDerivedTensorRestriction`. It already owns precisely the same
flat-term K-flat predicate and representative comparison construction. As the
brief requires reuse of existing notions, this repair cites that definition node
instead of creating a duplicate definition node. The live base still has the
original fourteen dependencies, and no Lean record; the repaired packet adds
only this landed definition node. No existing node other than the item's `lean`
and `stmt_deps` is edited.

The Lean changes are the public import, the body of `sectionResolving` (now the
existing `CategoryTheory.TensorFlatRepresentative`), and the arrow in
`NativeLocalizationCondition` (now the `.hom` of
`CategoryTheory.tensorDescentPair`). The latter takes the two membership proofs
from the full-subcategory objects. It has the same direction and four factors:
Q to Qh of the homotopy quotient, inverse complex/homotopy tensor comparison,
the given homotopy/derived comparison, and native tensor applied to the two
Qh-to-Q factors. The choices come from the same published descent datum.
`tensorDescentComplexIso` and `tensorDescentDerivedIso` use the named existence
wrappers of that datum, whose bodies return its original nested witnesses.
The rigidity conclusion and scalar-restriction conclusion are unused.

Fresh searches on 2026-10-23 (raw tool records are retained in `searches.jsonl`):
* msearch leansearch: “The cochain flat term K-flat representatives and their
  canonical arrow from localized total tensor to the site derived tensor” —
  eight generic K-projective, flat-module or derived-localization hits; none
  defines this comparison.
* msearch loogle: `SheafOfModules.cochainTensorRepresentativeArrow` — zero
  Mathlib hits (identifier unknown there).
* msearch grep: `cochainTensorFlatRepresentatives|cochainTensorRepresentativeArrow`
  — zero Mathlib hits.
* Direct rg of these names in `dag/nodes`, `lean/Sheaf` and `lean/WeilConjectures`
  found the rigidity helper module and, in a repaired Roos-descent consumer's
  record, the existing definition owner above. I opened its complete statement,
  Lean record, predicate and comparison body. `tools/blueprint_refs.py search
  cochain` was also run; the ancestor command reports null for this extracted
  item's blueprint origin. No new definition is needed.

## Second reading by NZ

Self-check against the return and the revised file: Λ, its commutative ring-object
instances, unrestricted T and the fixed derived-universe convention are unchanged.
The first clause still quantifies all cochain maps and reflects/preserves
quasi-isomorphisms. The second clause still identifies precisely the internal
acyclic-total/exact-term test with K-flatness and flat terms on the section side.
The resolving localization clause retains arbitrary independent target universes
e/z and bijectivity on transformations. The existing qTensor condition, native
tensor and all-complex localization-map equation remain. The native map is now
pinned to the existing definition-owned four-arrow comparison, with its exact
original source and target. The normalized unique theta equation, its assertion
for the fixed theta, regular degree-zero representative, localized unit comparison
and transported associator/both-unitor condition are unchanged. No boundedness,
nonzero assumption or site-universe identification is introduced. The zero ring,
empty scheme and zero complexes remain allowed. The theorem signature is verbatim
the node's `lean.statement`; there is one `sorry`, on the same named theorem.
The original source places 06YU and 0FPT were reopened. The report's earlier
clause-by-clause correspondence remains valid with the replacement definition
owner specified above.

Repair validation (2026-10-23): `scompile.py NZ
lem-pd-section-kflat-tensor-comparison
lean/Sheaf/Paper/SectionKFlatTensorComparison.lean` passed both compilations
(14.7 seconds sandbox, 7.5 seconds library path), with no errors or warnings.
The first compile exposed a missing `ObjectProperty` result annotation on the
replacement predicate alias; the annotation was supplied, retaining exactly the
same predicate. A mechanical self-check confirmed the unchanged theorem signature,
100-character source line limit, only `lean`/`stmt_deps` changes from current live,
addition of only the existing definition node, and one named postponed theorem.
