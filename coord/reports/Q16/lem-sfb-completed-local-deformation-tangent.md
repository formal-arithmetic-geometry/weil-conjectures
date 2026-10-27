## Worker report

The item is stated by `Algebra.FlatDeformation.completedLocal_deformation_tangent`
in `Sheaf.RingTheory.CompletedLocalDeformationTangent`. Its conclusion gives the
fully specified `CompletedLocalComparison` record. There is one postponed theorem,
with the entire proof route in its docstring. All definitions have actual data.
No natural-language statement or proof dependency was changed.

Hypotheses and clauses, matched individually:

- The field is `{k : Type u} [Field k]`. The local k-algebra is
  `{A : Type u} [CommRing A] [Algebra k A] [IsLocalRing A]`.
- Being a localization of a finite type k-algebra at a maximal ideal is rendered
  by the theorem's `B`, `[Algebra.FiniteType k B]`, `m`, `[m.IsMaximal]`,
  `[Algebra B A]`, `[IsScalarTower k B A]`, `[IsLocalization.AtPrime A m]`.
  No Noetherianity hypothesis is imposed on A: Noetherianity is a conclusion.
- The completion is the actual `localCompletion A`, namely
  `AdicCompletion (IsLocalRing.maximalIdeal A) A`, with its canonical algebra map.
- R ranges over the existing `TestCategory k k`. Its `IsTestAlgebra` supplies
  Artinianity (the descending-chain condition), locality and the marked residue
  augmentation to k. It does not impose an additional finite-type condition on Q.
- The source groupoid is the existing `FlatDeformation.Groupoid A R`, with its
  existing `scalar`, `marking`, `hom`, and `ideal`. Its marking is a surjection
  with kernel m_R Q, equivalently the specified special-fibre isomorphism.
- `ContinuousGroupoid (localCompletion A) R` is the full subcategory on
  `IsContinuous`: local, Noetherian, and complete at its actual maximal ideal.
  A ring isomorphism between local rings maps maximal ideals and their powers
  onto each other, so every retained marked isomorphism is continuous, and these
  are precisely all continuous marked isomorphisms. No topology is lost here.
- `completion` is a functor on every fibre. `completionIso` identifies its
  actual algebra with the completion at `ideal (maximalIdeal A) Q`.
  `completion_scalar` fixes the R-algebra structure.
  `completion_marking` and `completion_arrow` use `IsCompletionMap` at EVERY
  finite quotient to fix the canonical marking and all arrow maps.
- `completion_flat` states R-flatness of that actual completion. The target
  marking, its kernel equation, and `completion_scalar` give exactly the
  canonical completed-special-fibre tensor isomorphism with the completion of A;
  this uses the same quotient-with-prescribed-kernel encoding as the source.
- `base_change_exists` supplies all Artinian base changes. `base_change`
  preserves them through a unique marked map, whose completion is characterized
  at every quotient. `IsBaseChange` includes the actual tensor isomorphism and
  its simple-tensor formula. This is naturality on the full deformation category,
  including the identity and composition cases by uniqueness, not merely an
  unrelated family of fibre functors.
- P is the existing `CotangentResolution.Naive.Presentation`; the predicate
  `IsFinitePolynomial P` means a localization of a polynomial algebra on Fin r,
  with compatibility on k. J/J^2 and the differential module are exactly the
  recorded `conormal P` and `differentials P`, with `differential P`.
- `conormalComplex P` uses the cone of the degree-zero map, hence degrees -1,0.
  It uses the already supplied conormal differential, not a private replacement.
  `completedDifferential` is `ModuleCat.extendScalars.map` of that differential;
  `completedConormalComplex` is its cone, hence the termwise tensor complex.
  The tensor factors are written in the equivalent B-tensor-A order used by
  Mathlib's existing extension-of-scalars functor.
- `continuous_presentation` supplies `ContinuousPresentationModel P`.
  Its `quotient` is the quotientwise canonical completed presentation map, with
  surjectivity. `conormalIso` and `conormal_dense` identify completed conormal
  classes with the actual kernel modulo its square. `differentialIso` and
  `differential_dense` identify the completed polynomial differential term after
  quotient. `derivation_dense` specifies the extended derivation on the original
  ring; `derivation_continuous` states ideal-power continuity. `boundary_formula`
  says the differential sends a completed relation to its continuous derivative.
  No ordinary differential module of the completed ring over k is substituted.
- `algebraicIndependence` and `completedIndependence` are derived isomorphisms
  for any two allowed presentations. `independence_normalization` fixes them
  on every compatible presentation map by its conormal-class and differential-
  tensor formulas. `independence_identity` and `independence_cocycle` give
  coherence. The two `*_presentation_compatibility` clauses make the tangent
  identifications agree under these specified comparisons.
- `dualTest k` is the existing `squareZeroTest k`, i.e. k plus k epsilon with
  epsilon squared zero. `FirstOrderClasses` and `ContinuousClasses` are quotients
  by marked isomorphism, with no selected representatives or size truncation.
- `algebraicTangent` and `continuousTangent` are k-linear equivalences from those
  actual quotients to `TangentHom P` and `CompletedTangentHom P`. These are the
  displayed ordinary derived-category Hom spaces with A and its completion
  embedded in degree zero BEFORE shift by 1.
- The vector structures are supplied simultaneously with the equivalences,
  rather than assumed as hypotheses. `algebraic_relations` and
  `continuous_relations` provide relation maps for every object.
  `*_normalization` equates the image of EVERY relation map with the existing
  positive `DerivedCategory.twoTermBoundary`. This fixes the canonical
  classifications and, together with their surjectivity, also fixes the vector
  structures. Addition and scaling agree with addition and scaling of relation
  maps, hence with the usual fibre-product/pushout operations of the source.
- `algebraic_origin` and `continuous_origin` send a split marked extension to
  zero. Such extensions are exactly the trivial dual-number deformations.
- `extended_relations` supplies tensor extensions of every relation map;
  `IsExtendedRelationMap` fixes its value on every b tensor [j].
  `scalarExtension_boundary` fixes `scalarExtension` on the actual two-term
  boundaries. These boundaries generate the entire derived Hom: the normalized
  algebraic tangent equivalence is onto and every deformation has a relation
  map. Thus this specifies exactly extension of scalars on derived Hom and
  cannot be satisfied by an arbitrary map. Flatness makes termwise tensor a
  functor on derived categories and its quotient-map/boundary formula is the
  one stated here. `completion_tangent` is the asserted commuting tangent square.
- There is no equality or separability assumption on the residue field of A/k,
  and no comparison with ordinary differentials of its completion.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`,
  `IsAdicComplete`, `AdicCompletion.of`, `evalₐ` and the algebra structure.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat` and `Module.Flat`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, its `D`, and the
  universal property `linearMapEquivDerivation`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`/`.Basic`/`.Map`: `TensorProduct`,
  its generators and universal property, and the existing scalar extension.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `Q`, and `singleFunctor`; `.Linear` supplies k-linearity.
  The two explicitly quantified localization instances choose the morphism
  universe u+1, the standard available size for ModuleCat.{u}. They are choices
  of the existing localizations, not extra mathematical restrictions.
- `Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory`: `TestCategory`,
  `ring`, `residue`, `squareZeroTest` and its real square-zero algebra.
- `Sheaf.RingTheory.MarkedFlatAlgebraDeformations`: `Groupoid`, `algebra`,
  `scalar`, `marking`, `hom`, `ideal`, `IsCompletionMap`, `IsBaseChange`.
- `Sheaf.RingTheory.NaiveCotangentComparison`: `Presentation`, `conormal`,
  `kernelClass`, `differentials`, `tensorGenerator`, `differential`,
  `PresentationMap`, owned by `def-trf-naive-cotangent-comparison-data`.
  The comparison theorem remains a proof dependency.
- `Sheaf.Algebra.Homology.TwoTermDerivedHomBoundary`: `twoTermBoundary` and
  `twoTermSquareMap`, including the positive quotient convention, now registered
  by `def-sfb-two-term-derived-hom-boundary-maps`.
- Stated proof dependencies are imported privately: the completion functor,
  polynomial-lift calculus, local completion quotient, finite module completion,
  Noetherian localization/completion, completion exactness and tensor comparison,
  flat tensor exactness, triangle Hom exactness, and projective Ext criterion.
  Mathlib matches were read as declaration records, not treated as missing Lean.

Edge cases checked: r=0 (including A a field); J=0; maximal ideal zero;
R=k; the trivial deformation; zero relation maps; level n=0 in completion
characterizations; inseparable residue extensions; different allowed presentations;
identity and successive Artinian base changes. No dimension or finiteness of the
residue extension is imposed. A common universe u can contain all rings in a
comparison; the deformation object/class quotients and derived Hom are allowed
in u+1. No independent smaller test universe makes a quantifier vacuous.

Searches: msearch LeanFinder queried completion and first-order deformation
classification (8 component hits; no comparison theorem); Loogle queried
`AdicCompletion, Algebra.Extension.Cotangent, DualNumber` and the expected
isomorphism-class/complex names (0 hits); LeanSearch queried the complete local
marked deformation/conormal package (8 component hits, no package). msearch grep
`deformation|Deformation` in Mathlib/RingTheory found only a perfectoid docstring.
Project rg searches of `lean/WeilConjectures` and `lean/Sheaf` found the recorded
marked-flat and conormal components but no continuous subgroupoid or completed
classification. Searching the exact item id found no existing statement.
`blueprint_refs.py search 'completed local deformation'` returned 0 blueprint
nodes; DAG concept searches found the item and its surrounding lemmas, not the
new definition package. Exact wrapper search results are retained in the new
node's `mathlib_searches`.

No STATEMENT-DISPUTED issue or statement correction. The historical compact-object
example is withdrawn in this checkout (its module contains no declarations);
module-mode/public-import conventions were followed from the current stage brief.

Validation: both delivered files compiled separately in dependency order through
scompile.py. Only the main theorem has a sorry. All universes and variables are
explicitly bound, `autoImplicit` is false, and each helper has its owning node's
source/blueprint docstring. The deliver2.py dry run passed preflight and compilation (12d7a58585f).
The current preflight also requires `import_flags: []` on the new definition
node; this field was added after its initial metadata-only rejection. The
prescribed push command reruns validation before delivery.

## New nodes

`def-sfb-completed-local-deformation-objects` defines the continuous full subgroupoid,
its actual first-order isomorphism-class quotients, finite localized presentations,
cone/tensor conormal models, and the dense relation-map normalization predicates.
It imports and uses the existing marked-flat and naive-conormal APIs. It supplies
only the absent continuous package and coordinating predicates, not another
construction of their component notions. Sources are Stacks 0DYV, 0GPU, 0GPW,
0AJR and 0GAE as interpreted in the parent node. Its searches are listed above and
in its own record. It contains no theorem or postponed proof. The item cites this
definition node and the boundary-map definition node described below.


`def-sfb-two-term-derived-hom-boundary-maps` records `existing: true` on
`Sheaf.Algebra.Homology.TwoTermDerivedHomBoundary`, with the three declarations
`DerivedCategory.twoTermQuotient`, `DerivedCategory.twoTermSquareMap`, and
`DerivedCategory.twoTermBoundary`. The abelian category and chosen localization
are exactly the existing `Abelian` and `HasDerivedCategory` interfaces. The cone
of `d[0]` supplies degrees -1,0; negating its triangle's third arrow and applying
the localization/shift comparison gives the positive quotient. The boundary is
its composition with the shifted degree-zero embedding of every morphism to G.
For a commuting square, the cone map has precisely the components a,b. This node
asserts only these constructions, not their exactness or naturality. Stacks
014E and the zero-homotopy case of its functorial-cone construction specify the
maps; 0149 explains the boundary composition. Zero differential and zero objects
are allowed, with no projectivity hypothesis. Object, category-morphism and
localization-morphism universes remain independent, as in the existing source.
No new Lean module or declaration is introduced.

The new map searches were run through msearch: LeanSearch's query
`two term complex cone quotient shifted source additive derived Hom boundary map`
returned eight component hits (including the cone triangle), Loogle's query
`DerivedCategory.twoTermBoundary, DerivedCategory.twoTermQuotient, CochainComplex.mappingCone.map`
returned zero hits with the explicit unknown-project-identifier note, and grep
`twoTermBoundary|twoTermQuotient|twoTermSquareMap` in Mathlib/Algebra/Homology
returned zero hits. Exact results are in the node record. Project and DAG rg
found the existing module and only its theorem node; the blueprint search
`two-term` returned five unrelated nodes. Hence this is a registration of existing
maps with a definition owner, not a duplicate construction.

## Repairs

The immutable-head review of `742f9728cf32` returned H12/H2 solely for definition
ownership in the DAG. The repair addresses each requested change:

- `def-sfb-completed-local-deformation-objects` now cites the already accepted
  `def-trf-naive-cotangent-comparison-data` for its plain Naive definitions,
  replacing the existence-theorem node in both its text and `stmt_deps`.
- The new `existing: true` definition node
  `def-sfb-two-term-derived-hom-boundary-maps` registers exactly the three
  explicit boundary/cone maps. Both the completed-objects node and the item
  cite it in `stmt_deps`, including the item's direct boundary-map usage.
- `lem-trf-lci-naive-cotangent-model` and
  `lem-sfb-two-term-derived-hom-boundary` remain in the item's `proof_deps`.
  No theorem is used through `.choose` to define any of these objects.

The retained Lean sources are unchanged from the returned delivery. Comparing
the item with the current read-only main record shows changes only in `lean`
and the added definition `stmt_deps`; all mathematical text and proof fields
are preserved. The accepted naive definition record was read on current main,
and its existing module is reused without a dependency-record repair.

## Second reading by Q16

I reread the node and both modules clause by clause in this single-worker session;
this is a self-check, with the maintainer's independent review still to follow.
The read found that mere existential equivalences would not specify the tangent
map or presentation independence. The delivered record therefore normalizes the
equivalences by every relation map, fixes scalar extension on tensor generators
through the boundary, and fixes comparison maps on every presentation lift.
It also retains actual Artinian base-change tensor maps and complete local target
objects. Type checking exposed bundled-algebra and derived-localization instance
visibility issues, repaired with explicit canonical instances/category arguments;
no mathematical hypotheses were added. The match of every hypothesis and clause
is recorded above. No consumer-side correction or dependency-record repair is needed.

Repair self-check: I read the three map definitions, their source docstrings,
the existing naive definition node and the Stacks cone convention. Both new
nodes now cite definition owners only. The map node's boundary is the exact
existing additive composition, and its square-map clause has the required
commuting-square hypothesis. The theorem nodes remain proof inputs, so none of
the independently accepted tangent mathematics changed in this repair.

Repair validation: scompile.py compiled both delivered modules on the live server
cleanly (objects: 3.0 s; tangent: 20.8 s). No Lean source changed during repair.
