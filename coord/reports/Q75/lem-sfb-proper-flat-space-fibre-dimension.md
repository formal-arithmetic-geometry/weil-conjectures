## Worker report

The module `Sheaf.AlgebraicGeometry.ProperFlatSpaceFibreDimension` states
`AlgebraicGeometry.AlgebraicSpace.proper_flat_fp_fibreDimension_isLocallyConstant_and_baseChange`.
Its sole theorem has proof `sorry`. Its helper `fibreDimension` has real data: an indexed
supremum of topological Krull dimensions. It introduces no axioms or arbitrary choices.

The source read was `literature/stacks-project/spaces-more-morphisms.tex`, lines 7122–7262:
lemma-dimension-fibre, Tag 0D4N (lemma-base-change-dimension-fibres), Tags 0D4P/0D4Q,
and Tag 0D4R (lemma-dimension-fibres-proper-flat). Tags were checked in tags/tags.
The node's four proof steps are reproduced in the theorem docstring.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A scheme T and an algebraic space with a map to T are `T : Over S`,
  `X : AlgebraicSpace S`, `f : X ⟶ schemeSpace T`. This ambient-base formulation
  imposes no extra geometric restriction: take S=T and the identity T/T for any family;
  every scheme map T'→T then defines an object T'/S. All are in the existing size
  convention, with universe u explicitly declared and autoImplicit false.
- Flatness is `hflat : MapIsFlat f`, whose definition is `MapIsLocally (@Flat) f`:
  every compatible pair of representable étale scheme charts has a flat scheme map.
- Properness is `hproper : MapIsProper f`: `MapIsSeparated f ∧ MapIsFiniteType f ∧
  MapIsUniversallyClosed f`. The first tests the relative diagonal by closed immersions;
  the second is quasi-compactness and chartwise locally finite type; the third tests
  closedness on the existing atlas-topologized point spaces after every space base change.
- Finite presentation is `hfp`: chartwise `MapIsLocallyOfFinitePresentation f`,
  `MapIsQuasiCompact f.hom.hom`, and quasi-compactness of
  `Limits.pullback.diagonal f.hom.hom`. No properness/flatness component is substituted
  for these hypotheses.
- The helper forms the actual presheaf fibre product of `f.hom.hom` and the Yoneda map
  of `T.left.fromSpecResidueField t`, with its precise Over S structure map. This is
  X ×_T Spec κ(t), not a chosen chart, arbitrary space, or set-theoretic fibre.
- The helper takes `⨆ (U : Over S) (_ : IsAffine U.left) (a : yoneda.obj U ⟶ ...)
  (_ : IsEtale a), topologicalKrullDim U.left`: exactly the specified supremum over
  every affine representable étale chart. `IsEtale` includes representability. For a
  scheme this is its topological Krull dimension: affine opens are such charts, and
  étale charts preserve local dimension. No replacement by the generally different
  topology on arbitrary non-decent space points is made.
- `WithBot ℕ∞` carries bottom = −∞ and possible top = +∞. The first theorem conjunct
  says each value is bottom or a natural number, excluding +∞ under precisely the
  family hypotheses, hence rendering the stated codomain {−∞,0,1,...} exactly.
- `IsLocallyConstant (fibreDimension f)` renders local constancy, including the bottom stratum.
- `∀ d : ℕ, IsClopen {t | fibreDimension f t = (d : WithBot ℕ∞)}` renders the
  open-and-closed loci for all integers d≥0, equivalently natural numbers.
- For every scheme morphism `h : T' ⟶ T`, the fourth conjunct uses
  `enlargedFibreProductFst (ObjectProperty.homMk ⟨yoneda.map h⟩) f`, the canonical
  projection T' ×_T X→T', and equates its fibre-dimension function with
  `fibreDimension f ∘ h.left`. The order of fibre-product factors is harmless and
  retains the actual projection to T'.
- The fifth conjunct equates each new dimension-d locus to the inverse image by
  `h.left` of the original locus. The equality concerns the actual subsets and hence
  their induced open subspaces; no unrelated isomorphism or component choice appears.
- Arbitrary residue-field extensions are included by T'=Spec K→T, with its composite
  to S. No nonempty, pure-dimensional, connected, Noetherian or characteristic hypothesis
  appears anywhere.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`,
  `IsRepresentableWith`, with their complete scheme-test definitions.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.fromSpecResidueField`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, `etale_fibreProduct_isScheme`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `.FinitePresentation`, `.FiniteType`,
  `.Proper`: `Flat`, `LocallyOfFinitePresentation`, `LocallyOfFiniteType`, `QuasiCompact`,
  `IsProper`, `IsSeparated`, `UniversallyClosed`, through the existing general space predicates.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`,
  used by existing quasi-compactness/universal-closedness predicates.
- Newly cited landed `def-sfb-space-morphism-properties`, module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsFlat`,
  `MapIsLocallyOfFinitePresentation`, `MapIsProper` and its constituents.
- Newly cited landed `def-trf-scheme-algebraic-space`, recorded `existing: true` in
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace` (and its
  Prop-valued property theorem `schemeSheaf_isAlgebraicSpace`). This definition node
  owns the actual Yoneda representable scheme sheaf.
- Newly cited landed `def-sfb-space-sheaf-fibre-product`, recorded `existing: true` in
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `enlargedFibreProduct` and
  `enlargedFibreProductFst`. This definition node owns the actual sheaf pullback and
  its first projection; their data are not selected from an undetermined existence.
- Newly cited landed `def-sfb-proper-curve-moduli`, module
  `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapIsQuasiCompact`, the existing
  affine-scheme-test quasi-compactness predicate used in hfp and properness.

The four landed definition-node ids are added to stmt_deps under the explicit landed-node rule.
There are no new nodes, dependency repairs, or statement changes. The helper belongs to
this node's stated fibre-dimension function and is listed in lean.declarations.

Proof-only imports include the stated locality, affine atlas and chartwise permanence
modules and Mathlib's coproduct, étale and dimension-monotonicity modules. The lower/upper
semicontinuity, atlas topological dimension, and field-extension-dimension proof nodes
have no recorded Lean declaration in the read clone and so have no import to add yet.
No proof dependency is needed to define the statement. No import cycles are introduced.

Edge cases checked: empty T (all pointwise conclusions vacuous), empty X (only empty
charts of fibres, supremum bottom, constant bottom function, empty finite-dimensional
strata), identity family (dimension zero), disjoint unions of different-dimensional
proper flat families (maximum dimension, without purity/connectedness), empty T' and
identity base change, arbitrary characteristic and arbitrary residue-field extensions.
The codomain's +∞ value is explicitly ruled out rather than silently truncated.

Searches actually run:

- msearch leanfinder: “A proper flat finitely presented morphism of algebraic spaces has
  locally constant fibre dimension invariant under arbitrary base change”: 8 hits,
  scheme flat/smooth/locally finite presentation base-change results; no exact statement.
- msearch loogle: `IsLocallyConstant, topologicalKrullDim`: 0 hits.
- msearch grep: `fibre.*[Dd]im|fiber.*[Dd]im|[Dd]im.*[Ff]ib` in AlgebraicGeometry:
  2 hits (quasi-finite scheme fibre, elliptic-curve documentation), no exact statement.
- msearch leansearch: “The dimension of fibres of a proper flat finitely presented morphism
  of algebraic spaces is locally constant”: 8 hits, module rank local constancy and
  generic local-constancy lemmas, no algebraic-space fibre-dimension result.
- rg of WeilConjectures and Sheaf for fibreDimension/fiberDimension/fibreDim/fiberDim,
  chart dimension, space dimension and this node id: the upstream
  finiteLocallyFree_fiberDimension_isLocallyConstant concerns vector-space ranks, not
  Krull dimensions. No node-id match upstream. Existing localFibreDimension is at a
  source point, not the dimension of an entire fibre. etaleDimension is a different
  general presheaf formula (supremum of local dimensions), so the node's exact chart
  formula is supplied as the helper without restating either existing definition.
- Read the DAG records and modules for existing space morphism predicates and the
  canonical sheaf fibre product rather than supplying duplicate definitions.

Validation: scompile.py compiled both the isolated sandbox module and the actual module
cleanly against the live library, with autoImplicit false. No theorem is proved.
No STATEMENT-DISPUTED flag or mathematical node fault was found.


## Returned delivery repair

H2 (immutable returned head `637692340d58`): replaced the statement dependency
`lem-trf-space-enlarged-etale-ringed-site-model` by the existing definition owners
`def-trf-scheme-algebraic-space` and `def-sfb-space-sheaf-fibre-product`.
Kept `def-sfb-space-morphism-properties` and also cited `def-sfb-proper-curve-moduli`
for `MapIsQuasiCompact`, as the return optionally suggested. Read each owner's node
statement, existing Lean record, and the definitions in EnlargedEtaleRingedSite
(lines 79, 230, 236) and ProperCurveModuli (line 55); these are precisely the constructions
and predicate already used in the module. The theorem node no longer occurs in stmt_deps.

Compared the retained delivery with the current read-only main node: only lean and
stmt_deps differed. Rebased the sandbox node on that current node, retaining the entire
returned lean record and Lean module byte-for-byte, and applying the dependency repair.
The source statement, proof, proof_deps, and all other node fields are unchanged.
The report's dependency ownership list above now reflects all four added definition nodes.
The authorized delivery wrapper rebases the packet on current main for dry-run and push.
The prescribed fresh compile and dry-run are run before re-delivery.

## Second reading by Q75

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
