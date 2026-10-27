## Worker report

Delivery: `lean/Sheaf/AlgebraicGeometry/StackPointTopologyFlatLfpOpen.lean`.
Source read: `literature/stacks-project/stacks-properties.tex`, definition-points and
its following paragraph (04XG, lines 763 onward), lemma-points-cartesian (04XH),
and the full statement and proof of lemma-topology-points (04XL, lines 938–1035).
No correction of the informal statement is needed.

The module constructs an actual topology, residue-field chart maps, and the canonical
comparison with the existing algebraic-space point classes. It states three named
proof obligations with `sorry`: comparison well-definedness, agreement of topologies,
and the atlas/continuity/openness theorem. Every definition has real data. The
well-definedness theorem determines the proof of descent of a specified function;
it chooses neither a point, an atlas nor a map.

Hypotheses and clauses, matched individually:

- The base scheme is `{S : Scheme.{u}}`. The source and target stacks are
  `BasedCategory.{v₁, w₁} (Over S)` and `BasedCategory.{v₂, w₂} (Over S)`.
  Their object and morphism universes remain independent. Tests, field spectra,
  algebraic spaces and charts use the same universe `u` as the base schemes.
- An algebraic stack means `IsAlgebraicModuliStack F`: the existing predicate
  is precisely `IsModuliStack F ∧ HasAlgebraicSpaceDiagonal F ∧ ∃ U a,
  IsSmoothModuliAtlas F U a`. The atlas definition includes algebraic-space
  representability, smoothness and surjectivity after every scheme base change.
  Thus no separatedness, DM, finite-type, quasi-compactness, or additional atlas
  hypothesis is imposed.
- Field-valued objects and their equivalence classes are the existing
  `ModuliFieldObject F`, `ModuliFieldRelation F`, and `ModuliPoints F`, not a new
  quotient. In a category fibred in groupoids, the equivalence closure of arrows
  between field objects is exactly the common-extension/isomorphism equivalence:
  cartesian lifting identifies an arrow with an isomorphism after field extension,
  and common extensions amalgamate zigzags. `moduliPointMap` is the existing
  quotient map induced by the actual functor on objects. It implements composition
  on representatives without an arbitrary function parameter.
- For a scheme chart `p`, `moduliSchemePointMap p x` applies `moduliPointMap p`
  to the Yoneda object of the residue-field morphism
  `U.left.fromSpecResidueField x`. Its `Over` source includes the composite to S.
  This is the actual map from ordinary scheme points, rather than from a discrete
  topology on field representatives.
- The topology is `moduliPointTopologicalSpace F`, the supremum of the coinduced
  topologies of these maps over all `U`, `p`, and `IsSmoothModuliAtlas F U p`.
  This is a construction with no chosen atlas and no proof placeholder in its data.
- The first conjunct of `stackPointTopology_flat_lfp_open` says, for EVERY smooth
  surjective scheme atlas and EVERY subset W,
  `IsOpen W ↔ IsOpen (moduliSchemePointMap p ⁻¹' W)`. In particular the constructed
  topology is the quotient topology of each individual atlas. This is both the
  required characterization and atlas independence, and determines the topology
  uniquely since an algebraic stack has at least one such atlas.
- Agreement with algebraic spaces is separately stated as
  `moduliSpacePointMap_isHomeomorph (A : AlgebraicSpace S)`.
  Its concrete map goes from the EXISTING `AlgebraicSpace.Point A.obj.obj` with
  the EXISTING `pointTopologicalSpace` to `ModuliPoints (discreteModuli A.obj.obj)`
  with the newly constructed stack topology. A representative `x` goes to
  `CostructuredArrow.mk (yonedaEquiv.symm x.value)` over its actual field spectrum.
  `moduliSpaceFieldObject_rel` is exactly the quotient well-definedness obligation.
  A homeomorphism here expresses the node's agreement of the two point spaces and
  their topologies, with the canonical comparison fixed, not merely an unspecified
  equivalence or an arbitrarily selected topology. Schemes are the representable
  case, where the chart map is the residue-field map used above.
- The second main conjunct quantifies over every algebraic stack G and EVERY
  `f : BasedFunctor F G` and concludes `Continuous (moduliPointMap f)`.
  There is no representability assumption on f.
- The third conjunct quantifies over EVERY `A : AlgebraicSpace S` and every
  `q : BasedFunctor (discreteModuli A.obj.obj) F`. Flatness is
  `ModuliSpaceTest @Flat q`; local finite presentation is
  `ModuliSpaceTest @LocallyOfFinitePresentation q`. These existing tests say that
  every scheme base change has an algebraic-space presentation with its specified
  projection, and every representable etale scheme chart has the stated SCHEME
  property on its composite with this projection. They are precisely the node's
  chartwise conventions. Representability is a consequence for a space source and
  an algebraic-stack target, so it is not imposed as a separate hypothesis.
- The openness conclusion is
  `IsOpenMap (moduliPointMap q ∘ moduliSpacePointMap A.obj.obj)`.
  This uses the usual topology on the original algebraic-space points, as required.
  It is the actual |q| after the canonical identification, not the image of all
  points only. There is no surjectivity hypothesis on q. Continuity for the
  corresponding stack map is already covered by the second conjunct and agreement
  with algebraic spaces by the comparison theorem.

Dependency declarations used (source signatures and docstrings read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map`; field spectra and all schemes are these existing objects.
- `Mathlib.Algebra.Field.Defs`: `Field`; it is used inside the existing field-object
  and algebraic-space representative types.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`;
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`;
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.discreteModuli`, `IsModuliStack`, `HasSpaceBaseChange`,
  `HasAlgebraicSpaceDiagonal`, `SpaceMapIsSurjective`,
  `IsRepresentableByAlgebraicSpaces`, `moduliTwoFiberProduct` and `ModuliTwoIso`.
  Definitions at lines 372–541 were read, including the actual projection comparison.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsEtale`; the full subcategory, diagonal and atlas definitions
  at lines 41–88 were read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`:
  `AlgebraicSpace.PointRepresentative`, `.Rel`, `Point`, `schemePointMap`;
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicSpace.pointTopologicalSpace`. Both files were read in full.
- Added the ALREADY LANDED `def-sfb-algebraic-moduli-stack` to stmt_deps:
  `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`,
  `CategoryTheory.IsAlgebraicModuliStack`, `IsSmoothModuliAtlas`, `SpaceMapIsSmooth`.
  These replace no existing definition; they provide the exact general-stack
  predicate already defined for this project.
- Added the ALREADY LANDED `def-sfb-dm-stack-morphism-properties` to stmt_deps:
  `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`,
  `CategoryTheory.ModuliFieldObject`, `ModuliFieldRelation`, `ModuliPoints`,
  `moduliFieldMap`, `moduliPointMap`, `ModuliSpaceTest`. Despite the owning node's
  DM title, these declarations have general BasedCategory signatures and define
  exactly the general field-object quotient and representable chartwise tests
  needed here. Its etale-atlas closed-set predicate is NOT used for Artin stacks.
- Plain proof import: `Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatLfpUniversallyOpen`,
  `AlgebraicGeometry.AlgebraicSpace.universallyOpen_of_flat_of_locallyOfFinitePresentation`.
  The other three proof-only stack lemmas have no Lean records locally, so no
  nonexistent proof import is added. They are not prerequisites for this statement;
  their mathematical argument is preserved, by node id, in the theorem docstring.

Edge cases checked before writing: empty base, empty stack, empty source algebraic
space, empty W, W the entire point space, the identity scheme atlas, a nonsurjective
flat lfp q, and stacks with nontrivial stabilizers. No nonemptiness or characteristic
assumption is imposed. For an empty stack, the empty atlas gives the topology on the
empty point set. The openness conclusion is for all open subsets, including empty
images. The construction does not discard automorphisms before defining the stack;
it takes the point quotient only at the final topological-space stage. Field tests
use Type u, not an independent lower universe. There is no restriction relating the
two stacks' total-category universes.

Searches actually run:

- `msearch.py ... leanfinder`, query: `Topology of algebraic stacks on field valued
  objects with open flat locally finitely presented maps from algebraic spaces`.
  Eight hits, including `AlgebraicGeometry.UniversallyOpen.of_flat` and scheme site
  definitions; none states stack point topology or space-to-stack openness.
- `msearch.py ... loogle`, query: `AlgebraicGeometry.AlgebraicStack, IsOpenMap`.
  Zero hits; the AlgebraicStack identifier is unknown to that service.
- `msearch.py ... grep`, query: `AlgebraicStack|stackPoint|UniversallyOpen.of_flat`.
  One hit: Mathlib/AlgebraicGeometry/Morphisms/UniversallyOpen.lean:147,
  `UniversallyOpen.of_flat`, for schemes only.
- `msearch.py ... leansearch`, query: `The topology on an algebraic stack is the
  quotient topology from any smooth surjective scheme atlas`. Eight hits, including
  `Flat.isQuotientMap_of_surjective` (schemes) and ordinary quotient topology; no match.
- `rg` of `lean/WeilConjectures` for the item id and for
  `moduliPointTopologicalSpace|moduliSpacePointMap|ModuliPoints|AlgebraicStack`:
  no hits. `rg` of `lean/Sheaf` for `AlgebraicStack|StackPoint|stackPoint|
  IsAlgebraicModuliStack|Moduli.*Point|SpaceMapIsSmooth` found the landed general
  algebraic-stack predicate and DM-owned point/test interfaces listed above, which
  are reused. No stack TopologicalSpace instance was found.
- `rg` of Mathlib, WeilConjectures, Sheaf and `dag/lean_names_upstream.json` for
  every proposed declaration name found no clashes.
- The source of `AlgebraicSpaceFlatLfpUniversallyOpen` was inspected: it concerns
  maps between two algebraic spaces, not the current target stack statement.
- The example `CompactObject.lean` was opened and currently contains only
  `module` and a withdrawal notice. The current brief's explicit module-mode,
  exposed-public-section, namespace and source-docstring conventions are followed.

No new DAG node, dependency repair, statement correction or disputed statement.
The two additions to stmt_deps are existing landed definition nodes, as authorized.

## Second reading by Q146

Author's second reading for direct delivery; independent review is the maintainer's.
I reopened the item, the constructed module and Stacks 04XG/04XL. The atlas criterion
has the required biconditional and quantifies over every smooth SURJECTIVE atlas;
continuity is for arbitrary stack maps, not only representable maps. Openness is for
all q from arbitrary algebraic spaces, and uses separate flat and lfp chart tests.
The conclusion uses the original algebraic-space point topology via the explicit
Yoneda comparison. The extra comparison theorem expresses the node's agreement
clause; the well-definedness theorem is solely the proof needed to descend that
specific map through the existing quotient. No duplicate point relation was added.
I checked both tests' full signatures, including actual projection compatibility.
I also checked that the new topology uses smooth atlases, not the existing DM-only
etale-atlas closed-set predicate. Nontrivial automorphisms and empty sources are
retained. No hypotheses or conclusion clauses were changed on this rereading.
The first compile required an explicit `Over` source annotation for the residue-field
map; the subsequent compile passed with no errors or warnings.
