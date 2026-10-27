## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceAbsoluteNoetherianApproximation` states
`AlgebraicGeometry.AlgebraicSpace.exists_absoluteNoetherianApproximation`, with its
single proof left `sorry`. There are no definitions or extra proof obligations.
The source was read at `literature/stacks-project/spaces-limits.tex`,
`proposition-approximate` (Tag 07SU), including the full filtration/gluing proof,
and `spaces-morphisms.tex`, `lemma-locally-finite-type-locally-noetherian`
(Tag 04ZK). The theorem docstring records the node's complete proof route.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Work with algebraic spaces over a scheme S | Existing `AlgebraicSpace S`, a full subcategory of big fppf sheaves with representable diagonal and a surjective representable etale scheme atlas. |
| Size convention | Explicit `universe u`; schemes and fields in `Type u`, algebraic spaces over `Scheme.{u}`, and small index `I : Type u`. |
| S = Spec Z | `AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))`; lifting the integers places their unchanged ring in the chosen universe. |
| Y quasi-compact | `hqc : CompactSpace (Point Y.obj.obj)` with the existing atlas point topology. This is precisely the finite-subcover condition. |
| Y absolutely quasi-separated | `hqs : IsAbsolutelyQuasiSeparated Y`. This existing predicate is the equivalent affine-pair test for the absolute diagonal (Tag 0AHR), including without a qs hypothesis on a general base. |
| Small nonempty directed set | Existential `I : Type u`, `Preorder I`, `Nonempty I`, `IsDirected I (· ≤ ·)`, using the project's Stacks directed-set convention. |
| Inverse system over Spec Z | `D : Iᵒᵖ ⥤ AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))`. Its objects and all transitions already live over this base. |
| Affine transitions | For every `i ≤ j`, `MapIsAffine (D.map (homOfLE h).op)`. The existing definition supplies affine representing source schemes and actual pullback squares for every affine scheme test. |
| Y is isomorphic to the inverse limit | A cone transformation `π : (Functor.const Iᵒᵖ).obj Y ⟶ D` and `Nonempty (IsLimit (Cone.mk Y π))`. This is exactly the limit universal property with vertex Y; it requires no preselected limit or extra limit-existence assumption. |
| Every stage quasi-separated | `∀ i, IsAbsolutelyQuasiSeparated (D.obj (op i))`. |
| Every stage finite type over Z | `∃ p : D.obj (op i) ⟶ schemeSpace (Over.mk (𝟙 (Spec ...))), MapIsFiniteType p`. The existing predicate is affine-test quasi-compactness and the compatible-etale-chart test for locally finite type. The target is the representable terminal base, so p is the unique structure morphism, not a freely chosen additional morphism or a stronger hypothesis. All diagrams of such structure morphisms commute automatically. |
| Every stage quasi-compact | `CompactSpace (Point (D.obj (op i)).obj.obj)`. Together with the preceding qs clause this supplies the two global parts of the node's Noetherian convention. |
| A locally Noetherian etale scheme atlas for each stage | Existential `U : Over (Spec ...)` and `a : yoneda.obj U ⟶ (D.obj (op i)).obj.obj`, with `IsEtale a ∧ IsSurjective a ∧ IsLocallyNoetherian U.left`. Both etaleness and surjectivity have the recorded representable scheme-test meaning. The final class is the existing scheme class, not a new space predicate. |
| No Noetherian or finite type hypothesis on Y | The only geometric hypotheses on Y are hqc and hqs. Neither atlas Noetherianity nor finite type is imposed on Y. |

The introductory definitions of qc/qs morphisms and finite presentation set the
meaning of the words used in the node and its proof; they are not additional
hypotheses on Y or additional conclusions about the transitions. The theorem
uses the existing definitions, including `MapIsQuasiCompact` through
`MapIsFiniteType`, and does not add a finite-presentation assumption.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map` (scheme structure/signature, morphism signature and spectrum
  docstrings read).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`,
  `IsSurjective`, and `EtaleSite`; their full scheme-test signatures were read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace` and its universal property, with
  `etaleCover_pullback` and `etale_fibreProduct_isScheme` read as well.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`;
  `Point` and `schemePointMap` are from its public dependency
  `AlgebraicSpacePointClasses`. The final-topology signature was read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsFiniteType`
  and its dependencies `MapIsLocally`, `MapIsQuasiCompact` (the latter defined in
  `ProperCurveModuli`). All full signatures and defining predicates were read.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, the
  every-affine-open Noetherian-ring class equivalent to the node's affine-cover
  formulation.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated`, already carried by
  `def-sfb-space-absolute-quasi-separated`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite`: `MapIsAffine`,
  already carried by `def-sfb-space-affine-quasifinite-properties`.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`, the actual
  Yoneda sheaf of a scheme with its algebraic-space proof. Its owning definition
  node is `def-trf-scheme-algebraic-space`, with `existing: true` and this exact
  module. The theorem node for the enlarged etale site is not needed as a
  statement dependency for this definition.

The last three already-landed owner nodes were added to `stmt_deps` to cite
those existing notions. No new node or dependency repair was needed. The
metatheoretic size-convention node has no Lean declaration, as its record says.
The algebraic-space category and spectrum dependencies are public through the
statement imports; the proof modules already recorded on the base are imported
privately. The still-unstated proof dependencies cannot yet be imported:
`lem-sfb-qcqs-space-fibre-product`, `lem-sfb-qcqs-space-splitting-filtration`,
`lem-sfb-scheme-approximation-prescribed-open`,
`lem-sfb-space-affine-limits-schematic-stages`, `lem-sfb-space-affine-locality`,
`lem-sfb-space-etale-monomorphism-open`, `lem-sfb-space-etaleness-eventual-stage`,
`lem-sfb-space-fp-qcqs-source`, `lem-sfb-space-integral-qcqs-permanence`,
`lem-sfb-space-qcqs-permanence`, and `lem-sfb-space-qs-atlas-criterion`.
These are proof prerequisites only; none is needed to type this statement.

Edge cases checked before writing:

- Empty Y is included: the constant one-stage empty scheme system has the
  required properties, with an empty locally Noetherian scheme atlas.
- The index is explicitly nonempty; no empty inverse diagram can incorrectly
  witness the conclusion. Singleton systems remain allowed.
- No nonemptiness, reducedness, irreducibility or separatedness is imposed on
  stages or atlases. Absolute qs does not impose separatedness.
- Positive-characteristic spaces remain spaces over the lifted integer spectrum.
  No characteristic or field hypothesis was added.
- Arbitrarily non-Noetherian qcqs Y remains admissible, for example an affine
  scheme over a polynomial ring with infinitely many variables.
- The order is a preorder with common upper bounds, not a total order. Its
  opposite gives the correct direction j to i when i ≤ j.
- The locally Noetherian atlas is existential for every stage, exactly as in
  the node; neither a finite atlas nor a Noetherian assumption on every chart
  was imposed as a stronger statement.

Searches actually run via `msearch.py Q43 lem-sfb-space-absolute-noetherian-approximation`:

- LeanFinder: `A quasi-compact quasi-separated algebraic space is an inverse
  limit of finite type algebraic spaces over the integers with affine transition
  maps` returned eight scheme/topological hits, including
  `Scheme.exists_isQuasiAffine_of_isLimit`, `Scheme.exists_isAffine_of_isLimit`,
  and `Scheme.nonempty_of_isLimit`; none is the algebraic-space approximation.
- Loogle: `AlgebraicGeometry.AlgebraicSpace, IsLimit` returned zero hits with
  `unknown identifier 'AlgebraicGeometry.AlgebraicSpace'`, consistent with the
  algebraic-space framework belonging to this project.
- Mathlib grep: `AlgebraicSpace|absolute_noetherian|noetherian_approximation`
  under `AlgebraicGeometry` returned zero hits.
- LeanSearch: `Every quasi-compact quasi-separated algebraic space is a limit
  of finite type spaces over the integers` returned eight scheme and topology
  hits (`QuasiSeparatedSpace`, `quasiCompact_iff_compactSpace`,
  `QuasiSeparated.diagonalQuasiCompact`, etc.), no approximation theorem.
- Direct rg of `lean/WeilConjectures` for the node id returned no match. Searches
  there for absolute/Noetherian approximation found the scheme theorem
  `Scheme.nonempty_noetherianApproximation` in
  `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`, whose full
  docstring and signature were read. It is already the recorded proof
  prerequisite `prop-nagata-noetherian-inverse-system`, not this space theorem.
- Direct rg of `lean/Sheaf/AlgebraicGeometry` for space approximation and
  `MapIsAffine`, `IsAbsolutelyQuasiSeparated`, `schemeSpace` found the reused
  definitions and downstream proof references to this node, but no declaration
  already stating this theorem. The proposed full declaration name was also
  checked against project/upstream and Mathlib sources, with no existing hit.

No statement correction or mathematical dispute was found. The node's statement,
proof, proof dependencies and all other fields besides `lean` and the three
added existing owner ids in `stmt_deps` are preserved.

Validation: prescribed `scompile.py` compiled the statement both as the private
sandbox module and at its intended library module name, with no errors or
warnings. The final header exposes statement dependencies and keeps proof
imports private. Delivery preflight and its final per-file compile are run below.

## Second reading by Q43

A separate rereading in this worker compared the actual signature and node
again with Tag 07SU and the Noetherian consequence in Tag 04ZK. The dispatcher
explicitly forbids starting other agents; no independent worker review is
claimed here. The maintainer performs the independent delivery review.

The rereading checked: base Spec Z with an explicit universe lift; exactly qc
and absolute qs on Y; a small nonempty directed preorder; a functor on its
opposite; affine transition maps; the cone vertex literally Y; finite type
through the existing chart-test predicate on the unique base map; and the three
Noetherian clauses (qc, qs, locally Noetherian surjective etale scheme atlas).
The cone's naturality supplies all compatibility equations. No HasLimit binder
is assumed, and the statement contains no chosen noncanonical construction.
The scheme atlas maps have the same representability convention as the node.
The empty-space and singleton-index cases and the absence of Noetherianity on
Y were rechecked. No mathematical mismatch was found. This pass removed an
ambiguous draft phrase "integral stages" from the docstring and made the direct
point-topology and fibre-product statement imports public. The signature did
not change.


## Repair of return for head 148fb3d2b39b

H2: replaced `lem-trf-space-enlarged-etale-ringed-site-model` in `stmt_deps`
with the live definition owner `def-trf-scheme-algebraic-space`. Read that
node's statement and existing Lean record, and reread the actual `schemeSpace`
definition in `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: its data is
exactly the Yoneda representable sheaf, with the named algebraic-space property
proof. This supplies precisely the scheme-as-space construction used for the
terminal base in the signature. Updated the dependency account above.

Compared the retained delivered node with the current live node and reapplied
only `lean` and the authorized additions to `stmt_deps` on the current live
metadata. The Lean source and signature are unchanged from the returned delivery;
the maintainer's mathematical check of all hypotheses and clauses therefore
continues to apply. No extra definition, theorem dependency, or statement
correction was introduced. This repairs the sole numbered return point.
Validation for this repair uses `scompile.py`, then `deliver2.py --no-push` and
`deliver2.py` against the current live base.
