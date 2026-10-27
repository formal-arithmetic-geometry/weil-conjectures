## Worker report

This stage-2 delivery states `AlgebraicGeometry.SplitTorusFrames.split_torus_torsor_frame_geometry`
in `Sheaf.AlgebraicGeometry.SplitTorusTorsorFrameGeometry`. Its only postponed proof is this
named theorem, with all eight DAG proof steps in its docstring. Every helper has real data
or is a structure recording the theorem's conclusions; no helper asserts existence.

The inherited BLOCKED ending concerned stage-1 delivery of an already reviewed split.
The current queue assigns this node to stage 2 and the node has no Lean record. As
coord/brief-stage2.md section 0 requires, this delivery preserves the accepted split and
uses deliver2.py. There is no released repair note for the node.

Hypotheses and clauses, read against the node and the Stacks source:

- `k : Type u`, `[Field k]`, `S : Over (Spec (.of k))`, `Y : Over S.left`, and `r : ℕ`
  introduce exactly the field, base scheme, structure morphism q, and nonnegative rank.
  All scheme/test universes are the same u, so the test-scheme quantifiers are not vacuous.
- The five instances on `Y.hom` render faithfully flat and of finite presentation:
  `Flat`, `Surjective`, `LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated`.
  The last two are part of finite presentation in def-sbc-locally-finite-presentation,
  not additional assumptions.
- `act` is an actual k-scheme morphism Y times T to Y; `hone` and `hmul` give the
  right action laws on all k-schemes, and `_hinvariant` gives the action over S.
  Test-scheme equalities, including the triple product as a test, are scheme identities.
- `torsor` is precisely an isomorphism Y times_k T to Y times_S Y, with first projection
  y and second projection act. It does not assert only transitivity of geometric points.
- `Geometry.line` and `.invertible` give all r invertible modules using the recorded
  `Scheme.Modules.IsInvertible`. `FrameModel` supplies the actual scheme, universal
  frame, and bijective map induced by pulling that frame to every S-scheme. Thus it
  represents exactly Isom(O_U,f^*A), naturally, without a free choice of bijections.
- `Geometry.comparison` is an isomorphism in Over S from Y to the actual finite product
  of the frame models. Its over-category equation identifies q with the product projection.
  `FrameEquivariant` requires the coordinate frames to multiply by the pullback of the
  actual Laurent coordinate for every test scheme U, points y,z and torus point t with
  z=y*t. All frames are on the same tensor pullback along U.hom. This states exactly
  equivariance for the scalar action on frames; no separate unspecified action is chosen.
- `framesProduct` is the actual categorical product of the first j frame factors;
  `forget` is `Pi.lift` of the first j product projections. Its structure morphism and
  the over-category identities give the entire tower and its composite. The empty
  product is canonically the terminal object of Over S, namely S with identity.
- `rankTwo` is O plus `tensorPullback f.hom (dual A)`, so the dual convention is exactly
  B_j=f^*(A_j dual), not its inverse. `Compactification.quotient` uses the existing
  `TautologicalQuotient` for the canonical symmetric algebra of this rank-two module.
  Its `.inclusion`, `.openImmersion`, and `.overBase` are i_j, its open-immersion
  property, and p_j i_j=q_j for that fixed canonical relative Proj.
- `Compactification.image` says a morphism from every test scheme factors through i_j
  iff both pulled-back summand maps of that very quotient are isomorphisms. This is
  the exact open locus, including its scheme structure, not merely its point set.
- `.first` and `.first_eq` give O_Yj isomorphic to i_j^*O(1), specifically through the
  first summand of the universal quotient, with the canonical structure-sheaf comparison.
- `Good` renders smooth, closed diagonal, locally finite type and quasi-compact over k.
  `Geometry.good` gives this for all Y_j, including Y_0, and all P_j, conditionally on
  the same properties for S. No Noetherian, connectedness, nonempty-base or characteristic
  assumption is imposed.
- `.rank_zero` says q is an isomorphism for r=0; the comparison is then to the empty
  product over S, so it identifies q with the identity of S, as stated in the node.

Dependency declarations used:

- Mathlib: `Field`; `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Flat`, `Surjective`,
  `LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated`, `Smooth`,
  `LocallyOfFiniteType`, `IsClosedImmersion`, `IsOpenImmersion`;
  `CategoryTheory.Limits.pullback` and `.diagonal`, `Pi.π`, `Pi.lift`, products in Over,
  and the finite product structure from `Mathlib.CategoryTheory.Monoidal.Cartesian.Over`.
  Their recorded source modules and complete defining signatures/docstrings were read.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` (local rank-one freeness).
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank`, read as the dependency's general
  rank predicate; the rank-two module here is constructed from the unit and a line.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback`, `tensorPullbackSectionComp`,
  `tensorPullbackSectionAdjunction`; tensor inverse images throughout.
- `WeilConjectures.AlgebraicGeometry.Modules.Dual`: `Scheme.Modules.dual` is precisely
  internal Hom(A,O). `boundaryPullbackComparison` and `pullbackObjUnitIso` give the
  canonical comparison for the unit; no second inverse-image functor is defined.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `MultiplicativeType.splitTorus` is the product of the existing
  `StandardGroupSchemes.multiplicative` (Spec of the Laurent polynomial algebra),
  including its unit in rank zero. Its owning node is added to stmt_deps.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry`:
  `ProjectiveBundleQuotientGeometry.TautologicalQuotient` and
  `projective_bundle_quotient_geometry` provide the fixed canonical projective bundle,
  quotient, and twist. No private substitute for projective bundles is introduced.
- Proof imports include `WeilConjectures.AlgebraicGeometry.Descent`,
  `WeilConjectures.AlgebraicGeometry.FpqcMorphismsDescend`, and
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`. Other proof dependency
  modules (relative projective space, Fpqc covering comparison, smooth composition and
  locality, and closed immersion base change/composition) are already imported by the
  public statement dependencies. There is no import cycle or omitted proof import.

Sources opened: descent.tex proposition-fpqc-descent-quasi-coherent (023T),
lemma-finite-locally-free-descends (05B2); groupoids.tex
lemma-characterize-trivial-pseudo-torsors (0499), definition-principal-homogeneous-space
(049A); constructions.tex definition-projective-bundle (01OB), its following quotient
classification, and lemma-projective-space-bundle (01OE). These support the accepted
agent-extracted geometric consequence, rather than pretending it is one quoted theorem.

Edge cases: r=0 gives no lines or compactifications, terminal product and q isomorphism;
r=1 has P(O plus A dual), and evaluation of a frame on the dual gives the positive
scalar coordinate, not its inverse. Empty S has empty total schemes and all local
properties remain meaningful. Arbitrary characteristic and nonreduced test schemes
are retained. No separatedness, finiteness or smoothness is assumed of S until the
conditional geometric clause.

Searches actually run:

- msearch.py leanfinder: `A torsor under a split torus is the product of the frame
  schemes of invertible modules`: 8 hits on affine space and its coordinates, none
  stating this theorem or representing line frames.
- msearch.py loogle: `Scheme, Torsor, MulAction`: unknown identifier Scheme, no hits;
  repeated with `"AlgebraicGeometry.Scheme", "torsor"`: OK 0 hits.
- msearch.py grep: `structure.*(Torsor|RightAction)|def.*frameScheme` in
  AlgebraicGeometry: OK 0 hits.
- rg over lean/WeilConjectures, lean/Sheaf and Mathlib AlgebraicGeometry for
  `SplitTorus|splitTorus|FrameScheme|frameScheme|frame.*torsor|TorusTorsor`:
  found the existing split torus, étale frame torsors, and unrelated Picard/Kummer
  constructions; no frame-scheme representation and compactification theorem.
- rg for the exact node id in upstream and Sheaf: no existing declaration.
- DAG search for frame schemes and split-torus frame geometry: the item is the
  combined geometry theorem; no independent missing notion was introduced. Helpers
  specify its own universal-property and conclusion data, under brief section 1.

No statement correction, new node, dependency repair, or STATEMENT-DISPUTED finding.

Validation: the complete module compiled cleanly in sandbox and declared-module mode,
with no warnings (8.8 s and 10.0 s). The stage-2 server dry run passed both preflight
and compile. The initial kernel timeout was repaired by factoring scalar equivariance
into a named predicate on arbitrary test schemes, retaining its full mathematical
content; the delivered file needs no increased resource limit or linter suppression.

## Second reading by Q10

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
