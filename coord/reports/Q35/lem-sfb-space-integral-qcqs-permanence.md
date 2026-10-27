## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceIntegralQcqsPermanence` states
`AlgebraicGeometry.AlgebraicSpace.integral_qcqs_permanence`, with a single `sorry`.
It introduces no definitions and proves nothing. The node's statement, proof, and
proof dependencies are unchanged. Its statement dependencies additionally name the
three already landed nodes supplying the absolute quasi-separatedness, affine-map,
and separated-map predicates used below. This is the permitted addition of existing
landed statement dependencies, not a statement correction.

Clause and hypothesis correspondence:

* The base scheme is `{S : Scheme.{u}}`, and all spaces are `AlgebraicSpace S`.
  `universe u` is explicit and `autoImplicit` is false. These are the existing fppf
  sheaves on the big site with representable diagonal and surjective etale atlas.
  There is no separatedness or quasi-compactness assumption on the base scheme.
* The point topology is `pointTopologicalSpace` on the existing field-valued point
  quotient `Point`. `CompactSpace (Point X.obj.obj)` is precisely the finite-subcover
  condition for all open covers, with no Hausdorff condition.
* Absolute quasi-separatedness is `IsAbsolutelyQuasiSeparated X`. Its actual
  definition tests compactness of `Point (Limits.pullback a b)` for all affine
  scheme maps into X; Stacks 0AHR(3) identifies this with the quasi-compact absolute
  diagonal over Spec Z. It does not replace absolute quasi-separatedness by a
  condition on the diagonal over the arbitrary base S.
* Integral `g : B ⟶ X` is the hypothesis
  `IsRepresentableWith (fun _ _ p ↦ IsIntegralHom p.left) g.hom.hom`.
  The existing predicate supplies the representing scheme and its cartesian square
  for every scheme test; Mathlib `IsIntegralHom` includes affineness and integral
  maps on affine-open rings. Thus the representability and scheme-test integrality
  in the node are both present, with no surjectivity or finite-type hypothesis.
* Its first three conclusions are `MapIsAffine g`,
  `MapIsQuasiCompact g.hom.hom`, and `MapIsSeparated g`. The affine predicate asks
  for an affine representing source on every affine test. The quasi-compact
  predicate asks for compact point space of each affine-test pullback. The
  separated predicate is representability of the relative diagonal by closed
  immersions, using Mathlib `IsClosedImmersion` on the projections.
* The qcqs-target clause is
  `CompactSpace (Point X.obj.obj) → IsAbsolutelyQuasiSeparated X →
  CompactSpace (Point B.obj.obj) ∧ IsAbsolutelyQuasiSeparated B`.
  Both target hypotheses and both source conclusions are retained.
* A scheme target is an arbitrary `T : Over S` with
  `Nonempty (X.obj.obj ≅ yoneda.obj T)`. Absolute separatedness is the additional
  hypothesis `T.left.IsSeparated`, Mathlib's separated structure map to the
  terminal scheme Spec Z. The conclusion supplies `U : Over S`, an isomorphism
  `B.obj.obj ≅ yoneda.obj U`, and `U.left.IsSeparated`.
  The additional quasi-compactness assertion is
  `CompactSpace T.left → CompactSpace U.left`. This imposes no quasi-compactness
  hypothesis on the scheme-representability/separatedness assertion itself.
  The same representing U has both properties when T is compact.
* The second outer conjunct quantifies independently over all `A X` and `f : A ⟶ X`.
  Its only hypotheses are `CompactSpace (Point A.obj.obj)` and
  `IsAbsolutelyQuasiSeparated X`; its conclusion is `MapIsQuasiCompact f.hom.hom`.
  It does not depend on an integral map, or require representability of f.
* The last independent conjunct quantifies over `U X` and `j : U ⟶ X`, with
  `IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom`, the node's
  scheme-test definition of an open immersion. This expresses an open subspace
  by its inclusion, without choosing a different copy of its presheaf.
  `CompactSpace (Point U.obj.obj)` retains the quasi-compact-open hypothesis;
  `IsAbsolutelyQuasiSeparated X` gives `IsAbsolutelyQuasiSeparated U`.
* Geometric points, geometric fibres, and etaleness are background conventions in
  this node, not extra hypotheses or conclusions. This theorem introduces no new
  geometric-point or fibre construction; all fibre products used by its predicates
  are the canonical presheaf/sheaf pullbacks already in the dependencies.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsRepresentable`, `IsEtale`, and
  `IsAlgebraicSpace` (full-subcategory sheaf and scheme-test interfaces).
* `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `PointRepresentative.map`,
  `pointImage`, `pointTopologicalSpace`; the existing point classes are imported.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme`; fibre products throughout have this convention.
* `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; and
  `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.SpecToEquivOfField`.
  These are the node's geometric-point convention; no geometric point needs a
  separate binder in the permanence assertions.
* `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`; and
  `Mathlib.AlgebraicGeometry.Morphisms.Integral`: `IsIntegralHom`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated` (added dependency
  `def-sfb-space-absolute-quasi-separated`).
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite`: `MapIsAffine`
  (added dependency `def-sfb-space-affine-quasifinite-properties`).
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsSeparated`
  (added dependency `def-sfb-space-morphism-properties`). Its imported module
  `Sheaf.AlgebraicGeometry.ProperCurveModuli` supplies
  `AlgebraicGeometry.AlgebraicSpace.MapIsQuasiCompact`, the existing point-space
  scheme-test notion, not a new predicate in this delivery.
* `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `Scheme.IsSeparated`.

Proof-only imports cover the available recorded modules:
`AlgebraicSpaceOpenSubspace` (`OpenSubspace`), `AlgebraicSpaceFiniteAffineSubatlas`
(`exists_finite_affine_subatlas`, `compactSpace_points_of_surjective`,
`compactSpace_points_of_scheme_atlas`), and `SpaceQuasiCompactAffineTests`
(the four recorded quasi-compactness comparison/locality statements).
The Mathlib match of `lem-weil-pbc-affine-scheme-qcqs` is imported from
`Mathlib.AlgebraicGeometry.AffineScheme` and
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
The other proof dependencies have no recorded Lean or Mathlib declarations yet:
`lem-sfb-qc-space-affine-etale-atlas`, `lem-sfb-space-affine-locality`,
`lem-sfb-space-qcqs-permanence`, and `lem-sfb-space-separated-fp-composition`.
They are preserved in the DAG and explicitly named in the proof docstring; no
statement interface depends on these still-unstated proof results.

Edge cases checked before writing: empty B and empty open U are allowed because
no `Nonempty` of points, fields of points, or atlases is assumed. The `Nonempty`
binders only package isomorphisms, and allow the empty representing scheme.
If X is empty, the same universal scheme-test predicates apply. No hypothesis
of quasi-compactness of B occurs in the integral clause. No quasi-separatedness
of A is added to the arbitrary-f clause. The base S can fail to be separated or
quasi-separated. The open source is required compact even though the usual
stronger open-subspace assertion can omit that hypothesis. No stronger theorem
was substituted. For the identity integral map, the first clause recovers the
input qcqs and scheme-separated properties without changing them. No
characteristic or nonzero-ring restriction occurs.

Searches made:

* `msearch.py ... leanfinder "Integral morphisms of algebraic spaces are affine
  quasi compact separated and preserve absolute quasi separatedness"`: eight
  hits, including `IsIntegralHom.hasAffineProperty`, `IsIntegralHom`,
  `IsIntegralHom.toIsAffineHom`, `IsIntegralHom.of_comp`, and a scheme
  quasi-separatedness instance. All are scheme-level; none is this statement.
* `msearch.py ... loogle "AlgebraicGeometry.IsIntegralHom,
  AlgebraicGeometry.QuasiCompact"`: nine normalization declarations for schemes;
  none states algebraic-space permanence.
* `msearch.py ... grep "integral.*(quasi|separated)|IsIntegralHom"
  AlgebraicGeometry/Morphisms`: twelve hits in Integral, Proper, and Finite,
  confirming the existing scheme predicate and its scheme-only scope.
* `rg` over `lean/WeilConjectures` for integral/absolute-quasi-separated/affine/
  separated algebraic-space interfaces found no matching statement;
  `grep -rn 'lem-sfb-space-integral-qcqs-permanence' lean/WeilConjectures`
  found no occurrence.
* `rg` over `lean/Sheaf/AlgebraicGeometry/AlgebraicSpace*` and `Space*` found the
  existing predicates listed above and the scheme-test comparison theorem;
  no integral-permanence declaration. A further search for
  `def (IsIntegral|MapIsIntegral)` and integral qcqs/permanence theorems found
  no matching algebraic-space statement. `rg` of the DAG located the owning
  nodes for all three extra landed predicates, which are cited rather than
  duplicated.

Source checks: read the local Stacks `spaces-morphisms.tex` statements
`lemma-affine-representable` (03WE), `lemma-affine-local` (03WG),
`lemma-quasi-compact-quasi-separated-permanence` (073B), and
`definition-integral`; the node's explicit proof is reproduced step by step in
the declaration docstring. The earlier CompactObject example is now a withdrawn
module with no declarations; this delivery follows the current module-mode,
public-import, and exposed-public-section rules in the standing brief instead.

Validation: `scompile.py Q35 lem-sfb-space-integral-qcqs-permanence` compiled
the delivered module in sandbox and library modes, both cleanly (1.4 seconds
each). All Lean lines are at most 90 characters. The Lean record contains the
signature verbatim. No statement dispute, new node, dependency repair, or
statement correction was needed. The delivery dry run passed preflight and
the per-file compilation; nothing was pushed by that check.

## Second reading by Q35

Re-read the node against the final signature. The three outer conjuncts keep
the arbitrary-map and open-subspace claims independent of the existence of an
integral map. In the integral clause all three morphism properties occur, both
qcqs-target hypotheses and both qcqs-source conclusions occur, and the scheme
conclusion carries absolute separatedness plus precisely the optional compact
target implication. The source representation is an actual Yoneda isomorphism,
not a chosen arbitrary scheme. `Scheme.IsSeparated` concerns Spec Z, and the
space criterion is absolute rather than relative to S. The open-immersion
hypothesis is exactly the representable scheme-test condition in the node.
No nonemptiness or separation assumption on S was added. All proofs remain
`sorry`; the only additions to the DAG statement dependencies are the three
already landed owning nodes for predicates actually used in the signature.
