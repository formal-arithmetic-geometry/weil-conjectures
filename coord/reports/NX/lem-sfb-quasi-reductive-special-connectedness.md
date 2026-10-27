## Worker report

The module Sheaf.AlgebraicGeometry.QuasiReductiveSpecialConnectedness states
AlgebraicGeometry.quasiReductive_special_connected. Its sole theorem has proof
`sorry`. There are no new definitions, new nodes, dependency replacements, or
statement corrections. The natural-language statement and all seven proof steps
are unchanged. Two already-landed definition nodes are added to stmt_deps:
def-sfb-reductive-torus-centralizer-terminology and def-kun-dimension. These supply
exactly the reductivity and dimension notions already mentioned in the statement.

Read Prasad--Yu, On quasi-reductive group schemes, at
https://arxiv.org/pdf/math/0405381: the definition before Theorem 1.2, Theorem
1.2(c), Proposition 4.4(i), and Section 5 first paragraph. The finite-type
specialization and geometric form agree with this node. No statement is disputed.
The accepted Q23 split is input to stage 2, and is preserved. The live queue lists
this node at stage 2; it has no Lean attachment or released repair note. The
inherited stage-1 accepted-item refusal is not a reason to leave it unstated.

Hypotheses and clauses, with their Lean renderings:

- A discrete valuation ring: `(A : Type u) [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A]`. The class is the nonfield local PID definition.
- Fraction field K: `(K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]`.
- Residue field k: the canonical quotient `IsLocalRing.ResidueField A`; its
  quotient map is `IsLocalRing.residue A`. This fixes k as the actual residue
  field, rather than introducing an arbitrary A-field.
- A chosen algebraic closure of k: `(Ω : Type u) [Field Ω]
  [Algebra (IsLocalRing.ResidueField A) Ω]
  [IsAlgClosure (IsLocalRing.ResidueField A) Ω]`. Ω is arbitrary with the specified
  embedding, not an unspecified geometric point or just an algebraically closed
  field without algebraicity. The special-fibre base map is exactly Spec of
  `(algebraMap (IsLocalRing.ResidueField A) Ω).comp (IsLocalRing.residue A)`.
- B finitely generated and flat over A: `(B : Type u) [CommRing B] [Algebra A B]
  [Algebra.FiniteType A B] [Module.Flat A B]`.
- G = Spec B, affine over Spec A, with its given group law:
  `(G : Grp (Over (Spec (.of A))))` and
  `(e : G.X ≅ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A B))))`.
  The isomorphism is in Over, so it identifies the structure map as well as the
  underlying scheme. This is an affine presentation of the given object, not a
  new affine hypothesis or a restriction to a different group. Every literal
  G = Spec B has the identity presentation. `Grp` contains `GrpObj G.X`, hence
  multiplication, identity, inverse, and the group diagrams over Spec A.
- The generic fibre is the scheme pullback of G.X.hom along Spec(A → K).
  Its structure map is `pullback.snd`. `[Smooth ...]` supplies exactly generic
  smoothness, and `[GeometricallyConnected ...]` means connectedness after every
  field extension of K, using the existing Mathlib predicate.
- H is the reduced neutral component, with induced group law: H is a bundled
  Ω-group, and `j` is a morphism from H to the group obtained by
  `(Over.pullback specialBaseMap).mapGrp.obj G`. Thus the multiplication and unit
  on H are compatible with those of the special fibre. The hypotheses
  `[IsClosedImmersion j.hom.hom.left]`, `[IsReduced H.X.left]`, and
  `hH : Set.range j.hom.hom.left = connectedComponent (GrpObj.onePoint ...)`
  identify its scheme structure, not only its rational points. A reduced closed
  subscheme with that image is the unique reduced closed subscheme on the
  identity component. Reduction preserves the underlying space, so this is the
  component of the reduction appearing in the node. This presentation adds no
  structural condition to the specified H and permits the given induced law.
- Reductivity of H: `hred : ReductiveTorusCentralizer.IsReductive H` is the
  already-landed predicate. Its affine finite-type and smooth clauses, geometric
  connectedness, and triviality of every smooth connected normal closed
  unipotent subgroup are the clauses in the node. Because Ω is algebraically
  closed, its geometric formulation is equivalent to the Ω-formulation here.
  Unipotence is the existing faithful closed matrix representation predicate;
  `SolvableGroupStructure.IsUnipotent` includes smoothness and tests nilpotence
  of the matrix minus identity on all algebraically closed extension fields.
- The dimension hypothesis is `hdim : topologicalKrullDim H.X.left =
  topologicalKrullDim (pullback (C := Scheme.{u}) G.X.hom genericBaseMap)`.
  These are dimensions of underlying topological spaces, not tangent dimensions
  or dimensions of sets of rational points.
- The conclusion is `ConnectedSpace (pullback (C := Scheme.{u}) G.X.hom
  specialBaseMap)`: the whole geometric special fibre, including any nonreduced
  structure, is connected. ConnectedSpace includes nonemptiness.
- No residue-characteristic hypothesis, henselian hypothesis on A, or smoothness
  hypothesis on G over A occurs. The module's docstring gives all seven proof
  steps and names their DAG inputs, including the coordinate boundedness argument.

Dependency declarations read and used:

- def-sc-discrete-valuation-ring: Mathlib.RingTheory.DiscreteValuationRing.Basic,
  IsDiscreteValuationRing (lines 55-60, docstring and full class).
- def-weil-algebraic-closure: Mathlib.FieldTheory.IsAlgClosed.Basic, IsAlgClosure
  (lines 262-269); read its IsAlgClosed and algebraicity fields. This is the
  arbitrary-closure interface recorded in the node's mathlib_match.
- def-weil-affine-spectrum: Mathlib.AlgebraicGeometry.Scheme, Spec and Spec.map
  (lines 469-480), including the full signature and docstrings.
- def-weil-pbc-flat-ring-map: Mathlib.RingTheory.RingHom.Flat, RingHom.Flat
  (lines 25-34) and Module.Flat; for an algebraMap these agree by
  RingHom.flat_algebraMap_iff. The statement uses Module.Flat A B directly.
- def-sc-group-scheme: Mathlib.CategoryTheory.Monoidal.Grp, GrpObj and Grp,
  together with WeilConjectures.AlgebraicGeometry.GroupScheme.Defs, whose
  introductory terminology documents the Over encoding and IsMonHom. The
  categorical group object is used over Spec A as the node explicitly prescribes.
- def-pc-fibre-product: Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback,
  pullback and pullback.snd (lines 94-115), and
  Mathlib.CategoryTheory.Monoidal.Cartesian.Over for product-preserving pullback
  and mapGrp. These retain exactly the pulled-back group law.
- def-sbc-smooth-morphisms: Mathlib.AlgebraicGeometry.Morphisms.Smooth, Smooth
  (lines 59-66). Its precise affine-local definition is the recorded one.
- def-weil-connected-scheme: Mathlib.Topology.Connected.Basic, ConnectedSpace
  (lines 699-710), including its nonemptiness field.
- Added landed def-sfb-reductive-torus-centralizer-terminology:
  Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology,
  AlgebraicGeometry.ReductiveTorusCentralizer.IsReductive. Read the whole
  signature and body, and the referenced SolvableGroupStructure.IsAlgebraic
  and IsUnipotent in Sheaf.AlgebraicGeometry.SolvableGroupStructure.
- Added landed def-kun-dimension: topologicalKrullDim in
  Mathlib.Topology.KrullDimension (lines 35-40); the node's recorded module
  WeilConjectures.Mathlib.Topology.KrullDimension reexports this definition.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Basic, GrpObj.onePoint
  (lines 86-89), gives the identity point without a choice of a point of G.
- AlgebraicGeometry.IsReduced in Mathlib.AlgebraicGeometry.Properties
  (lines 68-72), and IsLocalRing.ResidueField/residue in
  Mathlib.RingTheory.LocalRing.ResidueField.Defs (lines 28-40), are used directly.

Stated proof dependencies are plain imports: HasRingHomProperty.Spec_iff from
Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties;
Algebra.Smooth.exists_lift_of_henselianRing from
Sheaf.RingTheory.HenselianSmoothAlgebraLifting (read the complete signature and
proof docstring); and Scheme.Hom.denseRange_fieldPoints from
WeilConjectures.AlgebraicGeometry.DensePoints (lines 197-218). The four new
structural prerequisites in the accepted Q23 split have no Lean declarations,
so there are no module paths for them to import. They are proof dependencies,
not missing statement dependencies.

Edge cases checked before writing:

- The trivial model G = Spec A is included: H is the trivial group, both
  dimensions are zero, and the geometric special fibre is a point.
- Residue characteristic 2 and positive-characteristic nonreduced special
  fibres are permitted. Only H, never G or its entire special fibre, is assumed
  reduced; the source's exceptional nonsmooth models are not discarded.
- H and both fibres have identity sections, so the empty scheme cannot arise.
  ConnectedSpace correctly keeps nonemptiness rather than silently using
  preconnectedness. No positive-dimension assumption is made.
- Arbitrary fraction fields K and arbitrary specified algebraic closures Ω are
  quantified. One ambient universe u is the standard Scheme.{u} convention;
  u is arbitrary and can contain any given finite diagram of these objects.
- H is constrained by its whole topological image and its reduced scheme
  structure. It cannot be replaced by a proper smooth subgroup of smaller
  dimension with the same abstract rational-point group.

Searches made in this session (all actually run):

- msearch.py leanfinder: "Affine flat group scheme over a discrete valuation
  ring with smooth geometrically connected generic fibre and reductive special
  identity component has connected special fibre". Eight hits: Flat,
  generalizingMap, valuative domain, an abstract Galois-category connectedness
  lemma, and flatness characterizations; no match for the item.
- msearch.py loogle: `"IsDiscreteValuationRing", "ConnectedSpace"`:
  successful, zero hits.
- msearch.py grep: `quasi.?reductive|Prasad|special.*fib.*connect` in
  AlgebraicGeometry: successful, zero hits.
- rg of lean/WeilConjectures and lean/Sheaf with the same pattern: only
  unrelated connected-fibre arguments for sections, nodal curves, and local
  algebra. rg of the item id in WeilConjectures: no occurrence.
- rg for definitions/classes of Reductive and Unipotent found the existing
  ReductiveTorusCentralizerTerminology and SolvableGroupStructure modules;
  read and reused them. Other hits concerned linearly reductive groups and
  representation-theoretic unipotence, different notions.
- rg of dag/nodes for reductive and component definition nodes found
  def-sfb-reductive-torus-centralizer-terminology and def-wf-algebraic-components.
  The latter's upstream GroupScheme.Basic was read for onePoint and the
  identity component. No new definition node is needed.
- rg of Mathlib, WeilConjectures, Sheaf, and dag/lean_names_upstream.json for
  `quasiReductive_special_connected`: no occurrence; the declaration name is free.
- rg of literature/blueprint/latest for quasi-reductive and Prasad: no direct
  occurrence. This supporting node follows its recorded Prasad--Yu source.

Validation: scompile.py compiled the delivered module separately as sandbox and
library module, with no errors or warnings. The first compile exposed category
inference selecting Type for a coerced pullback in dimension and connectedness;
explicit `(C := Scheme.{u})` on those two pullbacks fixed it. No mathematical
hypothesis or universe equality was added. All binders and universes are explicit
and `autoImplicit` is false. The required dry run and delivery are run after this
report is written.

Required dry run passed on 2026-10-24: deliver2.py --no-push printed
"OK (dry run): commit c4cdab54437 passes the preflight and compiles; nothing pushed".
The previous stage-1 accepted-split gate does not block this stage-2 packet.

## Second reading by NX

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
