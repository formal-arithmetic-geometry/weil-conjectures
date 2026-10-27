## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SmoothSubgroupFullTangent` states
`AlgebraicGeometry.isIso_of_smooth_closedSubgroup_surjective_tangent`, with its proof
postponed by `sorry`. No definition or other theorem is introduced. The node changes
only in `lean`; its mathematical statement and dependency lists are unchanged.

Read the complete item, its seven statement dependencies and their Lean records, and
their defining declarations. Read Milne, Algebraic Groups (2017), Proposition 10.15,
printed pp.190-191, using pdftotext on the local PDF. Milne states Lie(H)=Lie(G), H smooth,
G connected implies H=G, and specifically points out the need for smoothness of H and
connectedness of G. For a closed immersion the differential is injective, so the node's
surjectivity formulation is equivalent. The file documents all eight accepted proof
steps with their DAG references. Proof-only imports include the recorded modules of
already stated proof dependencies. The smoothness-at-identity and regular-separable
neighbourhood nodes do not yet have Lean records and cannot be imported.

Hypothesis and conclusion correspondence:

- Any field k: `(k : Type u) [Field k]`, with explicitly declared universe `u`.
- k-group schemes A and B: `(A B : Over (Spec (.of k))) [GrpObj A] [GrpObj B]`.
  The over-category records their structure maps and k-linearity of morphisms.
- A affine: `[IsAffine A.left]`.
- A finite type: `[LocallyOfFiniteType A.hom] [QuasiCompact A.hom]`, exactly the
  conjunction specified by def-weil-finite-type-morphism.
- A connected in its underlying topology: `[ConnectedSpace A.left]`.
- The closed subgroup embedding: `(j : B ⟶ A) [IsClosedSubgroupScheme j]`.
  This existing class supplies the subgroup homomorphism, injectivity on algebra-valued
  points, and closed immersion of `j.left`. No replacement predicate is introduced.
- B smooth over k: `[Smooth B.hom]`.
- Lie(J) is the tangent space at the identity: the source of the differential is
  `schemeTangentSpace k B.left B.hom (GrpObj.onePoint B)`. Its target is the same
  recorded tangent-space construction on A at `j.left (GrpObj.onePoint B)`. This is
  the identity of A, since a group homomorphism preserves the unit section. Leaving
  the target indexed by this definitionally supplied image avoids an unnecessary cast.
- Surjective differential: `hsurj` asserts `Function.Surjective (schemeTangentMap ... he)`.
  The accompanying existential `he` is a bijectivity witness for the induced residue-field
  map, required by the recorded canonical differential's type. Both identity points
  are k-rational, so this map is necessarily an isomorphism; the witness imposes no
  restriction on the groups or field. Proof irrelevance makes the choice irrelevant.
  This existential belongs to the surjectivity premise rather than being an additional
  externally supplied map or identification. The map is the canonical postcomposition
  differential, never an arbitrary linear map.
- j is an isomorphism of k-group schemes: `IsIso j`, in `Over (Spec (.of k))`.
  Since j is already a group homomorphism, its categorical inverse commutes with the
  group operations by cancellation; thus this says exactly group-scheme isomorphism.
- No characteristic or perfectness restriction, no smoothness hypothesis on A, and
  no connectedness or separate finite-type hypothesis on B occur in the signature.

Dependency declarations used:

- def-weil-field: `Field` (Mathlib algebra field definitions).
- def-sc-group-scheme: `CategoryTheory.GrpObj`, in
  `Mathlib.CategoryTheory.Monoidal.Grp`, specialized to the scheme over-category.
- def-weil-finite-type-morphism: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, in Mathlib's morphism modules of those names.
- def-weil-connected-scheme: `ConnectedSpace`, `Mathlib.Topology.Connected.Basic`.
- def-sc-group-scheme-subgroup: `AlgebraicGeometry.IsClosedSubgroupScheme`,
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` (including its inherited
  `IsSubgroupScheme` and `IsMonHom` interfaces).
- def-sbc-smooth-morphisms: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- def-sc-scheme-tangent-space: `AlgebraicGeometry.schemeTangentSpace`, its canonical
  module instances, and `AlgebraicGeometry.schemeTangentMap`, all in
  `WeilConjectures.AlgebraicGeometry.SchemeTangentSpace`.
- The identity point is the existing `AlgebraicGeometry.GrpObj.onePoint` from
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Basic`, part of the group-scheme
  interface. It is the image of the unique point of Spec k under the unit section.

Edge cases checked before writing: the trivial group and zero-dimensional connected
ambient group are included; no nonzero tangent dimension is assumed. A group scheme
has a rational identity, so the empty scheme is not a missing case. Imperfect fields
and fields of positive characteristic are included. B may be disconnected. The usual
alpha_p inside G_a counterexample fails the smoothness hypothesis on B; a proper
identity component of a disconnected ambient group fails the connectedness hypothesis
on A. Surjectivity need not be asserted to be bijectivity: injectivity follows from
the closed subgroup condition. The residue-field witness is automatic at both rational
identities, over arbitrary k. There is no field extension or algebraic closure in the
signature.

Searches for an existing statement:

- msearch leanfinder, query `A smooth closed subgroup with surjective tangent map equals
  a connected algebraic group over any field`: eight hits about manifold Lie groups,
  with no scheme-theoretic subgroup criterion.
- msearch leansearch, query `smooth closed subgroup with surjective tangent space equals
  connected algebraic group`: eight hits, mainly topological ClosedSubgroup and smooth
  algebra results, none equal to the node.
- msearch loogle, query `AlgebraicGeometry.IsClosedSubgroupScheme, CategoryTheory.IsIso`:
  no hits; the project-specific identifier is unknown to the remote Mathlib index.
- msearch grep, query `(Lie|tangent).*(subgroup|closedImmersion)|same.*Lie` in
  Mathlib/AlgebraicGeometry: one unrelated Sites/Affine module-docstring hit.
- rg over both lean/WeilConjectures and lean/Sheaf for `full_tangent`, `smooth_subgroup`,
  `same_lie`, `surjective.*differential`, `differential.*surjective`: no existing exact
  theorem. Broader Lie/subgroup searches found general-linear and specialized
  characteristic-zero results, not this arbitrary-field general group-scheme theorem.
- rg for the item id in lean/WeilConjectures: no declaration. Read the canonical
  SchemeTangentSpace API, GroupScheme.Defs, GroupScheme.Basic, and the Lie differential
  and tangent equivalence interfaces to avoid duplicate definitions.

No statement correction, new node, unusable dependency record or mathematical dispute
was found. Only the theorem proof is postponed, as required for stage 2.

## Second reading by Q116

A separate reading pass compared the final node copy and module clause by clause.
The dispatch explicitly forbids starting another agent; this is a second pass by the
same worker, not a claimed independent worker review. The maintainer supplies the
independent delivery review.

Checked field, both group objects, A affine and finite type, connectedness of A, the
closed subgroup j, and smoothness only of B against the signature. Checked the actual
`schemeTangentMap` signature: `j.w` is its over-base equality, `GrpObj.onePoint B`
is its base point, and the existential witness is bijectivity of exactly its induced
residue-field map. The codomain tangent point is the image identity and hence the
ambient identity. Checked that `IsIso j` is in the over-category and its inverse is a
group homomorphism because j is one. No hypotheses, conclusions or definitions differ
from the node. No mismatch or edit arose in this pass. Universes and variables are
explicit; there are no statement lets, local notation, local instances or private
helpers, and every file line is at most 100 characters.
