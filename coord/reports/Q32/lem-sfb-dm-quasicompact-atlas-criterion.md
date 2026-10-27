## Worker report

The module `Sheaf.AlgebraicGeometry.DmQuasicompactAtlasCriterion` states
`CategoryTheory.dm_quasicompact_atlas_criterion`, with one `sorry` and no definitions.
The node's mathematical statement is unchanged. Source read in full:
`literature/stacks-project/stacks-properties.tex`, lemma-quasi-compact-stack (04YC),
statement and proof, lines 1170–1205. Its conditions (1), (2), (3), (5), restricted to
DM stacks, are the four conditions of the node.

Hypotheses and clauses, individually:

- Arbitrary base scheme: `{S : Scheme.{u}}`. No field, finite-type, separation,
  quasi-separatedness, nonemptiness, or additional property of S is assumed.
- The stack over S: `(F : BasedCategory.{v₁, w₁} (Over S))` with
  `(hF : IsDeligneMumfordModuliStack F)`. This retains the whole category fibred in
  groupoids, stack descent, representable diagonal and étale surjective atlas.
- The underlying point set is the existing `ModuliPoints F`, not objects over one
  field or isomorphism classes in a single fibre. Its arrow-generated quotient is
  identified with common-field-extension equivalence by the recorded
  `moduliPoints_eq_iff_common_field`.
- Condition (1): `CompactSpace (ModuliPoints F)`. This is quasi-compactness with no
  Hausdorff requirement. It uses the existing global `moduliPointTopologicalSpace`,
  the supremum of the coinduced topologies of residue-field point maps of all smooth
  surjective scheme atlases. For DM stacks this is the atlas topology in the node:
  étale atlases are smooth and the atlas-independence statements give the same opens.
  The existing `moduliPointIsClosed_compl_iff` gives the étale chart criterion.
- Condition (2): `∃ (A : Over S) (a : BasedFunctor
  (discreteModuli (yoneda.obj A)) F), IsAffine A.left ∧
  ModuliSpaceTest @Smooth a ∧ Function.Surjective (moduliPointMap a)`.
  `Over S` binds the structural map to S; the based functor is a map over S.
  `IsAffine A.left` means the canonical `A.left → Spec Γ(A.left)` is an isomorphism,
  equivalently A is isomorphic to a spectrum (`Scheme.isoSpec`). It does not mean
  the structural map A → S is affine.
- In (2) and (3), `ModuliSpaceTest @Smooth a` binds every scheme test and provides
  an actual algebraic-space presentation of its 2-fibre product, compatible with
  the actual projection (`HasSpaceBaseChange`), and tests `Smooth` on every étale
  scheme chart. This includes algebraic-space representability; no duplicate
  `IsRepresentableByAlgebraicSpaces a` hypothesis is needed. It imposes no
  representability by schemes.
- Condition (3) has exactly the same map conditions as (2), replacing `IsAffine`
  by `CompactSpace U.left`, the usual topological quasi-compactness of the scheme.
- Condition (4): `∃ (V : BasedCategory.{max u v₁ v₂,
  max (u + 1) w₁ w₂} (Over S)) (f : BasedFunctor V F),
  IsDeligneMumfordModuliStack V ∧ CompactSpace (ModuliPoints V) ∧
  Function.Surjective (moduliPointMap f)`.
  This requires precisely a quasi-compact DM source and a surjective morphism.
  The map need not be smooth or representable. Universe maxima permit both a lift
  of F itself and scheme-source witnesses; v₂ and w₂ remain arbitrary, so there is
  no fixed small source-category restriction.
- Every occurrence of surjectivity is literally `Function.Surjective` of the
  actual induced map on point classes, as specified in the node. There is no
  requirement of surjectivity over a fixed field without extending it.
- The conjunction of three biconditionals `(1) ↔ (2)`, `(1) ↔ (3)`, `(1) ↔ (4)`
  is exactly the assertion that all four conditions are equivalent.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsDeligneMumfordModuliStack`, `discreteModuli`,
  `HasSpaceBaseChange`, `IsRepresentableByAlgebraicSpaces`, and the underlying
  based-category and based-functor framework.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsEtale` (used by `ModuliSpaceTest`).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Sheaf.AlgebraicGeometry.StackTopologyOpenSubstacks`:
  `moduliPoints_eq_iff_common_field`, `moduliPointIsClosed_compl_iff`,
  `moduliSchemePoint_topology`, and the recorded point-image bijection.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`:
  `ModuliPoints`, `ModuliSpaceTest`, `moduliPointMap`, `ModuliPointIsClosed`.
- `Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen`:
  `moduliPointTopologicalSpace`, `moduliSchemePointMap`,
  `stackPointTopology_flat_lfp_open`.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffine`, `Scheme.isoSpec`.

The item's stmt_deps gains only two already-landed definition nodes:
`def-sfb-dm-stack-morphism-properties` (point map and representable smooth tests)
and `def-sfb-stack-point-topological-space` (the topology instance). These are
existing notions, with their recorded modules imported publicly, not new definitions.
All proof-only recorded modules and Mathlib modules are imported plainly: the
chartwise calculus, scheme-as-space embedding, affine open cover, scheme coproducts,
finite affine coproduct spectrum, affine quasi-compactness/quasi-separatedness,
open immersion étaleness, and fibre products. The five proof steps are in the theorem
docstring. No new node, dependency-module repair, or statement correction is needed.

Edge cases checked before writing:

- Empty stack and empty selected affine family: the finite product of zero chart
  rings is the zero ring, whose spectrum is empty. No Nonempty assumption prevents it.
- Affine scheme as a discrete DM stack: its identity supplies (2), including Spec 0.
- A quasi-compact non-affine scheme supplies (3); the conclusion allows choosing a
  finite union of affine chart sources without making the original scheme affine.
- A non-quasi-compact scheme has none of the compact-source surjections, since its
  scheme point space is its usual topology and continuous surjective images of
  quasi-compact spaces are quasi-compact.
- Classifying stacks with nontrivial field torsors: surjectivity is on field-point
  classes, so lifting after field extension is admitted. No fixed-field lift is added.
- Arbitrary characteristics and non-quasi-separated or non-quasi-compact bases:
  the statement uses only the base as an object of Scheme. All test schemes are in
  the base's scheme universe; independent too-small test-scheme universes are absent.

Searches actually made (2026-10-24):

- msearch.py leanfinder: `A Deligne Mumford stack is quasi compact iff it has a smooth
  surjective atlas from an affine scheme` — 8 hits, all scheme quasi-compactness or
  covering results; no DM stack theorem.
- msearch.py loogle: `CompactSpace, AlgebraicGeometry.Scheme` — 12 hits, finite
  subcovers, affine compactness and scheme-morphism quasi-compactness; no matching
  stack statement.
- msearch.py leansearch: `A Deligne Mumford stack is quasi compact if and only if it
  has an affine smooth surjective scheme atlas` — 8 scheme quasi-compactness hits;
  no matching stack theorem.
- msearch.py grep in Mathlib AlgebraicGeometry:
  `DeligneMumford|quasiCompact.*[Aa]tlas|quasi[Cc]ompact.*[Mm]oduli` — zero hits.
- rg in `lean/WeilConjectures` and `lean/Sheaf`:
  `quasiCompact.*[Aa]tlas|quasi[Cc]ompact.*[Mm]oduli|[Mm]oduli.*[Qq]uasiCompact|DeligneMumford`
  — existing DM predicates and related algebraic-stack atlas results. The closest
  `algebraic_stack_quasicompact_surjection` uses atlas-defined `IsQuasiCompactModuli`,
  an algebraic-stack source, and field-lifting surjectivity. It is not this node's
  four-way assertion for the actual topological compactness and DM source.
- rg of the item id in `lean/WeilConjectures`: zero hits.
- rg of `dm_quasicompact_atlas_criterion|DmQuasicompactAtlasCriterion` in Mathlib/project
  source search context and `dag/lean_names_upstream.json`: no existing declaration
  or module with these names before this sandbox file.

Validation: scompile.py compiled the delivered file, in module mode, both as its
sandbox module and at its library module path, with no errors or warnings (3.3 s
and 3.2 s respectively). The file explicitly binds every universe and variable and
sets `autoImplicit false`; its only proof is `by sorry`.

## Second reading by Q32

This is the dispatcher's direct-worker delivery. Its brief explicitly forbids starting
another agent and assigns the independent delivery review to the maintainer. No
independent worker reading is claimed here. I reread the node and final module side
by side: the base/DM hypothesis, the point quotient and topology, both scheme-atlas
conditions, the unrestricted point-surjective DM-source condition, and all three
biconditionals match as detailed above. In particular ModuliSpaceTest already carries
representability, IsAffine applies to the source scheme itself, and the last map has
no smoothness or representability condition. No mismatch or statement correction was
found in this self-check; independent mathematical review remains the maintainer's.
