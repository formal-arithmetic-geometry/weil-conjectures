## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceDualEffectiveLineTriviality` states
`AlgebraicGeometry.AlgebraicSpace.lineModule_trivial_of_dual_effective`, with its
whole proof postponed by `sorry`. It introduces no definitions. Its source is
Stacks Project, Spaces over Fields, Tag 0DMZ,
`lemma-characterize-trivial-pic-integral`, whose statement and proof were read in
`literature/stacks-project/spaces-over-fields.tex`. The current blueprint direct-image
proof, paragraph (3), is the surrounding stability context; this supporting node's
precise source is 0DMZ. The accepted natural-language statement and split are preserved.

The previous unchanged-item refusal concerned stage 1. The current assignment is
stage 2, the queue lists this item at stage 2, and the live node has no `lean` record.
There is no repair note for this item. This delivery adds its missing statement.

Clause-by-clause correspondence:

- The field is `(k : Type u) [Field k]`; its spectrum is
  `Spec (CommRingCat.of k)`.
- An algebraic space over this spectrum is
  `(X : AlgebraicSpace (Spec (CommRingCat.of k)))`, using the recorded definition.
- The structure morphism is `f : X ⟶ schemeSpace (Over.mk (𝟙 (Spec ...)))`.
  The target is the represented base scheme. It is terminal among spaces over that
  base: on a test scheme over the base there is exactly one map to its identity
  object in `Over`. Thus specifying `f` makes the already given structure morphism
  explicit and imposes no extra geometric hypothesis or choice of action.
- Properness is `(hf : MapIsProper f)`. The definition is exactly the conjunction
  of separatedness, finite type and universal closedness requested by the node.
- Reducedness is `(hred : X.IsReduced)`: every small-etale scheme chart is reduced,
  equivalently the affine chart rings have no nonzero nilpotents.
- Nonemptiness and irreducibility together are
  `[IrreducibleSpace (Point X.obj.obj)]`. Mathlib's `IrreducibleSpace` includes
  `Nonempty`; the topology is the existing final topology of etale scheme charts.
  No geometric integrality, normality or smoothness hypothesis occurs.
- The module is `(L : X.Modules)` and its line condition is
  `(hL : X.IsLineModule L)`. This uses the small-etale structure sheaf and local
  rank-one trivializations of the dependency definition, not a tensor-invertibility
  replacement or a private definition.
- A nonzero global section of L is
  `(hs : ∃ s : SheafOfModules.unit X.structureSheaf ⟶ L, s ≠ 0)`.
  Mathlib's `SheafOfModules.unitHomEquiv L` identifies precisely these morphisms
  with compatible global sections: on each chart it evaluates the map at 1, and
  its inverse sends a section s to a ↦ a s. Zero corresponds to zero, chartwise.
- A nonzero global section of the specified internal dual Hom(L,O_X) is
  `(ht : ∃ t : L ⟶ SheafOfModules.unit X.structureSheaf, t ≠ 0)`.
  By the definition of internal sheaf Hom, its compatible global sections are
  exactly global module morphisms L → O_X. On a local basis e the section is the
  functional with coefficient t(e); evaluation against s is exactly t(s).
  Therefore this binder expresses the given dual and its canonical evaluation,
  with no arbitrary dual, tensor pairing or nondegeneracy hypothesis added.
  The local identification L tensor Hom(L,O_X) ≅ O_X is a consequence of hL,
  as in the node, rather than extra data to assume or construct in this statement.
- The conclusion is `Nonempty (L ≅ SheafOfModules.unit X.structureSheaf)`, an
  isomorphism of the same small-etale module sheaves. It asserts existence of an
  isomorphism, without requiring a chosen trivialization or a canonical section.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (read in full, including the local-affineness field).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.Modules`, `AlgebraicSpace.structureSheaf`, and
  `AlgebraicSpace.IsLineModule` (the complete construction and docstrings were read).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicSpace.MapIsProper` and its three constituent predicates.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicSpace.pointTopologicalSpace`, on the recorded `AlgebraicSpace.Point`.
- `Sheaf.AlgebraicGeometry.ReducedAlgebraicSpace`: `AlgebraicSpace.IsReduced`.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `AlgebraicSpace.schemeSpace`
  (the exact construction recorded by `def-trf-scheme-algebraic-space`).
- Mathlib's existing `SheafOfModules.unit`, `SheafOfModules.unitHomEquiv`, and
  `IrreducibleSpace`; no alternate global-section or internal-dual notion is defined.

The four existing definition nodes for properness, point topology, reducedness and
represented schemes were added to `stmt_deps`, as permitted for already landed nodes.
Their complete Lean records and relevant source declarations were read. There are no
new nodes and no dependency repairs. The two proof-only prerequisites
`lem-sfb-space-generic-line-section-injectivity` and
`lem-sfb-space-proper-connected-function-field` currently have no Lean records, so
there are no modules for them to import. Their statements were read, and the proof
plan cites them explicitly. The third proof dependency, algebraic spaces, is imported
publicly because it is also used in the statement. No proof is supplied at stage 2.

Edge cases checked before writing:

- The empty space is excluded by the nonemptiness in `IrreducibleSpace`; it is not
  accidentally admitted by `PreirreducibleSpace` alone.
- Spec K for a finite field extension K/k is allowed, including inseparable K/k.
  Global functions need not equal k. No geometric connectedness or reducedness is
  assumed; the proof docstring explicitly retains this point.
- Singular integral spaces are included: no regularity or normality binder appears.
- Disconnected reduced proper spaces and reducible connected spaces are excluded
  exactly by the integral hypothesis, not by a hidden stronger condition.
- Either zero section fails the corresponding explicit `s ≠ 0` or `t ≠ 0` condition.
  For the structure module itself, the expected identity sections satisfy the result.
- Arbitrary field characteristic and arbitrary object universe u are supported; there
  is no independent test universe that could make a chart quantifier vacuous.

Searches for an existing statement (all run for Q46 and this item):

- `msearch.py leanfinder`, query: “A line bundle on a proper integral algebraic space
  is trivial if it and its dual both have nonzero global sections”. Eight results:
  scheme nontriviality/domain and restriction statements, and ring Picard statements
  including `CommRing.Pic.mk_eq_one_iff`. None is this algebraic-space theorem.
- `msearch.py loogle`, query: `"IsInvertible", "IsIntegral"`. Zero hits.
- `msearch.py grep`, query:
  `[Tt]rivial.*[Pp]ic|[Pp]ic.*[Tt]rivial|nonzero.*[Ss]ection.*[Dd]ual`.
  Nineteen hits, concerning ring Picard groups, elliptic curves, ordinary linear
  algebra and unrelated topology; none states this result.
- `msearch.py leansearch`, query: “A line bundle on a proper integral algebraic space
  with nonzero sections in both it and its dual is trivial”. Eight hits on ordinary
  vector-space duals and topological trivializations; none is the desired statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, using the item id and
  `dual_effective|dualEffective|trivial.*[Ll]ine`, found no existing theorem.
  Concept searches found the existing line modules, point topology, properness,
  reducedness, scheme realization and section/Hom encodings which this module uses.
  The node's own recorded Mathlib searches agree with these results.

Validation: `scompile.py Q46 lem-sfb-space-dual-effective-line-triviality` compiled
this module both as a sandbox file and under its library module name, with no errors
or unexpected warnings. All declaration variables and universes are explicitly bound,
with `autoImplicit false`. No statement fault or STATEMENT-DISPUTED flag was found.

Delivery dry run: `deliver2.py Q46 lem-sfb-space-dual-effective-line-triviality
--no-push` returned OK: the three-file packet passes server preflight and compilation.

## Second reading by Q46

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
