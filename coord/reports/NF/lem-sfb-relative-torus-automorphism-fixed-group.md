## Worker report

The delivery states `AlgebraicGeometry.GroupScheme.exists_torus_automorphism_fixed_group`
in `Sheaf.AlgebraicGeometry.GroupScheme.RelativeTorusAutomorphismFixedGroup`.
Its sole theorem has proof `sorry`. The two helper definitions `fixedPoints` and
`actionBaseChange` contain their actual formulas; the new definition module
`Sheaf.AlgebraicGeometry.GroupScheme.RelativeReductive` defines relative reductivity
using the previously recorded field predicate. No node statement is corrected.
No dependency declaration is replaced.

The source was opened online: Conrad, Reductive group schemes,
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf,
Definition 2.2.1, Lemma 2.2.4 and Example 2.2.6 (printed pp.64--67),
Definition 3.1.1 (p.81), the paragraph before Remark 3.1.5 (p.83), and
Corollary 3.3.5 proof (p.101). In particular, the latter proof explicitly obtains
smoothness, connected geometric fibres and reductivity by the semidirect product.
The theorem's docstring contains all eleven DAG proof steps, with their dependency
identifiers. The arbitrary-base assertion assembles the cited relative centralizer
lemma, fppf splitting and fpqc descent, as the node's proof specifies.

Clause-by-clause statement correspondence:

- The scheme S is `{S : Scheme.{u}}`, unrestricted. Both H and R are
  `Grp (Over S)`: the existing internal group object supplies multiplication,
  identity and inverse, and a morphism `i : F ⟶ H` preserves the group law.
- H is smooth: `[Smooth H.X.hom]`. It is affine over S:
  `[IsAffineHom H.X.hom]`, which does not require that S or H be absolutely affine.
- H is of finite presentation: `[LocallyOfFinitePresentation H.X.hom]`,
  `[QuasiCompact H.X.hom]` and `[QuasiSeparated H.X.hom]`, exactly the recorded
  scheme convention. The redundant consequences of affineness are displayed as
  components of the requested finite-presentation condition.
- Connected geometric fibres: `[GeometricallyConnected H.X.hom]`. Mathlib defines
  this by connectedness of pullbacks to all fields. Testing only algebraically
  closed fields is equivalent, by descent of connectedness along the surjective
  algebraic-closure extension. ConnectedSpace includes nonemptiness.
- R is a torus: `hR : IsRelativeTorus R.X` uses the existing arbitrary-base
  definition, an fppf cover and isomorphisms of group-valued functors with finite
  powers of units of global functions. No embedding of R in H is supplied.
- The action is `[ModObj R.X H.X]`, an actual action morphism with unit and
  associativity diagrams. The hypothesis `ha` says on every test scheme that
  `r • (x * y) = (r • x) * (r • y)`. Since R is a group, r inverse provides
  the inverse action, so this is precisely action by group automorphisms;
  identity and inverse preservation follow from multiplicativity in groups.
- The node's definition of H^R(U) is `fixedPoints γ[R.X, H.X] U`.
  It quantifies over every `V : Over S`, `f : V ⟶ U`, `r : V ⟶ R.X` and
  demands `lift r (f ≫ x) ≫ a = f ≫ x`. Morphisms V to U in Over S are exactly
  all U-schemes; this tests the full group scheme, including nilpotents.
- Representability is the existential `F : Grp (Over S)` and `i : F ⟶ H`,
  together with equality of the image of `Hom(U,F)` with that fixed subset for
  every U. `IsClosedImmersion i.hom.hom.left` gives uniqueness of the lift,
  so this is the represented subfunctor, not just a surjection onto its points.
  Naturality follows from the displayed definition and the given inclusion.
- The first output predicates give a closed subgroup, smooth affine over S,
  of finite presentation (LFP, QC, QS) and connected geometric fibres.
- Arbitrary base change: for every `T : Scheme.{u}`, every `f : T ⟶ S`,
  and every `U : Over T`, the actual group pullback
  `(Over.pullback f).mapGrp.obj F`, with pulled-back inclusion
  `(Over.pullback f).mapGrp.map i`, represents the fixed subset for the
  canonical base-changed action. `actionBaseChange` is exactly
  `Functor.LaxMonoidal.μ (Over.pullback f) R H ≫ (Over.pullback f).map a`.
  The monoidal comparison is the canonical product/pullback comparison, not
  an arbitrary action or map. Hence the compatibility is with the inclusion
  into H_T and is canonical, including for identity and nonflat f.
- Reductivity is the final implication `IsReductive H → IsReductive F`,
  using the new relative definition. That definition includes smooth affine
  finite presentation and for every algebraically closed k and Spec k to S
  the previously recorded `ReductiveTorusCentralizer.IsReductive` of the
  pulled-back group. The latter uses the existing affine finite-type,
  connectedness, normal closed subgroup and faithful-matrix unipotence notions.
- The opening multiplicative-type and G_m descriptions fix terminology, not
  extra hypotheses. Relative tori use the existing group functor of units;
  `ringDiagonalizableGroup` is the recorded Spec of the actual group algebra
  with canonical Hopf structure and is imported, without a private duplicate.

Dependency declarations read and used:

| Node / notion | Module | Declaration |
| --- | --- | --- |
| schemes and morphisms | Mathlib.AlgebraicGeometry.Scheme | AlgebraicGeometry.Scheme, Scheme.Hom |
| diagonalizable group over a ring | Sheaf.AlgebraicGeometry.RingDiagonalizableGroup | AlgebraicGeometry.ringDiagonalizableGroup, ringDiagonalizableGroupMap |
| fppf covers | Mathlib.AlgebraicGeometry.Sites.Fpqc | Scheme.fppfPrecoverage, Scheme.fppfTopology |
| smoothness | Mathlib.AlgebraicGeometry.Morphisms.Smooth | AlgebraicGeometry.Smooth |
| connectedness | Mathlib.Topology.Connected.Basic | ConnectedSpace |
| finite-presentation conventions | Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation; Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated | LocallyOfFinitePresentation, QuasiCompact, QuasiSeparated |
| relative torus | Sheaf.AlgebraicGeometry.RelativeTorus | AlgebraicGeometry.IsRelativeTorus, relativeSplitTorusFunctor |
| group object | Mathlib.CategoryTheory.Monoidal.Grp | CategoryTheory.Grp, GrpObj |
| group base change | Mathlib.CategoryTheory.Monoidal.Cartesian.Over; WeilConjectures.AlgebraicGeometry.BaseChangeConventions | Over.pullback, Functor.mapGrp |
| field reductivity | Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology | AlgebraicGeometry.ReductiveTorusCentralizer.IsReductive |
| action on represented points | Mathlib.CategoryTheory.Monoidal.Cartesian.Mod | ModObj, CategoryTheory.Hom.mulAction |
| connected geometric fibres | Mathlib.AlgebraicGeometry.Geometrically.Connected | AlgebraicGeometry.GeometricallyConnected |

`def-weil-pbc-scheme-conventions` is explicitly a convention-only node with
no declaration. Its specified Mathlib notions are used directly. Every recorded
proof dependency that has a module is imported privately, including affine fpqc
descent, morphism descent, closed-immersion descent, smooth base change, gluing,
Nullstellensatz and connected-normal-subgroup reductivity. The currently unstated
centralizer, unipotent radical and field fixed-subgroup proof nodes have no
module to import; this does not affect their names in the eleven-step proof plan.

Edge cases checked before writing:

- R of rank zero and the trivial action: the fixed set is all of H(U), and
  F = H with identity inclusion satisfies the representability interpretation.
- A nonfaithful action is admitted: neither a monomorphism from R nor injectivity
  of an action representation occurs anywhere.
- Empty S: Over S contains only empty schemes, there are no geometric points,
  the relative-torus cover may be empty, and the claim has no nonempty-base
  hypothesis. Empty geometric fibres over an existing geometric point are
  excluded by ConnectedSpace, as required for group fibres with identity.
- Nonreduced test schemes and nonflat/nonreduced base changes: V and f have
  no property predicates. All fixedness quantifiers persist after base change.
- Disconnected bases and varying torus ranks: IsRelativeTorus has an independent
  finite rank on each cover member, with no global constant-rank requirement.
- Characteristic zero and positive characteristic: no characteristic binder or
  reducedness replacement appears. Smooth unipotent subgroups use the recorded
  faithful geometric matrix representation, with no characteristic restriction.
- Universes: S, T, test schemes and geometric-point fields all use the same u,
  following the recorded size convention. There is no independent smaller
  test-algebra universe making a universal condition vacuous. All variables
  and u are bound explicitly with autoImplicit false.

Searches for an existing statement and notions:

- msearch leanfinder: "A torus acting by automorphisms on a smooth connected
  affine group scheme has a smooth connected fixed subgroup" returned eight
  abstract Galois-category results, not this statement.
- msearch loogle: `"torus", "fixed"` returned zero hits.
- msearch grep: `IsTorus|IsReductive|FixedSubgroup` in AlgebraicGeometry
  returned zero hits.
- rg in WeilConjectures for this node identifier returned no hit. Searches of
  WeilConjectures, Sheaf and Mathlib for torus, reductivity, automorphism actions
  and fixed schemes found the field-only ToriMultiplicativeType and
  ReductiveTorusCentralizerTerminology, plus the usable relative-torus node.
- `SchemeActionFixedIdeal` handles a discrete external automorphism group and
  is not the scheme-group action subfunctor here. `FixedScheme` handles the
  equalizer of two morphisms in a correspondence, not this fixed subfunctor.
  The existing field-only ActsByGroupAutomorphisms is rendered inline over S,
  without defining another predicate for the same field notion.
- DAG definition-node scans and blueprint_refs searches were used before
  proposing the new relative definition. The complete new-node search outputs
  are included in its mathlib_searches as returned by msearch.

No STATEMENT-DISPUTED flag or unresolved node fault remains. The original node's
statement, proof and proof dependencies are unchanged. Its stmt_deps gains the
existing relative-torus node and the new relative-reductive-group node.

## New nodes

`def-sfb-relative-reductive-group` supplies the missing arbitrary-base reductivity
predicate in `Sheaf.AlgebraicGeometry.GroupScheme.RelativeReductive`.
Source: Conrad Definition 3.1.1, printed p.81, with the finite-presentation
convention already specified by the item. It defines smooth affine finite
presentation plus field reductivity of every geometric fibre, using the recorded
field predicate rather than a copy of matrix-unipotence or subgroup notions.
LeanSearch, LeanFinder and Mathlib grep found no such arbitrary-base predicate;
project and DAG scans found only the field definition and special pinned-root
realizations. The existing relative-torus node is cited, so no torus definition
node or module is delivered. The new definition has real data and no sorry.

Validation: both delivered modules compile separately through scompile.py against
the published server library and the private dependency overlay. The theorem is
left with its requested sorry proof; no other theorem or axiom is introduced.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
