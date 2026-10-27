## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.LunaBorelAttractionCharts` states
`AlgebraicGeometry.exists_luna_borel_attraction_chart`, with its sole proof `sorry`.
No definitions or extra theorem obligations are introduced. The node's mathematical
statement and proof are unchanged.

Source read: Milne, Algebraic Groups (2017), Theorem 17.65 and its complete proof,
printed p.374, and the following argument on p.375. The final paragraph of the proof
uses only containment in a Borel through T to preserve the dual line. Thus the
containment-only V formulation of the node follows by the same argument; it does not
require normality in G or assume Chevalley's equality.

Hypotheses and clauses, matched to Lean:

- The algebraically closed base field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- Affine group schemes of finite type are bundled `Grp (Over (Spec (.of k)))`
  with `SolvableGroupStructure.IsAlgebraic`: `hG` for G and `hValg` for V.
  T is a closed torus through `hT`, so its algebraic-group properties are inherent
  in the recorded torus construction. No reductivity is assumed of G.
- G smooth connected is `[Smooth G.X.hom] [ConnectedSpace G.X.left]`.
- T is a maximal torus subgroup through `iT : T ⟶ G` and
  `hT : ReductiveTorusCentralizer.IsMaximalTorus iT`. This is exactly closed
  inclusion, torus, and absence of a strictly larger torus subgroup.
- X and its action are `X : Mod (Over (Spec (.of k))) G.X`; this bundles the
  actual scheme action and its unit and multiplication laws. Borel subgroups are
  precisely the subobjects in the domain of `b`, with a group-structure witness
  and the dependency's `IsBorelGroupScheme` predicate. This is maximal smooth
  connected scheme-solvable closed subgroup, not an abstract rational-point group.
- The flag presentation is arbitrary `X,b` satisfying `hflag`, whose conjunction
  is copied verbatim from the conclusion of `exists_general_borel_flag_variety`.
  In order: nonempty; smooth; connected; projective; locally finite type;
  quasi-compact; proper; separated; G(k)-transitivity; conjugation compatibility
  tested over all commutative k-algebras; exact scheme stabilizers over all such
  algebras; containment of any torus in a Borel; scheme-theoretic torus-fixed
  point characterization. These are the properties of the named flag variety
  supplied by the statement dependency, not additional restrictions on G, T or V.
  In particular the statement makes no choice of X from an unproved existence.
  Applying the dependency theorem provides exactly this X,b,hflag interface.
- V is a closed subgroup through `iV` and `hVclosed`. Its smooth faithful-matrix
  unipotence is `hVuni : SolvableGroupStructure.IsUnipotent V`, which includes
  smoothness. Its connectedness is `[ConnectedSpace V.X.left]`.
- V lies in every Borel through T: `hV` quantifies over every Borel subobject C.
  Factorization of `iT.hom.hom` through `C.val.arrow` implies factorization of
  `iV.hom.hom` through that same inclusion. This is subgroup-scheme containment,
  including nonreduced test algebras, rather than rational-point containment.
- The Borel B containing T is the Borel-labelled subtype binder `B` and the
  factorization hypothesis `hTB`.
- The affine open subscheme is `∃ U : X.X.left.Opens, IsAffineOpen U ∧ ...`.
  Its canonical open immersion is the existing `U.ι`; `IsAffineOpen U` is by
  definition affineness of `U.toScheme`.
- The displayed equality of rational-point sets is the first conjunct after
  affineness: for every Borel B', the point underlying `b B'` belongs to U iff
  the point underlying `b B` belongs to the Zariski `closure` of the `Set.range`
  of `t ↦ (t ≫ iT.hom.hom) • b B'`, evaluated at `IsLocalRing.closedPoint k`.
  The equivalence b ranges over all rational points, so no points are omitted.
  Crucially the closure lives in the underlying space of the scheme X, not in
  a topology imposed on the set of rational points.
- Restriction of the V-action is the next existential morphism `a` from
  `V.X ⊗ Over.mk (U.ι ≫ X.X.hom)` to that same open k-scheme. Its composite
  with `Over.homMk U.ι` is exactly the original G-action restricted via iV.
  This equation pins down the canonical restriction, not an arbitrary action.
  The open immersion is mono; its cancellation gives the action laws from X's
  action laws, so this is precisely a restricted action.
- The final conjunct quantifies over every `v : 𝟙_ (...) ⟶ V.X`. The actual
  scheme self-map of X is the action composed with the pair consisting of the
  constant image of v in G and the identity of X. `Set.image` of the complement
  of U under its underlying point map is exactly that complement. This includes
  nonclosed topological points, and is full invariance rather than one inclusion.
- There is no normality hypothesis or conclusion for V.

Dependency interfaces inspected and reused:

- Mathlib.Algebra.Field.Defs: `Field`; Mathlib's `IsAlgClosed` convention.
- Mathlib.CategoryTheory.Monoidal.Grp: `GrpObj` and `Grp`;
  Mathlib.CategoryTheory.Monoidal.Cartesian.Mod: the internal module/action
  and the induced action on morphisms, with `Hom.smul_def`.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Defs:
  `IsSubgroupScheme`, `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`.
  Only the closed-subgroup interface is needed in this signature.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: `LocallyOfFiniteType`;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: `QuasiCompact`.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth`;
  Mathlib.Topology.Connected.Basic: `ConnectedSpace`, including nonemptiness.
- Sheaf.AlgebraicGeometry.SolvableGroupStructure:
  `IsAlgebraic`, `IsTorus`, `IsUnipotent`, `IsSolvable` (read their full bodies).
- Sheaf.AlgebraicGeometry.GroupScheme.GeneralBorelFlagVariety:
  `exists_general_borel_flag_variety`, full signature and docstring read;
  Sheaf.AlgebraicGeometry.GroupScheme.Borel: `IsBorelGroupScheme`.
- Mathlib.AlgebraicGeometry.OpenImmersion: `IsOpenImmersion`;
  Mathlib.AlgebraicGeometry.Restrict: `Scheme.Opens.toScheme`, `Scheme.Opens.ι`;
  Mathlib.AlgebraicGeometry.AffineScheme: `IsAffineOpen`.
- Mathlib.AlgebraicGeometry.Scheme: `Spec`, `Spec.map`.
- Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology:
  `ReductiveTorusCentralizer.IsMaximalTorus`. The existing definition node
  `def-sfb-reductive-torus-centralizer-terminology` is added to stmt_deps to
  record use of this already landed maximal-torus predicate. This is not a new
  node or a redefinition, and does not assume G reductive.

The stated proof dependencies' recorded modules are imported without `public`.
For the Nullstellensatz proof dependency, its declaration names were located in
`WeilConjectures.Mathlib.RingTheory.Nullstellensatz`. The five proof dependencies
without recorded modules are not invented or replaced: general-flag-isolated-linear-action,
smooth-group-rational-point-subspace-test, torus-extreme-weight-affine-chart,
torus-normalizer-borel-transitivity, proper-homogeneous-torus-borel-stabilizer.
They are named explicitly in the proof docstring for stage 3.

Edge cases checked before writing: G trivial or solvable (the flag variety is a point
and U is all of X); maximal torus rank zero (no positive-rank restriction); V trivial;
any characteristic; zero/nonreduced test algebras in the inherited flag stabilizer
and containment clauses; empty complement (image equality remains meaningful).
The algebraic-group and connected hypotheses exclude an empty G. The flag
presentation includes nonemptiness, so there is no empty-X loophole. Only the
common universe u is used, as in the existing group/flag interfaces; no independent
smaller universe makes algebra tests vacuous.

Searches performed for this item:

- msearch leanfinder, query "Affine open attraction charts of a maximal torus on
  the flag variety stable under a common unipotent subgroup": eight hits, including
  MulAction.IwasawaStructure.is_generator, Subgroup.IsRegularAtInfty and unrelated
  Lie/root-system facts; none states this scheme-theoretic result.
- msearch loogle, query "AlgebraicGeometry.IsAffineOpen, closure": zero hits.
- msearch grep, query "Luna|attraction|attracting|BorelGroupScheme" in
  AlgebraicGeometry: zero Mathlib hits.
- msearch leansearch, query "Luna theorem affine open flag variety torus orbit
  closure": eight hits concerning ordinary affine opens, including IsAffineOpen
  and exists_isAffineOpen_mem_and_subset; none is the attraction assertion.
- rg of the project Sheaf and WeilConjectures algebraic-geometry sources for
  IsMaximalTorus, IsBorelGroupScheme, attraction/attracting, Luna and luna_borel:
  found the reused Borel/maximal-torus definitions and Bruhat-cell theorem modules,
  which concern reductive groups and different cells. No existing exact statement.
  Search for this node id in WeilConjectures produced no hit.
- DAG search for the maximal-torus predicate/module found the existing definition
  node cited above, so no helper definition node is created.

The file compiles cleanly with scompile.py under the 60-second limit, both as the
sandbox module and at its intended library module path (2.9 seconds each).
All universes and variables are bound, `autoImplicit` is false, and the only
postponed proof is the named theorem. No statement dispute or correction.

## Second reading by Q74

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
