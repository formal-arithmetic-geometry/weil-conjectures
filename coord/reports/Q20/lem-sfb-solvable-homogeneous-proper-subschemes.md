## Worker report

Item: lem-sfb-solvable-homogeneous-proper-subschemes. The module
`Sheaf.AlgebraicGeometry.GroupScheme.SolvableHomogeneousProperSubschemes` states
`AlgebraicGeometry.solvable_homogeneous_proper_subschemes`, with one postponed theorem
proof and no new definitions. The accepted stage-1 statement and split are unchanged.
The previous worker's stage-1 stale-dispatch refusal does not apply to this stage-2
assignment: the current item has no Lean record and queue.tsv lists stage 2.
There is no repair note for this item.

Read the node, all ten statement dependencies and their declaration records, the full
signatures/docstrings of the notions used, and Milne Theorem 17.1 at PDF page 364
(printed p.352). Its statement agrees with this node. The node's repaired proof already
handles the disconnected-subgroup gap in Milne's original argument. No statement
correction or STATEMENT-DISPUTED flag is needed.

Hypothesis and conclusion correspondence:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- The group scheme is `G : Over (Spec (.of k))` with `[GrpObj G]`.
- Smooth, connected, affine and finite type over k are respectively
  `[Smooth G.hom]`, `[ConnectedSpace G.left]`, `[IsAffine G.left]`, and the pair
  `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`.
- Scheme-theoretic solvability is `hsolv : IsSolvableGroupScheme G`. This is the
  already landed definition of termination of the iterated smallest closed subgroup
  containing the commutator morphism. The already landed
  `def-sfb-semisimple-group-scheme` is added to stmt_deps solely to cite this notion;
  no semisimplicity hypothesis is imposed.
- The specified closed subgroup is `K : Over (Spec (.of k))`, `[GrpObj K]`,
  `i : K ⟶ G`, `[IsClosedSubgroupScheme i]`. There is no smoothness, reducedness,
  connectedness or normality assumption on K. Its group law is exactly the induced
  one because the subgroup predicate includes the homomorphism condition.
- The separated finite-type quotient k-scheme is `Q : Over (Spec (.of k))` with
  `[IsSeparated Q.hom] [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]`.
- The faithfully flat k-morphism is `q : G ⟶ Q` with `[Flat q.left]` and
  `[Surjective q.left]`, precisely flatness and topological surjectivity.
- Right invariance is `hinv`: `fst G K ≫ q` equals right multiplication followed
  by q, where right multiplication is `lift (fst G K) (snd G K ≫ i) ≫ μ[G]`.
- The displayed kernel-pair map is `e : G ⊗ K ≅ pullback q q` together with
  `he₁` and `he₂`. They prescribe its projections as g and gb respectively. Thus
  this is exactly the displayed canonical map, not an arbitrary isomorphism.
  The tensor product in the cartesian category of schemes over Spec k is the
  fibre product over k. The pullback in that over category has underlying scheme
  the scheme-theoretic pullback G ×[Q] G, with its canonical structure map to k.
- Every closed k-subscheme is quantified by `(Z : Over (Spec (.of k))) (j : Z ⟶ Q)`
  and `IsClosedImmersion j.left`. This quantifies over all presentations, without
  choosing an ideal or restricting the closed subscheme's scheme structure.
- Nonempty is `Nonempty Z.left`; proper over k is `IsProper Z.hom`.
- The first conclusion is exactly `topologicalKrullDim Z.left = 0`, retaining the
  bottom-valued dimension convention and all nilpotent structures.
- The final conclusion is `IsProper Q.hom → IsIso i`. For a specified closed
  subgroup inclusion, being an isomorphism is exactly equality with G as a closed
  subgroup scheme. It is stronger than equality of sets of rational points in
  exactly the way the node requires, and makes no choice of subgroup representative.

Dependency declarations used:

- def-weil-field: `Field`, Mathlib.Algebra.Field.Defs.
- def-weil-algebraic-closure: `IsAlgClosed`, Mathlib.FieldTheory.IsAlgClosed.Basic.
- def-sc-group-scheme: `CategoryTheory.GrpObj`, Mathlib.CategoryTheory.Monoidal.Grp,
  specialized to `Over (Spec (.of k))`, as prescribed by its lean.note.
- def-sc-group-scheme-subgroup: `AlgebraicGeometry.IsClosedSubgroupScheme`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- def-sbc-smooth-morphisms: `AlgebraicGeometry.Smooth`,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- def-weil-connected-scheme: `ConnectedSpace`, Mathlib.Topology.Connected.Basic.
- def-weil-finite-type-morphism: `LocallyOfFiniteType` and `QuasiCompact`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType and .QuasiCompact.
- def-pc-morphism-conventions is a convention record; use its specified Mathlib
  `IsSeparated`, `Flat`, `Surjective`, `IsClosedImmersion` and `IsProper`.
- def-pc-fibre-product: `CategoryTheory.Limits.pullback` and its two projections,
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback, also in the over category.
- def-kun-topological-krull-dimension: `topologicalKrullDim`,
  Mathlib.Topology.KrullDimension.
- Added landed definition dependency def-sfb-semisimple-group-scheme:
  `AlgebraicGeometry.IsSolvableGroupScheme`,
  Sheaf.AlgebraicGeometry.GroupScheme.Semisimple. Read its complete definitions of
  `groupSchemeCommutator`, `IsDerivedGroupScheme`, `GroupSchemeDerivedLength` and
  `IsSolvableGroupScheme` before reusing them.

All proof-dependency modules with recorded declarations are imported non-publicly.
This includes AffineNormalQuotientGeometry, LocallyAlgebraicGroupIdentityComponent,
ProperReducedGlobalSectionsProduct, ReductionUniversalHomeomorphism and
ZeroDimIntegralPoint, and the Mathlib/upstream modules for the recorded leaf matches:
Fpqc, Precoverage, QuasiFinite, FiniteType, Proper, Finite, GammaSpecAdjunction and
PullbackCarrier. The homogeneous quotient, nested quotient, derived subgroup, smooth
orbit, factorization and solvable normal subgroup product nodes have no recorded
Lean declarations yet; their steps and exact node identifiers remain in the proof
docstring or node proof. They are proof prerequisites, not missing statement notions.

Edge cases checked before writing:

- The trivial group (derived length zero) and K = G give a point quotient; the
  conclusions hold. K = 1 is allowed as well.
- G_a and G_m are solvable; their proper nonempty closed subschemes have dimension
  zero. Finite nonreduced thickened points are allowed, and the conclusion is about
  dimension, not an assertion that Z is itself Spec k.
- K = μ_p in G_m in characteristic p is allowed, as are disconnected finite K.
  No smoothness of K or D ∩ K is inferred or assumed in the statement.
- The empty Z is excluded by the exact nonemptiness hypothesis, consistent with its
  Krull dimension being bottom. G is nonempty by connectedness and its identity;
  a surjection q therefore prevents an empty Q.
- Q proper forces the inclusion itself to be an isomorphism, excluding a proper
  infinitesimal subgroup with the same rational points.
- No characteristic restriction and no positive-dimension condition is imposed.
  Universe u is explicit for k and schemes; there are no independent test-algebra
  universes or auto-bound variables.

Searches for an existing theorem:

1. msearch.py leanfinder, query: “Every nonempty proper closed subscheme of a
   homogeneous quotient of a smooth connected solvable affine algebraic group has
   Krull dimension zero”. Eight hits: locally Artinian of dimension at most zero,
   algebra presentations, ring quotient dimension and related commutative algebra;
   none states this theorem.
2. msearch.py loogle, query: `"IsSolvable", "AlgebraicGeometry"`. Zero hits.
3. msearch.py grep, query:
   `(solvable|IsSolvable).*(quotient|proper|homogeneous)|(quotient|proper|homogeneous).*(solvable|IsSolvable)`.
   Three hits in Mathlib/GroupTheory/Solvable.lean, all abstract-group quotient results.
4. msearch.py leansearch, query: “A proper closed subscheme of a homogeneous space
   of a connected solvable algebraic group has dimension zero”. Eight hits, including
   subscheme construction, proper restriction and affine space of dimension zero;
   none is the solvable homogeneous-space theorem.
5. rg over lean/WeilConjectures and lean/Sheaf for solvable/homogeneous/proper
   combinations and the item id. No existing theorem. The definition search found
   the landed GroupScheme.Semisimple module and its exact scheme-theoretic solvability
   predicate, which is used rather than copied. Also read SolvableGroupStructure's
   alternate normal-series interface; the derived-series interface directly matches
   the wording of this item.

Validation: both initial and final scompile.py runs passed with no errors or warnings.
The final version includes all recorded leaf proof imports and passed both sandbox
and library checks (2.7 s and 5.1 s). The deliver2.py --no-push dry run returned OK: commit 3de790e26c6 passes
the preflight and compiles; nothing pushed. This validation note is the only
subsequent report change before the final delivery wrapper repeats its checks. All files are written only
inside the assigned sandbox; no direct Git command or live-repository edit was made.

## Second reading by Q20

The dispatcher explicitly prohibits starting other agents and specifies independent
review by the maintainer. This section records the worker's own separate rereading,
not a claim of an independent reviewer. Read the full node and final theorem together:
each hypothesis and each conclusion matches the correspondence above. In particular,
the kernel-pair isomorphism is projection-preserving, K is arbitrary, properness is
over k, and equality of subgroup schemes is expressed by the actual inclusion being
an isomorphism. The only added stmt_deps entry cites an already landed definition of
an existing notion in the statement; no natural-language statement or proof changed.
The theorem proof is sorry, definitions are reused, all variables are explicit,
and no file-local notation, instance or helper definition enters the signature.
The final independent mathematical review remains the maintainer's delivery review.
