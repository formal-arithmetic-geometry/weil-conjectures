## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.NonsolvableCentralTorusCorankThree`
states `AlgebraicGeometry.isReductive_of_nonsolvable_central_torus_corank_three`.
Its only proof is `sorry`; there are no new definitions or helper theorems.
The natural-language statement and proof are unchanged. Four already recorded
notion nodes are added to `stmt_deps`, as allowed for landed definitions:
`def-sfb-tori-multiplicative-type`, `def-sfb-semisimple-group-scheme`,
`def-sfb-reductive-torus-centralizer-terminology`, and
`def-sc-group-scheme-subgroup`. No dependency record is changed.

Hypothesis-by-hypothesis and clause-by-clause translation:

- The algebraically closed base field is `(k : Type u) [Field k] [IsAlgClosed k]`.
  `IsAlgClosed` is the precise algebraic-closedness component of the algebraic
  closure dependency's `mathlib_match`; no choice of a special base field is made.
- The two group schemes and the subgroup homomorphism are
  `(H Z : Grp (Over (Spec (.of k)))) (i : Z ⟶ H)`.
  `Grp` bundles the dependency's `GrpObj` with the underlying k-scheme.
- Smoothness, connectedness, affineness and finite type are respectively
  `[Smooth H.X.hom]`, `[ConnectedSpace H.X.left]`, `[IsAffine H.X.left]`, and
  `[LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]`. Finite type is the
  conjunction specified in the dependency record, with no stronger finiteness
  condition.
- A closed subgroup inclusion is `[IsClosedSubgroupScheme i.hom.hom]`.
- The torus clause is `hZ : ∃ r : ℕ, Nonempty (Z ≅ MultiplicativeType.splitTorus k r)`.
  This uses the existing split-torus construction, including its rank-zero unit
  object. Its multiplicative factors are the existing group scheme with points
  A-units. It states actual splitting over k, exactly as the node does; no new
  torus predicate or rank restriction is introduced. The explanatory definition
  of maximality does not occur as a hypothesis in the node or the theorem.
- Centrality is `hcentral`, universally quantifying a commutative k-algebra A,
  a Z(A)-point z, and an H(A)-point h, with conclusion
  `Commute (z ≫ i.hom.hom) h`. The test object is
  `(Spec (.of A)).asOver (Spec (.of k))`; the algebra structure supplies the
  structure map. No reducedness or field assumption is imposed on A. Since every
  extension algebra is among these A, centrality is tested after every extension.
- Codimension three is the equality `hdim` between `topologicalKrullDim H.X.left`
  and `topologicalKrullDim Z.X.left + 3`, in `WithBot ℕ∞`, using the recorded
  topological Krull dimension rather than a natural-number truncation.
- Nonsolvability is `hnonsolvable : ¬ IsSolvableGroupScheme H.X`. Opening that
  dependency shows `∃ n, GroupSchemeDerivedLength H.X n`; each successor uses
  `IsDerivedGroupScheme`, defined by the smallest closed subgroup through which
  the actual commutator morphism factors. This is exactly the node's
  scheme-theoretic derived series, including all nonreduced scheme structure.
- The conclusion is the existing `ReductiveTorusCentralizer.IsReductive H`.
  Opening this predicate gives affine finite type, smoothness, geometric
  connectedness, and triviality of every smooth connected normal unipotent closed
  subgroup after algebraic closure. Here the base is already algebraically closed:
  its algebraic closure is isomorphic over k to k, so this is equivalent to the
  node's assertion over k, with no additional conclusion. Its unipotent predicate
  is the existing `SolvableGroupStructure.IsUnipotent`: smoothness and a closed
  faithful GL representation with `(r(x)-1)^N = 0`, `N > 0`, for every point over
  every algebraically closed extension field. `IsAlgebraic U` is automatic for
  closed subgroups of affine finite-type H; the unipotence predicate itself
  contains the smoothness required in the node.
- There is no characteristic hypothesis, nor any upper or lower bound on r beyond
  r being natural. Universe u is explicitly bound and shared by the field, its
  schemes, and all test algebras; it is not an independent smaller test universe.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the fixed closure used
  inside the reductivity predicate is `AlgebraicClosure` from
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, `CategoryTheory.Grp`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsClosedSubgroupScheme` and `IsNormalSubgroupScheme`.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `AlgebraicGeometry.MultiplicativeType.splitTorus`.
- `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`:
  `AlgebraicGeometry.IsSolvableGroupScheme`, `GroupSchemeDerivedLength`,
  `IsDerivedGroupScheme`, and `groupSchemeCommutator`.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `AlgebraicGeometry.ReductiveTorusCentralizer.IsReductive`; its underlying
  `SolvableGroupStructure.IsUnipotent` and `IsAlgebraic` declarations were also read.

The statement modules publicly import the used dependencies, directly or through
these recorded definition modules. The proof-only imports are the already stated
`AffineNormalQuotientGeometry`, `SmoothConnectedDerivedSubgroup`,
`HomomorphismFactorization`, and upstream `GroupScheme.Separated`. The other six
proof nodes have no Lean record in the read repository at writing time:
`lem-sfb-solvable-normal-subgroup-products`,
`lem-sfb-group-hom-dimension-kernel-image`,
`lem-sfb-unipotent-normal-quotient-image`,
`lem-sfb-unipotent-to-multiplicative-trivial`,
`lem-sfb-connected-group-dimension-two-solvable`, and
`lem-sfb-smooth-unipotent-solvable`. They are therefore named in the complete
six-step proof docstring, and not imported as nonexistent modules. They are not
needed to elaborate the statement.

Edge cases checked before writing: r = 0 allows the trivial central torus in a
three-dimensional nonsolvable group such as SL2 or PGL2. Products SL2 × G_m^r
have the asserted codimension and illustrate arbitrary rank. G_a^3 × G_m^r is
excluded by nonsolvability; SL2 × G_a has codimension four for a rank-zero central
torus and is excluded by hdim. The trivial group and tori themselves cannot
satisfy both the dimension and nonsolvability hypotheses. Positive characteristic,
including characteristic two, remains allowed. Infinitesimal test algebras are
included in centrality; testing only k-points would have missed this clause.
Connectedness excludes the empty space; a group scheme also has its identity
section. No dimension is silently rounded or truncated.

Searches (all via the prescribed wrapper where applicable):

- `msearch.py ... leanfinder "A nonsolvable smooth connected affine algebraic group
  with a central torus of codimension three is reductive"`: eight hits about Lie
  algebra semisimplicity, including `RootPairing.GeckConstruction.instHasTrivialRadical`;
  none states this group-scheme theorem.
- `msearch.py ... leansearch` with the same query: eight abstract solvable-group
  hits, headed by `IsSolvable`; none states this theorem.
- `msearch.py ... loogle '"AlgebraicGeometry", "IsReductive"'`: zero hits.
- `msearch.py ... grep 'nonsolvable|IsReductive|IsSolvableGroupScheme'
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for `IsReductive`, `IsUnipotent`,
  `IsSolvableGroupScheme`, `IsTorus`, `central.torus`, and `nonsolvable` located the
  existing notion modules listed above, but no duplicate of the theorem.
  Searching the exact node ID in `lean/WeilConjectures` returned no match.
  Searching `dag/lean_names_upstream.json` for nonsolvable/corank-three found no
  attachment. Existing statements about central maximal tori, semisimple quotients,
  and reductivity of root centralizers have different hypotheses and conclusions.

Source checked: Conrad's PDF, printed p.88, proof of Proposition 3.1.9(1),
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf#page=88 . It contains the
central-torus/codimension-three argument. The six-step expansion follows the
unchanged DAG proof with all its named inputs. No STATEMENT-DISPUTED flag or
statement correction is needed.

## Second reading by Q152

The dispatcher explicitly prohibits starting other agents, so this is a second
reading by this worker, not a claim of independent review. The maintainer's
independent delivery review remains separate. I reopened the node and the full
source signature and checked each binder against the clause mapping above.
The derived-series predicate, the all-algebra centrality condition, the rank-zero
split-torus construction, and the geometric definition of reductivity were read
in their defining modules. In particular, the chosen conclusion's base change is
along an isomorphism because k is algebraically closed; it does not add an
unwarranted geometric hypothesis. No mismatch was found. The added statement
dependencies record existing notions rather than copying their definitions.
