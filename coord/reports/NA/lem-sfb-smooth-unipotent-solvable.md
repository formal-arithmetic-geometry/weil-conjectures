## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SmoothUnipotentSolvable` states
`AlgebraicGeometry.smooth_unipotent_isSolvable`. Its only proof is `sorry`.
It introduces no definitions, helper theorems, new nodes or dependency modules.
The item statement, proof and proof dependencies are unchanged. Its statement
dependencies gain the already landed `def-sfb-solvable-group-structure`, whose
recorded declarations supply exactly the two notions used here. The rest of the
node changes only in `lean`. No statement correction or disputed statement.

Source actually read: the local PDF of Milne, Algebraic Groups (2017),
Theorem 14.5, Corollary 14.12 (printed p.283), Proposition 14.21 and its proof
(printed pp.284--285). Proposition 14.21 explicitly concludes nilpotence and
solvability without perfectness or connectedness. Corollary 14.12 identifies
smooth geometric-point unipotence with the representation-theoretic notion;
the following warning about nonsmooth mu_p explains why smoothness is retained.
The module docstring gives all three accepted DAG proof steps, including the
matrix ideal calculation over arbitrary, possibly nonreduced, test algebras and
the fppf descent argument for commutativity of the represented quotients.

Hypotheses and conclusion, clause by clause:

- A field k: `{k : Type u} [Field k]`, with `universe u` declared explicitly.
- A group scheme over k: `U : Grp (Over (Spec (.of k)))`. `Grp` bundles a group
  object, with multiplication, inverse, identity and the group diagrams.
- Affine and finite type: `hU : SolvableGroupStructure.IsAlgebraic U`, whose actual
  definition is `IsAffine U.X.left ∧ LocallyOfFiniteType U.X.hom ∧
  QuasiCompact U.X.hom`. This is the original node's affine finite-type condition,
  without an additional separatedness, dimension or reducedness hypothesis.
- Smooth unipotence: `hu : SolvableGroupStructure.IsUnipotent U`. Its first
  conjunct is `Smooth U.X.hom`; thus no separate smoothness assumption is lost.
  Its remaining data assert a finite-dimensional representation into GL_n with
  `IsClosedSubgroupScheme r`, hence a faithful group-scheme homomorphism.
  For every point over every algebraically closed extension, it requires
  `∃ N : ℕ, 0 < N ∧ (matrix - 1) ^ N = 0`, exactly the stated unipotence equation.
  Testing on all algebraically closed extensions instead of one algebraic closure
  gives the same notion here: in finite dimension nilpotence has a uniform
  exponent n, so the condition is polynomial vanishing on the smooth, hence
  geometrically reduced, affine finite-type group; vanishing on algebraic-closure
  points is equivalent to vanishing of these regular functions and persists
  after every extension. This is Milne 14.12 and its proof using density and 14.9.
  Faithfulness as a closed immersion is the standard affine finite-type
  group-scheme meaning, not faithfulness only on k-rational points.
- The conclusion is `SolvableGroupStructure.IsSolvable U`, the landed finite
  closed-subnormal-series definition, not abstract solvability of U(k).
  It quantifies over a natural n and `S : Fin (n+1) → Grp (Over (Spec (.of k)))`,
  identifies the initial term with U and the last with `Grp.trivial _`, and for
  each adjacent pair requires a closed normal subgroup inclusion and that
  `x*y*x⁻¹*y⁻¹` factor through it for EVERY commutative k-algebra R.
  This is commutativity of its group-scheme quotient: the affine normal quotient
  theorem represents the fppf quotient; local lifts of two quotient points have
  trivial commutator in the quotient, and sheaf descent gives commutativity.
  Conversely, quotient commutativity puts every commutator in its kernel.
  All S are affine finite type because successive inclusions are closed and
  S(0) is isomorphic to the affine finite-type U. Thus the series has exactly
  the closed subgroup schemes and commutative group-scheme quotients requested.
- No perfectness or characteristic instance is present. Connectedness and
  geometric connectedness in the node's opening conventions are not hypotheses
  of its final assertion; neither is assumed by the Lean statement.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, defined in `Mathlib.Algebra.Field.Defs`.
- `def-sc-group-scheme`: `CategoryTheory.Grp`, `CategoryTheory.GrpObj` and the
  group-object convention in `Mathlib.CategoryTheory.Monoidal.Grp` and
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`. The full group-object
  signature and its multiplication/inverse/unit docstrings were read.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, read in their Mathlib Morphisms modules.
- `def-sc-group-scheme-subgroup`: `AlgebraicGeometry.IsSubgroupScheme`,
  `AlgebraicGeometry.IsClosedSubgroupScheme`, and
  `AlgebraicGeometry.IsNormalSubgroupScheme` from
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`; their signatures and
  docstrings explicitly quantify over all commutative test algebras.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth` from
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, read in full.
- `def-weil-connected-scheme`: `ConnectedSpace` in
  `Mathlib.Topology.Connected.Basic` was read; it includes nonemptiness, but is
  not needed in the theorem since connectedness is not assumed.
- Added existing statement dependency `def-sfb-solvable-group-structure`:
  `AlgebraicGeometry.SolvableGroupStructure.IsAlgebraic`, `IsUnipotent`,
  `IsSolvable`, in `Sheaf.AlgebraicGeometry.SolvableGroupStructure`.
  The entire source module and node statement/record were read. All are real
  Prop definitions; no chosen data or theorem with sorry is used as definition data.
  Importing this public module exposes the preceding basic definitions too.
- Proof dependency `lem-sfb-affine-normal-quotient-geometry`:
  `AlgebraicGeometry.affine_normal_quotient_geometry` and
  `AlgebraicGeometry.IsFppfGroupQuotient`, in
  `Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`, imported
  without `public`. Its full signature and proof-plan docstring were read.
- The other stated proof dependencies, closed immersions and subgroup/group
  schemes, are already exposed by the public terminology import. The geometric
  unipotence/unitriangular embedding node has no Lean record on the read base;
  it is cited in the proof docstring and needs no statement dependency or new
  theorem in this delivery, since its result is used only in the future proof.

Edge cases checked before writing:

- The trivial group is included: the definition permits a length-zero series.
  A zero-dimensional representation forces triviality; allowing n=0 in the
  reused matrix definition adds no nontrivial group and excludes no case.
- G_a and upper unitriangular groups over arbitrary fields have the indicated
  finite matrix filtration and hence the required series.
- Smooth disconnected constant p-groups in characteristic p remain included;
  they must not be excluded by a connectedness assumption.
- Imperfect-field smooth forms of G_a remain included. No additive splitting
  or perfectness is required of U or the series factors.
- Nonreduced test algebras are still quantified over in the conclusion, and
  intermediate closed subgroup schemes need not be smooth or connected.
- mu_p and alpha_p in characteristic p are excluded by smoothness. In particular,
  the singleton geometric-point set of mu_p cannot make it satisfy the hypothesis.
- G_m is not geometrically unipotent and is outside the hypothesis.
- An empty scheme is not a group scheme over a field: the identity section
  Spec k → U makes it nonempty. No extra nonemptiness assumption is imposed.
- The field and test algebras use the same arbitrary universe u, following the
  recorded group-scheme API; no independent smaller test universe is introduced.

Searches actually performed:

1. `msearch.py ... leanfinder "Every smooth unipotent affine algebraic group is
   solvable as a group scheme"`: eight hits, including `IsNilpotent.to_isSolvable`,
   `CommGroup.isSolvable`, `IsSolvable`, `isSolvable_def`, `IsSolvable.solvable`,
   `isSolvable_of_subsingleton`, `isSolvable_of_top_eq_bot`, and
   `LieAlgebra.ofAbelianIsSolvable`; none is the group-scheme theorem.
2. `msearch.py ... loogle "IsUnipotent, IsSolvable"`: zero hits, with unknown
   identifier IsUnipotent reported. This was a negative name search, not evidence
   against the already found project's terminology.
3. `msearch.py ... grep "unipotent|solvable" AlgebraicGeometry`: zero Mathlib hits.
4. `msearch.py ... leansearch` with the same full theorem query: eight hits,
   abstract group solvability, Lie algebra solvability, and smooth implies
   locally finite presentation; no matching group-scheme theorem.
5. `rg -n` for unipotent/solvable/representation in the project's
   `WeilConjectures/AlgebraicGeometry/GroupScheme` and `Sheaf` sources found the
   existing `SolvableGroupStructure` module and sibling group-structure theorems.
   Its actual definitions were read and reused. Searches in upstream
   WeilConjectures for the item id and unipotent/solvable found no matching theorem
   (one unrelated derived-category unipotent matrix construction).
6. `rg -n` for `smooth_unipotent.*solvable`, `isSolvable_of_isUnipotent` and
   `isSolvable_of_unipotent` in Sheaf and WeilConjectures found no declaration.
   A further search for theorem names with both solvable and unipotent found
   only the distinct perfect-field solvable-group decomposition theorem.
7. The DAG definition search found `def-sfb-solvable-group-structure`, already
   carrying precisely the finite series and geometric matrix unipotence notions.
   The different derived-series encoding in `def-sfb-semisimple-group-scheme`
   was read but is not copied or substituted for the series predicate here.

Validation: the delivered file is compiled with the prescribed `scompile.py`;
expected declaration-uses-sorry warnings alone are permitted. Dry-run preflight
and final delivery are performed through `deliver2.py`.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
