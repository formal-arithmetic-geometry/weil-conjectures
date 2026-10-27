## Worker report

The module states Milne's Rosenlicht dichotomy in the nonproper case, followed by the
smooth connected refinement from the reduced identity component. The only postponed
proof is `AlgebraicGeometry.exists_smooth_connected_affine_closed_subgroup_of_not_isProper`.
Its docstring records all six accepted DAG proof steps and their supporting nodes.
No definition is introduced; the node is changed only in `lean`.

Clause-by-clause rendering:

- The algebraically closed base field is `(k : Type u) [Field k] [IsAlgClosed k]`.
  There is no restriction on the characteristic.
- The k-group scheme H is `(H : Over (Spec (.of k))) [GrpObj H]`.
  The over-category retains its structure map, and the existing group-object structure
  retains multiplication, inverse and identity with their axioms.
- Smoothness is `[Smooth H.hom]`; connectedness, including nonemptiness, is
  `[ConnectedSpace H.left]`; separatedness is `[IsSeparated H.hom]`, whose defining
  field says its diagonal is a closed immersion.
- Finite type is `[LocallyOfFiniteType H.hom] [QuasiCompact H.hom]`, exactly the
  conjunction recorded for def-weil-finite-type-morphism.
- Nonproperness is `(hH : ¬ IsProper H.hom)`.
- The existential U is a k-scheme `U : Over (Spec (.of k))` with its own `GrpObj U`.
  The morphism `i : U ⟶ H` is over k. `IsClosedSubgroupScheme i` is the recorded
  predicate: a homomorphism, injective on algebra points, whose underlying scheme
  map is a closed immersion.
- `Smooth U.hom`, `ConnectedSpace U.left`, and `IsAffine U.left` render smooth,
  connected and affine. Mathlib's affine predicate gives the canonical isomorphism
  to the spectrum of global sections and is equivalent to being isomorphic to a spectrum.
- `0 < topologicalKrullDim U.left` is strict positivity in `WithBot ℕ∞`, not
  positivity of a truncated natural dimension.
- There is no `IsNormalSubgroupScheme i` and no `IsCommMonObj H` hypothesis or conclusion.
  Finite type of U follows from its closed immersion into H and is not added as a clause.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field` (through public imports).
- Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosed` (the relevant algebraic-closure
  node notion here is algebraic closedness, not a chosen closure).
- Mathlib.CategoryTheory.Monoidal.Grp: `CategoryTheory.GrpObj`.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Defs:
  `AlgebraicGeometry.IsClosedSubgroupScheme`, built from `IsSubgroupScheme` and `IsMonHom`.
  The module's documentation supplies the specified over-Spec encoding of group schemes.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `AlgebraicGeometry.Smooth`.
- Mathlib.Topology.Connected.Basic: `ConnectedSpace` (through public imports).
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType and Morphisms.QuasiCompact:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- Mathlib.AlgebraicGeometry.Morphisms.Proper and Morphisms.Separated:
  `AlgebraicGeometry.IsProper`, `AlgebraicGeometry.IsSeparated`.
- Mathlib.AlgebraicGeometry.Scheme and AffineScheme: `AlgebraicGeometry.Scheme`,
  its morphisms and `AlgebraicGeometry.IsAffine` (through public imports).
- Mathlib.Topology.KrullDimension: `topologicalKrullDim`.

The available recorded proof-dependency modules are plain imports:
Sheaf.AlgebraicGeometry.ZeroDimensionalClosedSubschemeFinite,
Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent,
Sheaf.AlgebraicGeometry.GroupNeutralComponentTranslates,
WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced,
WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs, and
WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper.
The finite-proper, proper-base-change and proper-composition Mathlib results are already
provided by the imported proper-morphism module. The other proof dependencies have no
recorded declaration at inspection time: affine-normal-subgroup-products,
rational-boundary-positive-stabilizer, rational-fixed-point-affineness,
abelian-subvariety-central and rosenlicht-connected-almost-complement (all with prefix
`lem-sfb-`). They are not statement dependencies and no unstated notion is needed from them.

Edge cases checked before writing: the empty scheme cannot satisfy ConnectedSpace
and has no group identity over the nonempty Spec k. A zero-dimensional finite-type
smooth group is finite and therefore proper, so does not satisfy hH. The trivial
subgroup has dimension zero and cannot witness the strict inequality. For an affine
positive-dimensional H, U = H is allowed. Proper abelian varieties are excluded by
hH. Noncommutative H and all positive characteristics are retained. Universe u is
arbitrary; k, H and U use the common scheme universe of the recorded group-scheme
interface, without an additional small test-algebra universe.

Sources read: literature/milne-algebraic-groups_iAG2017.pdf, Proposition 8.25,
printed pp.153-154, Corollaries 1.35 and 1.39, printed pp.17-18. The source explicitly
warns that equivariant completion would be circular; the docstring retains the accepted
rational-action/dimension-induction route. No statement discrepancy found.

Searches for an existing statement:

- msearch.py leanfinder: "A nonproper smooth connected algebraic group over an
  algebraically closed field contains a positive dimensional smooth connected affine
  closed subgroup". Eight hits: connected complements in real normed spaces and
  Subgroup.connectedComponentOfOne; none is the scheme-theoretic theorem.
- msearch.py loogle: `"GrpObj", "IsProper"`. Zero hits.
- msearch.py grep: `Rosenlicht|nonproper|non.proper.*subgroup|dichotomy`,
  AlgebraicGeometry. Zero hits.
- msearch.py leansearch: "A noncomplete group variety contains an affine algebraic
  subgroup of positive dimension". Eight hits about nonarchimedean open subgroups,
  dense subgroups, subgroup lattices and completions; none states this theorem.
- rg over lean/WeilConjectures and lean/Sheaf:
  `Rosenlicht|rosenlicht|nonproper|non.proper.*subgroup`. Hits concern nonproper-curve
  cohomology and unrelated Rosenlicht product factorization/orbit statements; none matches.
- grep of the exact node id in lean/WeilConjectures: no hits.

No new nodes, dependency repair, statement correction, or STATEMENT-DISPUTED flag.

## Second reading by Q68

Self-check only: this dispatcher-started worker was instructed not to start other agents.
The maintainer supplies the independent delivery review. Re-read the node and signature
against every clause in the mapping above: the closed-subgroup predicate retains the
specified group homomorphism and immersion, smoothness is relative to k, and connectedness
is nonempty connectedness. Strict topological dimension is preserved. No normality or
commutativity was accidentally added. No mismatch or statement change was found.

Validation: scompile.py compiled the statement file in both sandbox and library module modes
without errors or unexpected warnings. deliver2.py --no-push passed server preflight and
per-file compilation. The module has autoImplicit disabled, a single sorry proof, no local
notation or private data, and no lines exceeding 100 characters.
