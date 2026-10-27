## Worker report

The delivery states `AlgebraicGeometry.chevalley_root_exponential_group` in
`Sheaf.AlgebraicGeometry.GroupScheme.ChevalleyRootExponentialGroup`, with exactly one
postponed proof (`sorry`) and no new definitions. The item statement is unchanged.
Four existing terminology nodes are added to stmt_deps: def-sfb-diagonalizable-group,
def-sc-general-linear-group, def-sfb-semisimple-group-scheme, and
 def-sfb-torus-character-tangent-weights. Their notions were needed explicitly;
none is copied or redefined. All writes are in this item's sandbox.

Source read: Milne, Algebraic Groups (2017), printed pp.510--511 (PDF pages 522--523),
equation (153), Theorem 23.72 and Corollary 23.73. The node already specifies the
weight-character torus rather than independent scalars on all weight blocks and
already omits Milne's integral Lie-form identification in positive characteristic.
Both of those qualifications are retained. The current blueprint checkout was
searched for this node and Theorem 23.72; this supporting node is not a blueprint
unit statement (blueprint.is is null).

Hypotheses, matched individually:

- Rational V and its finite dimension: `V`, `AddCommGroup`, `Module ℚ`,
  `FiniteDimensional ℚ`. Reduced rational crystallographic roots: `R`, `c`,
  `_hfinite`, `_hne`, `_hspan`, `_htwo`, `_hint`, `_hreflect`, `_hreduced`.
  These are the same explicit rational-system axioms used by the admissible
  representation dependency. The integral weight lattice is `P` with `_hP`,
  exactly the condition that every coroot has integral value.
- Split semisimple rational Lie algebra: `g` with its LieRing/LieAlgebra and
  finite-dimensional instances, and `_hss : HasTrivialRadical ℚ g`.
  The Cartan `H` is abelian (`_hab`), maximal abelian (`_hmax`), and identified
  by `θ` with the rational dual of V. The decomposition `_hdecomp`, together
  with `_he`, diagonalizes every Cartan adjoint operator simultaneously,
  including the zero weight on H.
- Root vectors and Chevalley basis: `_he` makes each root vector nonzero and
  gives the bracket with every Cartan element; `_hbasis` quantifies a simple
  root base (integral coefficients of uniform sign), and an actual basis of g
  with the specified simple coroots and root vectors. `_hopp`, `_hstring` and
  `_hzero` give respectively the opposite-root bracket, the signed root-string
  coefficient with its largest p, and the bracket zero outside the root set.
- Faithful representation: the existing `LieRingModule g W` and `LieModule ℚ g W`,
  finite dimension, and `_hfaith : LieModule.IsFaithful ℚ g W`.
- Full free lattice: `Λ : Submodule ℤ W`, `_hlattice : Submodule.IsLattice ℚ Λ`,
  and `_hfree : Module.Free ℤ Λ`. The finite weight set is `Ω`.
  `_hΩ` places its weights in P and makes their eigenspaces nonzero;
  `_hweights` is the internal direct sum of the rational weight spaces;
  `_hgenerate` is exactly ZΩ = P; `_hintegral` is the internal direct sum of
  their intersections with Λ. All weight spaces are the dependency's existing
  `LieModule.weightSpace`, so their defining Cartan eigenvector equations are retained.
- Nilpotence is `_hnil` for every represented root vector; admissibility is
  `_hdiv`, for every root, nonnegative m and lattice vector, with the rational
  divided power. No factorial is inverted in F.
- The field is `F : Type u`, `[Field F] [IsAlgClosed F]`. All objects and test
  algebras inhabit the same common universe u, which can be enlarged to the
  maximum of any originally distinct universes. In particular test algebras
  are never quantified in a smaller independent universe.

Conclusions, matched individually:

- `I`, its finite/decidable instances and `b : Module.Basis I ℤ Λ` provide matrix
  coordinates. Base change of this basis identifies Λ tensor_Z A with A^I,
  in particular W_F with F^I. No replacement representation is assumed: the
  column equation for `D a m` pins each integer matrix to the rational divided
  power on the given lattice. The equation `N a ≤ m → D a m = 0` supplies the
  exact finite-support condition, independent of characteristic.
- The maps `x a` are actual group-scheme homomorphisms from the existing Ga
  to the existing GL(I,F). For every commutative F-algebra A and z in A, the
  `homMulEquiv` matrix is exactly the finite sum of `z^m` times the integer
  matrices mapped by `Int.castRingHom A`. Thus the formula is imposed on
  nonreduced algebras too, including the zeroth term.
- The group G (the node's H) has a closed inclusion `iG`; every exponential
  factors as `y a ≫ iG`. The quantified K/iK clause says that G factors through
  every closed subgroup containing all the x_a. This is precisely the smallest
  closed subgroup, with no smoothness assumed in that minimality quantifier.
- `IsSemisimpleGroupScheme G.X` expands to smooth, connected, affine and finite
  type, with every smooth connected solvable normal closed subgroup trivial.
  This is the node's precise semisimplicity, not a property of abstract F-points.
- The torus is literally the existing `diagonalizableGroup F P`, the Hopf
  spectrum of the finitely supported additive group algebra. Its existing
  Hopf operations send e^a to e^a tensor e^a, 1 and e^(-a). The morphism `iT`
  is a maximal closed torus by `IsMaximalTorus`, and the split-torus isomorphism
  is a conclusion. No independently chosen torus is substituted for D(P).
- The additive equivalence `χ` identifies P with the actual character Hom group;
  the pulled-back Laurent generator is exactly `AddMonoidAlgebra.single lam 1`.
  On every A, t, weight wt, and lattice vector w in that weight space, the
  matrix-coordinate equation says the action on w is multiplication by χ(wt)(t).
  Tensor-linearity extends this equation to the whole base-changed weight summand.
- The additive equivalence `ν` identifies the integer dual of P with the actual
  cocharacter Hom group. Its composition with χ(lam) is the integer power map
  with exponent f(lam). Both lattices are explicitly `Module.Finite ℤ`.
- `Q : RootDatum R P (Module.Dual ℤ P)` is reduced, its roots are exactly the
  original vectors of R, its coroot evaluations are the given rational c_a,
  now integral on P, and its perfect pairing is ordinary evaluation.
- `act.smul` is explicitly conjugation via iT. Its nonzero tangent-character
  weights are exactly `Set.range Q.root`. This tests characters, not their
  differentials, and so includes small positive characteristics.
- To fix the *group* coroot convention, the isomorphisms `s a` obey the reflection
  formula with `Q.coroot a`. They are realized by conjugation by the actual root
  word x_a(1)x_(-a)(-1)x_a(1) on every A-point. Together with the actual
  composition pairing, this identifies ν(Q.coroot a) with the coroot in the
  group-root convention, rather than choosing arbitrary cocharacters satisfying
  only the pairing-two equation. These clauses spell out the convention in the
  reductive-Borel dependency; they impose no additional input hypothesis.
- For `Subsingleton V` and `R = ∅`, both G and D(P) are isomorphic to the trivial
  group scheme. No integral-form Lie algebra identification is in the statement.

Dependency declarations read and used:

- `Sheaf.LinearAlgebra.RootDatumLatticeEmbedding`: `RootDatumLattice.lattice_embedding`,
  `rootSpan`, `root`, `coroot`, `weightLattice` (full signatures and docstrings read).
  The rational-system and weight-integrality axioms are stated on arbitrary V as
  in the next dependency; no second lattice definition is introduced.
- `Sheaf.Algebra.Lie.ChevalleyAdmissibleRepresentation`:
  `LieAlgebra.exists_chevalley_admissible_representation`. Its given data and all
  nonoptional conditions are the input binders, not merely a selected witness.
  Its final rank-zero witness W=Q is an optional existence choice; the present
  theorem applies to any given admissible W, including sums of trivial modules.
- Mathlib `Field` (Algebra/Field/Defs.lean:180) and `IsAlgClosed`
  (FieldTheory/IsAlgClosed/Basic.lean:62), whose docstrings and definitions were read.
- `CategoryTheory.GrpObj` (Mathlib.CategoryTheory.Monoidal.Grp:43) and the group-scheme
  interpretation in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`:
  `AlgebraicGeometry.reductive_borel_pair_structure` and
  `semisimpleGroupScheme_isReductive`; character/cocharacter Hom groups, composition
  pairing, conjugation action and reduced-root conventions are retained.
- `Sheaf.AlgebraicGeometry.DiagonalizableGroup`: `diagonalizableGroup`.
- `Sheaf.AlgebraicGeometry.LinearGroupSchemes` imports the actual upstream
  `GeneralLinearGroup`, its GrpObj structure and `GeneralLinearGroup.homMulEquiv`
  from `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: additive, multiplicative, affine;
  `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations`:
  `TorusCharacterTangent.additiveParameterPoint` and `multiplicativePointCoordinate`.
- `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`: `IsSemisimpleGroupScheme`;
  `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`: `IsMaximalTorus`;
  `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`: `splitTorus`;
  `Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights`: `weightSpace`.

The module also imports the recorded proof dependencies which have modules:
AffinePointedMapGeneratedSubgroup, MultiplicativeCharacterAntiduality,
LieLocalDimension, IdentityLocalDimension, MultiplicativeTypeLargestSubtorus,
and the root parametrizations module. Mathlib proof leaves use Group.Smooth
(`smooth_of_grpObj`) and RootSystem.BaseExists (including Base.toWeightBasis,
Base.toCoweightBasis, span_int_root_support, span_int_coroot_support and Base.mk').
Their signatures were read. Unstated proof prerequisites remain in the proof plan:
diagonalizable-group-geometric-criteria, chevalley-integral-rank-one,
chevalley-exponential-big-cell, solvable-normal-subgroup-products,
rank-one-reductive-generation and semisimple-roots-span. They are not needed to
type the statement and no fictitious import was made for them.

Edge cases checked: rank zero and empty roots (no root-indexed assumptions, P=0,
minimal subgroup trivial); arbitrary trivial summands in W; zero-dimensional
coordinate spaces; m=0 (identity divided power); an arbitrary sufficiently large
nilpotence cutoff N; characteristics 2 and 3 (all reduction follows integer
matrices); characteristic zero; nonreduced test algebras and the zero test ring.
The torus action is tested on lattice vectors and extends to arbitrary scalar
coefficients. Minimality includes nonreduced and nonsmooth closed subgroups.
There is no nonempty-root, positive-rank or nonzero-dimension assumption.

Searches actually run:

- msearch LeanFinder: “Chevalley root exponentials on an integral admissible
  lattice generate a smooth connected semisimple algebraic group with its weight
  character lattice”. Eight hits, GeckConstruction/EmbeddedG2 Lie algebra and
  combinatorial results; no group-scheme construction theorem.
- msearch Loogle: `GeneralLinearGroup, TensorProduct.map, MonoidAlgebra`.
  Zero hits, diagnostic “unknown identifier 'GeneralLinearGroup'”; not treated
  as evidence that the project has no GL. The upstream GL was found and reused
  by direct source search.
- msearch grep: `Chevalley|root.*exponential|generalLinear`. Twenty-five shown
  matches, primarily matrix GL references; no exact statement.
- msearch LeanSearch: “Integral divided power root exponentials generate a
  semisimple algebraic group scheme”. Eight hits, led by `DividedPowers.exp`
  and formal power-series/divided-power results; no algebraic group theorem.
- Direct rg in lean/WeilConjectures and lean/Sheaf for `Chevalley|chevalley` and
  the exact item id; rg in dag/lean_names_upstream.json for the same; no duplicate
  statement. Hits included the admissible representation and integral-root-model
  consumer, which were read. The consumer does not state this theorem.
- DAG/module search located the four existing terminology nodes above; their
  statements and Lean records were read, then their actual source declarations.
  No new notion or definition node was necessary.

No statement dispute or statement correction. Compile only through scompile.py.
The sandbox and named library module have compiled cleanly; the delivery dry run
and final delivery will run the authoritative checks again.

## Second reading by Q116

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
