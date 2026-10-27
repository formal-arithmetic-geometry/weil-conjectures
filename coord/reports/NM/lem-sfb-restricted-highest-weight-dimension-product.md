## Worker report

The single module `Sheaf.AlgebraicGeometry.GroupScheme.RestrictedHighestWeightDimensionProduct`
states `AlgebraicGeometry.RationalHighestWeight.restricted_highest_weight_dimension_product`.
Its only proof is `sorry`. No definition, auxiliary theorem, statement correction, or new node
is introduced. The item gains only its Lean record and two already landed statement dependencies:
`def-sfb-semisimple-group-scheme` and `def-sfb-rational-highest-weight-data`.

Hypothesis and clause correspondence:

- Algebraically closed field: `{F : Type u} [Field F] [IsAlgClosed F]`.
- Positive characteristic: `(p : ℕ) [CharP F p] (hp : 0 < p)`; the field assumptions
  force primality, so p=1 is impossible and p=2 is included without another restriction.
- Group schemes: `S T B U : Grp (Over (Spec (.of F)))` use the recorded group-object encoding.
- Semisimplicity: `hS : IsSemisimpleGroupScheme S.X` expands to smoothness, connectedness,
  affineness, finite type, and triviality of smooth connected solvable normal subgroups;
  its solvability predicate is termination of the actual scheme-theoretic commutator series.
- Simply connected: `hsc` is exactly the universal central-isogeny condition in
  `exists_rho_section_modules`. The kernel is `GrpObj.ker f`, its finiteness is
  `IsFinite ...hom`, and centrality is the displayed commutation for every test algebra
  and both arbitrary kernel and source points. There is no reducedness or prime-to-p assumption.
- The split maximal torus and Borel containing it: `iT iB j` and
  `hTB : IsRhoBorelPair iT iB j`. This is the recorded conjunction of maximal torus,
  split-torus isomorphism, Borel, and equality of the two inclusions into S.
- Unipotent radical: `iU` and `hUclosed hUnormal hUsmooth hUconnected hUunipotent hUmax`
  reproduce the radical specification in `reductive_borel_pair_structure`, including
  maximality among all smooth connected normal unipotent closed subgroups.
- Affine instances on S, T, U supply the coordinate algebra API. These are consequences of
  semisimplicity, split torus, and closed immersion into the affine Borel subgroup of S;
  they impose no additional mathematical case restriction.
- Character and cocharacter lattices are the actual additive Hom groups, rather than
  abstract lattices with an arbitrary identification. `IsCommMonObj` witnesses expose
  their canonical abelian group structures as in the recorded root-datum theorem.
- `aS aB haS haB` specify conjugation on S and B. `Φ P b hroot hpair hΦ hpos` use the
  recorded root datum, its base and integer bilinear pairing. `hroot` identifies roots
  with actual characters, `hpair` identifies pairing with composition of characters
  and cocharacters and an integer power map, `hΦ` specifies exactly the nonzero
  character tangent weights on Lie(S), and `hpos` specifies positivity by Lie(B).
  Thus an unrelated root datum cannot be supplied. `b.support` is exactly Δ.
- The introductory rho is not used in any hypothesis or conclusion of this dimension
  identity. Its existing integral half-sum construction remains in the public import
  RhoSectionModules; no independent rho or rho-existence assumption is introduced.
- Weights λ, μ are `lam mu` in the additive character lattice. `hlam hmu` express
  dominance by nonnegative integer simple-coroot pairings. `hrestricted` gives their
  strict upper bound by `(p : ℤ)` for lam; its lower bound is already `hlam`.
- The three arbitrary finite-dimensional vector spaces are `Vlam Vmu Vsum`, in independent
  universes v, w, z, with their additive, F-module and finite-dimensional structures.
  `clam cmu csum` are maps into tensor product with the actual coordinate Hopf algebra.
  The six `...coassoc`/`...counit` hypotheses give the two required coaction identities
  separately for every module. `hlamsimple hmusimple hsumsimple` use the existing
  nonzero-and-no-proper-stable-subspace predicate.
- `hlamweight hmuweight hsumweight` use existing `HasHighestWeight` on the given T
  and U inclusions. It says the U-invariant equalizer is one-dimensional and its
  restricted T-coaction is the character coaction on every vector. These are coaction
  equalities, retaining the identities after every algebra extension, including nonreduced
  algebras. The third weight `(lam + p • mu).toMul` is exactly λ+pμ, as character addition
  is multiplication of values.
- The sole conclusion `Module.finrank F Vsum = Module.finrank F Vlam * Module.finrank F Vmu`
  is equality of ordinary natural-number dimensions, equivalently their nonnegative
  integer values. Nothing is cast into F. No Frobenius map, Frobenius identification,
  regular-function induced realization, or tensor decomposition is a hypothesis.

Dependency declarations read and reused:

- Mathlib.Algebra.Field.Defs: `Field`; Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosed`.
- Mathlib.CategoryTheory.Monoidal.Grp and WeilConjectures.AlgebraicGeometry.GroupScheme.Defs:
  `Grp`, `GrpObj`, `IsMonHom`, `GrpObj.ker`, and the existing subgroup predicates.
- Sheaf.AlgebraicGeometry.RhoSectionModules: `IsRhoBorelPair` and
  `exists_rho_section_modules` (the latter's simply-connected interface is reused).
- Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure:
  `reductive_borel_pair_structure` and `semisimpleGroupScheme_isReductive`.
- Sheaf.AlgebraicGeometry.GroupScheme.Semisimple: `IsSemisimpleGroupScheme` and its
  derived-series definitions (through the existing public imports).
- Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData: `coordinateAlgebra`,
  `IsSimple`, `HasHighestWeight`, `invariants`, `coordinateMap`, `characterElement`.
- Sheaf.RingTheory.HopfActionModuleData: `HopfAction.Coassociative`, `HopfAction.Counital`.
- Mathlib.LinearAlgebra.RootSystem.Defs and Base: `RootDatum`, `RootPairing.Base`,
  `Base.support`, `Base.IsPos`, `toLinearMap`, and `coroot`.

All currently recorded proof-only modules are plain imports: SimpleModuleDualHighestWeight,
HomomorphismFactorization, BorelRootProductCoordinates, and upstream Geometrically.Reduced.
The reductive structure module is already a public statement import. The remaining three
proof nodes (root-datum-isogeny-realization, isogeny-root-power-laws,
restricted-frobenius-tensor-simplicity) have no Lean attachment in the read DAG, so no module
could be imported for them. Their exact uses remain in the six-step proof docstring.
No unstated proof input is needed to type this stage-2 statement.

Edge cases checked before and after drafting: empty root set (Φ and b.support may be empty),
trivial group, both zero weights and either zero weight, p=2, and products of simple groups.
There is no positive-rank, positive-weight or nonempty-root hypothesis. For the trivial group,
simplicity leaves a one-dimensional space and the conclusion is 1=1*1. A zero vector space
fails IsSimple, exactly as in the node. Independent module universes avoid unnecessary
universe identifications. Integral pairings are never replaced with their differentials.
No statement fault or dispute was found.

Searches actually run:

- msearch.py leanfinder, query "Dimension of simple rational algebraic group modules at lambda
  plus p mu is product of dimensions when lambda is p restricted": 8 hits including
  FDRep.finrank_hom_simple_simple and LieModule rank/weight-space results. None is the
  algebraic-group restricted highest-weight dimension formula.
- msearch.py loogle, query `"highestWeight", "finrank"`: OK, 0 hits.
- msearch.py grep, query `Steinberg|frobeniusTwist|highestWeight`, RepresentationTheory:
  OK, 0 hits.
- rg of `restricted.*highest|highest.*dimension|Steinberg` in lean/WeilConjectures and
  lean/Sheaf: only unrelated semilinear Lang-Steinberg references; no dimension formula.
- rg of the item id in both Lean roots and dag/lean_names_upstream.json: no attachment.
- rg of `HasHighestWeight|IsSimple` in the group-scheme sources located the landed coaction
  interface and its highest-weight theorem; these are reused. The upstream RationalHom
  simplicity predicate has characteristic-zero restrictions and is not substituted.

Source verification: read Williamson https://arxiv.org/pdf/1610.06261, Sections 1.1--1.4,
particularly Theorem 1.3 and equation (1.7). The source fixes semisimple simply connected
root data and states restricted-weight tensor simplicity and the p-adic tensor decomposition.
Its Borel convention is opposite (positive roots in Lie(G)/Lie(B)); our statement consistently
uses the node's B-positive highest-line convention on the actual coactions. The numerical
consequence is unchanged. Jantzen remains marked WANTED in the node, and is not claimed read.

Validation: prescribed scompile.py compiled the single delivered file in both sandbox and
library module modes, with no errors or non-sorry warnings (8.8 s and 10.6 s respectively).

## Second reading by NM

I reread the node and completed signature clause by clause. This is a worker self-check;
the dispatcher prohibits subagents and the maintainer provides the independent review.
The root datum is anchored by hroot, hpair, hΦ and hpos, not simply assumed to be an
abstract root datum. The bound is in ℤ, and all three modules have both coaction identities,
simplicity, finite-dimensionality, and the specified highest weights. The radical maximality
and simply-connected centrality quantify over arbitrary subgroup and kernel points.
The third character is the additive λ+pμ and the conclusion is in ℕ. Affineness instances
are implied by the named group/subgroup notions. No Frobenius choice entered the signature.
No mismatch required a statement correction. The only added DAG references are the already
landed definitions used directly, rather than copies or new definitions.
