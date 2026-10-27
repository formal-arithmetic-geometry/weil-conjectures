## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.RestrictedModuleInfinitesimalSimplicity`
states `AlgebraicGeometry.RationalHighestWeight.restricted_module_infinitesimal_simplicity`.
It has one theorem, with proof `sorry`, and no new definitions. The docstring contains
all five proof steps from the node, including scalar-extension normalization of the
operator algebra, the rank-one orbit formula, and the closed stabilizer argument.

Source read: Milne, *Algebraic Groups* (2017), Section 22(e), printed p.481,
statement 22.54 and the surrounding characteristic-p paragraphs, in the supplied PDF.
The node already uses the corrected fundamental-weight coefficients/simple-coroot
pairings. The delivered statement preserves that correction; this delivery changes
neither the natural-language statement nor the proof.

Hypothesis and clause correspondence:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
  Positive characteristic is `(p : ℕ) [CharP F p] (hp : 0 < p)`. No oddness or
  good-characteristic restriction is imposed.
- The group scheme is `G : Grp (Over (Spec (.of F)))`; its group-object law is
  the recorded Mathlib `GrpObj` structure. `hG : IsSemisimpleGroupScheme G.X`
  means smooth, connected, affine, locally of finite type and quasi-compact, with
  every smooth connected solvable normal closed subgroup terminal. The predicate's
  actual recursive scheme-theoretic commutator series is reused.
- Simple connectedness is `hsc`: every homomorphism `f` from a semisimple group
  scheme that is surjective with `IsFinite (GrpObj.ker f).hom` and central kernel
  is `IsIso f`. Centrality is the displayed commutation of every kernel point with
  every group point for every commutative F-algebra `A : Type u`. Thus nonreduced
  kernels and inseparable central isogenies are retained. Finiteness of the kernel
  is equivalent here to finite-dimensionality of its affine coordinate algebra.
- `iT : T ⟶ G`, `hT : IsMaximalTorus iT`, and `hsplit` give the specified split
  maximal torus, with rank allowed to be zero.
- `iB`, `hB`, `j` and `hj : j ≫ iB = iT` give the Borel and its containment of T.
- `iU : U ⟶ B` and `hUclosed`, `hUnormal`, `hUsmooth`, `hUconnected`,
  `hUunipotent` give a smooth connected normal unipotent closed subgroup. `hUmax`
  says every such subgroup factors through it: this is exactly the unipotent
  radical in the recorded Borel-pair conclusion, not an arbitrary unipotent group.
- Affineness instances for G, T and U expose the coordinate Hopf algebras. They
  impose no new restriction: G is semisimple, T is split, and U is closed in
  the Borel, itself closed in the affine G.
- `IsCommMonObj T.X` and the commutativity of the multiplicative group provide
  the commutative Hom-group structures from the recorded Borel-pair interface.
  The lattices are the actual `Additive (T ⟶ G_m)` and `Additive (G_m ⟶ T)`.
- `aG`, `aB`, `haG`, `haB` pin the two torus actions to conjugation through
  the specified inclusions; the actions are not arbitrary representations.
- `Φ`, `P : RootDatum Φ ... ...`, `b : P.Base`, and `hroot` identify roots with
  actual character morphisms. `hpair` pins the integer pairing to composition
  with the corresponding integer power morphism of G_m. `hweights` identifies
  exactly the nonzero tangent-character weights in G. `hpositive` says that
  positivity is precisely occurrence in Lie(B). Thus `b.support` is the specified
  simple-root base, and `P.coroot` is its coroot family.
- The vector space is `{V : Type v} [AddCommGroup V] [Module F V]` with
  `[FiniteDimensional F V]`. Its universe is independent of the field's.
- `c : V →ₗ[F] V ⊗[F] coordinateAlgebra G` is the actual coaction into global
  functions, with `hcoassoc : HopfAction.Coassociative ... c` and
  `hcounit : HopfAction.Counital ... c`. No arbitrary coordinate algebra is supplied.
- `hsimple : IsSimple c` includes nontriviality of V and says precisely that a
  subspace whose image lies in the tensor-inclusion range is bottom or top.
- `lam : T ⟶ G_m` is the character lambda. `hhighest : HasHighestWeight c iT
  (iU ≫ iB) lam` gives dimension one of the equalizer defining U-invariants,
  and the actual character coaction identity on the entire invariant line.
  These identities remain true after every scalar extension, including nonreduced
  test algebras; no rational-points-only highest-weight condition is substituted.
- `hrestricted` quantifies over `α : b.support` and requires
  `0 ≤ P.toLinearMap (Additive.ofMul lam) (P.coroot α)` and that integer strictly
  less than `(p : ℤ)`. These are coroot pairings, not simple-root coordinates.
- The Lie algebra in the node is rendered directly by quantifying over every
  `x : coordinateAlgebra G →ₗ[F] F` satisfying the displayed Leibniz identity
  at `Coalgebra.counit (R := F)`. The canonical coordinate Hopf counit evaluates
  a regular function at the identity. This avoids constructing a second Lie algebra.
- The differential operator applied to v is exactly
  `(TensorProduct.rid F V) (x.lTensor V (c v))`: first apply `1_V tensor x`, then
  the canonical identification `V tensor F = V`.
- The conclusion quantifies over every `N : Submodule F V`, assumes this vector
  belongs to N for all such x and all v in N, and concludes `N = ⊥ ∨ N = ⊤`.

Dependency declarations used:

- `Mathlib.Algebra.Field.Defs`: `Field` (line 180; full class signature read).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (line 62; docstring and
  equivalence with the root formulation read).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, `Grp`,
  with the group-scheme specialization and kernel API in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`. Its docstring identifies
  group schemes, homomorphisms, finite kernels and subgroup terminology.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`:
  `AlgebraicGeometry.reductive_borel_pair_structure` and
  `AlgebraicGeometry.semisimpleGroupScheme_isReductive`. Full signatures and
  proof docstrings were read. The chosen T/B/U and root-datum data are precisely
  the data in its universal Borel-pair conclusion.
- `Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData`:
  `coordinateAlgebra`, `coordinateHopf`, `IsStable`, `IsSimple`, `invariants`,
  `characterElement`, `HasHighestWeight`, using the existing `HopfAction`
  coassociativity/counit predicates. Full definitions/docstrings were read.
- `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`:
  `IsSemisimpleGroupScheme`, with its `GroupSchemeDerivedLength` and
  `IsSolvableGroupScheme` definitions. Full definitions/docstrings were read.
- The last two are already landed notion nodes; their ids are added to the
  item's `stmt_deps` to record the interfaces used. No dependency node is modified.
- The already stated proof dependency
  `Sheaf.AlgebraicGeometry.GroupScheme.BorelRootProductCoordinates` is imported
  privately. The other proof-only nodes have no recorded Lean statements in the
  read repository, so no speculative imports are added for them. Their ids and
  precise roles are retained in the theorem's proof docstring.

Edge cases checked before writing:

- `p = 2` satisfies the same characteristic hypotheses and integer inequalities;
  neither Lie semisimplicity nor a division by 2 is assumed.
- The trivial group has rank-zero torus and empty root family. The restricted
  condition is vacuous, while rational simplicity forces V to be one-dimensional;
  differential stability then has exactly the required conclusion.
- Highest weight zero is allowed by the non-strict lower bound. The trivial
  one-dimensional representation is included.
- A product root system need not be irreducible, and `b.support` ranges over
  every simple root of every factor.
- The zero vector space is excluded exactly by rational simplicity, as the node
  requires. Bottom and top subspaces are both included in the quantified conclusion.
- `p = 0` is excluded by `hp`; `p = 1` cannot occur for a field with `CharP F p`.
- No independent lower test-algebra universe is used: centrality tests algebras
  in the field's universe. Highest-weight and submodule conditions are coaction
  identities, so they need no size-limited family of points.

Searches actually run through msearch.py:

1. leanfinder: "A simple rational module for a simply connected semisimple algebraic
   group with p restricted highest weight remains simple under its differential Lie
   algebra action". Eight hits: Geck irreducibility, `LieModule.IsIrreducible`, its
   constructor and nontriviality result, adjoint irreducibility, Weyl-group root
   representation simplicity, characteristic-zero linear weights, and `chainBot`.
   None is this rational positive-characteristic theorem.
2. loogle: `LieModule.IsIrreducible`. Eight hits, comprising the definition,
   constructor, submodule criterion, adjoint/simple-Lie examples, two characteristic-zero
   radical lemmas, and the Geck example. No exact or one-line specialization.
3. grep: `Steinberg|frobeniusKernel|infinitesimally|restricted.*highest` in Mathlib.
   Zero hits.
4. leansearch: "A p restricted highest weight simple rational representation of a
   simply connected semisimple group is simple for its differential Lie algebra action".
   Eight hits, all general/simple Lie-algebra definitions and adjoint facts or the
   Weyl-group root representation; no match for the requested theorem.
5. `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
   `restricted.*highest`, and `infinitesimally` found no existing theorem. Follow-up
   searches for coactions, rational modules and highest weights found the landed
   RationalHighestWeightData interface, which is reused. The existing
   SimplyConnectedCharacterLattice statement was read to match the already used
   scheme-theoretic central-isogeny formulation of simple connectedness.
6. Declaration-name search in Mathlib, WeilConjectures and Sheaf for
   `restricted_module_infinitesimal_simplicity` found no collision.

No STATEMENT-DISPUTED issue remains, no statement correction is made, and no new
notion or dependency module is needed. Only the existing landed notion ids are
added to `stmt_deps`; all other original fields are preserved.

Validation: scompile.py compiled the sandbox and intended library module cleanly
on the server (12.6 s and 2.4 s respectively). No diagnostic commands remain,
`autoImplicit` is false, and every Lean line is at most 100 characters.

## Second reading by Q03

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
