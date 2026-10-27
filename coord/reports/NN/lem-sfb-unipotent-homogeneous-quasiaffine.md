## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.UnipotentHomogeneousQuasiaffine`
states `AlgebraicGeometry.exists_unipotent_homogeneous_quotient_immersion`.
Its only proof is `sorry`; it introduces no definitions, helpers, new nodes or
changes to the natural-language statement. All other node fields are preserved.

Read the item and every statement dependency, including their Lean records and
the full relevant source signatures/docstrings. Read the homogeneous quotient
module's two statements and the general-linear-group construction and points
isomorphism. Read Milne, Algebraic Groups (2017), Proposition 14.26 on printed
p.286 (PDF p.298). The existing split correctly uses only L contained in V^U,
not the unnecessary equality printed in that proof.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean |
| --- | --- |
| k algebraically closed field | `{k : Type u} [Field k] [IsAlgClosed k]` |
| G and U group schemes over k | `G U : Over (Spec (.of k))`, `[GrpObj G] [GrpObj U]` |
| G affine | `[IsAffine G.left]` |
| G smooth | `[Smooth G.hom]` |
| G connected | `[ConnectedSpace G.left]`, including nonemptiness |
| G finite type | `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]` |
| U a smooth closed subgroup | `i : U ⟶ G`, `[IsClosedSubgroupScheme i] [Smooth U.hom]` |
| some m >= 1 and faithful matrix homomorphism | `m : ℕ`, `hm : 1 ≤ m`, `ρ : U ⟶ GeneralLinearGroup (LinearGroupSchemes.Index.{u} m) k`, `[IsMonHom ρ] [IsClosedImmersion ρ.left]` |
| every u in U(k) has (rho(u)-I)^N=0 for some N >= 1 | `hρ` quantifies every k-point as an over-morphism from `(Spec (.of k)).asOver (Spec (.of k))`; `homMulEquiv ... k k (a ≫ ρ)` is coerced to its matrix, and `∃ N : ℕ, 1 ≤ N ∧ (...) ^ N = 0` |
| G/U the separated finite-type scheme representing the fppf coset sheaf | `Q`, `q : G ⟶ Q`, the three properties of `Q.hom`, `hQ`, `ηq`, `hηq`, `hquot` |
| the particular coset sheaf, with its canonical quotient map | The presheaf coequalizer is of projection `fst G U` and right multiplication `lift (fst G U) (snd G U ≫ i) ≫ μ[G]`, after Yoneda. `ηq` maps it to `yoneda.obj Q`; `hηq` fixes the map on generators to `yoneda.map q`. `hquot` is its universal property against every fppf sheaf, verbatim from the recorded quotient dependency. No arbitrary unidentified quotient is used. |
| exists n >= 0 | `∃ n : ℕ`, including zero |
| k-morphism to Spec k[x_1,...,x_n] | `j : Q ⟶ (Spec (.of (MvPolynomial (Fin n) k))).asOver (Spec (.of k))`; being in `Over` enforces the k-morphism condition |
| j factors closed into open | `IsImmersion j.left`; Mathlib's `IsImmersion.isImmersion_iff_exists` (Immersion.lean:155) gives exactly the factorization into `IsClosedImmersion` followed by `IsOpenImmersion` |
| no normality or connectedness of U | No such binders or substitute assumptions occur |

Fixing witnesses m and rho in binders is the universal statement for every supplied
faithful representation satisfying the existential hypothesis; the conclusion is
independent of these witnesses. Similarly the quotient binders concern every
presentation satisfying exactly the dependency's sheafification property. Extra
consequences in the dependency theorem (flatness, surjectivity, torsor equations
and rational-point surjectivity) are not added as assumptions.

Dependency declarations used:

- `Field`, Mathlib.Algebra.Field.Defs; `IsAlgClosed`,
  Mathlib.FieldTheory.IsAlgClosed.Basic; `ConnectedSpace`,
  Mathlib.Topology.Connected.Basic.
- `CategoryTheory.GrpObj` and `CategoryTheory.IsMonHom`,
  Mathlib.CategoryTheory.Monoidal.Grp and the monoid-object API, as recorded
  by def-sc-group-scheme.
- `AlgebraicGeometry.IsClosedSubgroupScheme`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs; its class extends
  the subgroup and homomorphism predicates and gives the closed immersion.
- `AlgebraicGeometry.Smooth`, Mathlib.AlgebraicGeometry.Morphisms.Smooth;
  `LocallyOfFiniteType`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType;
  `QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- `AlgebraicGeometry.GeneralLinearGroup` and
  `AlgebraicGeometry.GeneralLinearGroup.homMulEquiv`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.
  Imported through the recorded def-sc-general-linear-group module,
  Sheaf.AlgebraicGeometry.LinearGroupSchemes, which also supplies its
  `LinearGroupSchemes.Index` abbreviation (ULift of Fin m). No GL is copied.
- `AlgebraicGeometry.Spec` and `Spec.map`,
  Mathlib.AlgebraicGeometry.Scheme; the polynomial algebra has its standard
  k-algebra structure, which determines its over-object.
- `AlgebraicGeometry.IsClosedImmersion`,
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion;
  `AlgebraicGeometry.IsOpenImmersion`, Mathlib.AlgebraicGeometry.OpenImmersion;
  `AlgebraicGeometry.IsImmersion`, Mathlib.AlgebraicGeometry.Morphisms.Immersion.
- `AlgebraicGeometry.exists_homogeneous_fppf_quotient` and
  `AlgebraicGeometry.exists_orbit_stabilizer_quotient_iso`,
  Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousOrbitQuotientGeometry:
  the precise coequalizer/sheaf universal property in their signatures is used
  as the meaning of the specified quotient. This imports the recorded dependency
  without introducing a private quotient predicate.

Imports for already stated proof dependencies are retained: StandardGroupSchemes
(def-sc-gm-ga), SmoothGroupOrbitGeometry (lem-sfb-smooth-group-orbit-geometry),
and Mathlib's Separated module (the affine-source separatedness match).
The Chevalley line-stabilizer, geometric-unipotence/unitriangular embedding,
and unipotent-to-multiplicative-trivial proof dependencies had no recorded
Lean declaration in the read DAG; their proof plan remains in the docstring.
They are not needed to type this statement, so are not restated here.

Edge cases checked before writing:

- The trivial subgroup is permitted; its identity representation has nilpotent
  difference zero with N=1. The conclusion does not require a positive n.
- U=G is permitted when G itself satisfies unipotence; its quotient is a point.
- Nonconnected smooth U is allowed: in positive characteristic the constant
  additive F_p subgroup of G_a has the faithful 2-by-2 unitriangular representation.
  Neither a connectedness nor a normality restriction is hidden in the binders.
- N=0 is excluded explicitly, while m=0 is excluded by `hm` as in the node.
- Every field characteristic is allowed. No normality condition on i occurs.
- Group schemes have an identity section, so the empty group is not accidentally
  an added case. The quotient universal property fixes Q; it does not permit
  replacing the nonempty quotient by the empty scheme.
- No quantification over test algebras in a smaller independent universe occurs.
  The matrix index is lifted to the field's universe exactly as the dependency
  construction requires. Q and the sheaf tests use the dependency's same universe.
- The matrix condition concerns k-points only, exactly as the node requests;
  it does not impose nilpotence over all nonreduced algebras.

Searches actually run for this item:

- msearch leanfinder: "A smooth unipotent closed subgroup of a smooth connected
  affine algebraic group has a homogeneous quotient admitting an immersion into
  finite dimensional affine space". Eight hits: topological special-linear-group
  embeddings, Galois category quotients, Scheme.IsQuasiAffine and its immersion
  permanence, and AffineSpace.instIsAffine. None states this homogeneous quotient
  theorem. The immersion permanence statement assumes an immersion already.
- msearch loogle: `"unipotent", "quotient"`. Zero hits.
- msearch grep: `unipotent.*(quotient|quasi.?affine)|(quotient|quasi.?affine).*unipotent`.
  Zero Mathlib hits.
- rg on lean/WeilConjectures and lean/Sheaf for the item id and unipotent/quotient/
  quasiaffine phrases. No declaration of this statement; existing solvable group
  and split reductive quotient statements have different hypotheses/conclusions.
- rg on dag/lean_names_upstream.json for the item id: no hit.
- Read GL homMulEquiv and subgroup APIs, searched existing affine-space over-object
  usages, and read IsImmersion.isImmersion_iff_exists. All needed notions exist;
  no new definition node or dependency repair is needed.

Validation: scompile.py compiled the single delivered file against the current
server sources successfully. The wrapper first reported a sandbox OSError 28
(no space left on device), then its built-in confirmation compile succeeded
(exit 0, 2.6 seconds). No Lean errors or non-sorry warnings were returned.
The prescribed deliver2.py --no-push dry run passed server preflight and compilation
(commit 792879e3810); only the module, node record and report were staged.

No statement dispute or node fault was found.

Delivery result: both push attempts passed compilation and server preflight but
failed in the remote Git unpacker with "unable to create temporary object directory".
The server compile wrapper also reported OSError 28 before its successful fallback
confirmation. No delivery branch was pushed. The complete packet remains in this
sandbox; repair of the server's Git storage is outside this worker's write scope.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
