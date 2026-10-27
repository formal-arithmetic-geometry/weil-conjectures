## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.RankOneOppositeBorelIntersection`
states `AlgebraicGeometry.rank_one_opposite_borel_intersection`, with `sorry` as
its only proof. It introduces no definition. The node is unchanged except for
its `lean` field. Source read directly: Milne, Algebraic Groups (2017), printed
pp.412--415, Theorem 20.16(a) implies (b), Proposition 20.18, Lemmas 20.20--20.21.
The declaration docstring carries the node's complete seven-step proof plan,
including the Laurent-polynomial argument instead of testing reduced points.

Hypothesis and conclusion correspondence:

- The algebraically closed field F is `{F : Type u} [Field F] [IsAlgClosed F]`.
- F-group schemes are `Grp (Over (Spec (.of F)))`; their morphisms are bundled
  group-object homomorphisms. These reuse the recorded `CategoryTheory.GrpObj`
  group law and the upstream subgroup predicates.
- Reductivity is `hG : ReductiveTorusCentralizer.IsReductive G`, which includes
  affineness, finite type, smoothness and geometric connectedness. The maximal
  torus inclusion is `hT : ReductiveTorusCentralizer.IsMaximalTorus i`, including
  the closed-subgroup and torus conditions. No extra splitness is assumed.
- The presentations R and Q of the radical and its represented quotient are
  explicit parameters, not arbitrary substitutes: `hR` and `hQ` assert affine
  finite type; `hr` and `hrn` assert a closed normal inclusion; `hRs`, `hRc`,
  `hRsol` assert smoothness, connectedness and termination of the actual
  scheme-theoretic derived series. `hRmax` says that every smooth connected
  solvable closed normal subgroup factors through r, precisely the word
  “largest”. The subgroup candidates need no additional finite-type hypotheses:
  their closed immersions into affine finite-type G already imply them.
- `hq : IsFppfGroupQuotient r q` is the dependency's actual represented fppf
  sheaf quotient presentation, including kernel, torsor, local surjectivity and
  sheafification universal arrow. Thus the named Q is G/R(G), not a new quotient
  convention or an assumed map with unspecified kernel.
- `hrank` quantifies over every maximal torus inclusion into Q and asserts
  `topologicalKrullDim S.X.left = 1`, exactly the stated dimension condition.
  No non-vacuity or existence hypothesis is added: this is the node's universal
  assertion; existence follows mathematically for the affine smooth quotient.
- The conclusion chooses `Bplus`, `Bminus`, `bplus`, `bminus`; each inclusion
  satisfies the dependency `IsBorelGroupScheme`. Thus they are closed, smooth,
  connected, scheme-theoretically solvable and maximal. Closedness in affine
  finite-type G implies the ambient finite-type convention for these groups.
- Containing T is the existence of `tplus`, respectively `tminus`, with the
  exact factorization `tplus ≫ bplus = i`, respectively `tminus ≫ bminus = i`.
  Such maps are automatically closed subgroup inclusions since their composites
  with the closed embeddings are the given closed embedding of T.
- “Exactly two” consists of distinctness
  `¬ ∃ e : Bplus ≅ Bminus, e.hom ≫ bminus = bplus` and exhaustion: every Borel
  embedding b containing i admits an isomorphism to one of these two embeddings
  commuting with its map into G. This counts subgroups, not arbitrarily many
  presentations of an isomorphic domain; domain non-isomorphism is not claimed.
- Scheme-theoretic intersection is the literal equality of the two `Set.range`
  images' intersection with the `Set.range` image of i, in
  `StandardGroupSchemes.affine F A ⟶ G.X`, for every
  `(A : Type u) [CommRing A] [Algebra F A]`. These are precisely G(A), B±(A)
  and T(A). The common test-algebra universe is the field/scheme universe and
  includes coordinate algebras, so the condition detects the subgroup schemes.
- No assumption excludes nilpotents, the zero algebra, characteristic two, or
  central torus factors. There is no assertion about just F-valued points.

Dependency declarations used and inspected:

- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, `Grp` and the
  bundled group-object homomorphisms; upstream
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsSubgroupScheme`, `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`.
- `Mathlib.Algebra.Field.Defs`: `Field`;
  `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (the algebraic-closure
  dependency's recorded match explicitly supplies this predicate).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`. Their
  conjunction with `IsAffine` is reused through the recorded
  `SolvableGroupStructure.IsAlgebraic`.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `ReductiveTorusCentralizer.IsReductive` and `.IsMaximalTorus`. Read their full
  definitions and docstrings, including the algebraic-closure base change.
- `Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`:
  `IsFppfGroupQuotient` and `affine_normal_quotient_geometry`. The former supplies
  exactly the quotient notion introduced by that statement node.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Sheaf.AlgebraicGeometry.GroupScheme.Borel`: `IsBorelGroupScheme`; its public
  dependency `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple` supplies
  `IsSolvableGroupScheme`, `GroupSchemeDerivedLength`, `IsDerivedGroupScheme`.
  The actual derived-series definition is used, rather than abstract solvability
  of rational points or the other finite-series solvability predicate.
- Plain proof imports cover the currently stated proof dependencies:
  `PerfectSolvableUnipotentTorus`, `ReductiveTorusSelfCentralizer`,
  `CocharacterLimitSmoothStructure`, `MultiplicativeCharacterAntiduality`.
  The quotient module is already public for its use in the statement. The eight
  other proof dependencies have no recorded Lean declaration at this reading:
  connected-action-torus-rigidity, smooth-unipotent-solvable,
  reductive-semisimple-rank-formula, quotient-borel-torus-images,
  solvable-normal-subgroup-products, semisimple-rank-one-tangent-dimension,
  smooth-subgroup-tangent-generation, torus-normalizer-borel-transitivity
  (each with prefix `lem-sfb-`). No unstated proof dependency is needed to type
  this stage-2 statement; their steps remain in its proof docstring.

Edge cases checked before writing:

- For a torus G, R=G and the quotient is trivial; its maximal torus has dimension
  zero, so `hrank` fails. This excludes the rank-zero case without an extra
  hypothesis in the theorem.
- In SL2, the upper and lower triangular determinant-one matrices intersect in
  the diagonal matrices over every commutative algebra; vanishing of both
  off-diagonal entries works also for F[ε]/(ε²), and in characteristic two.
- Multiplying by a central torus preserves the asserted intersection and leaves
  the radical quotient rank one, so there is no accidental absolute-rank-one
  restriction.
- The zero F-algebra is allowed: all point sets are singletons and their images
  agree. Nilpotent algebras have no reducedness binder. No `CharZero` or
  invertibility of 2 is assumed.
- Distinct presentations of the same embedded Borel are identified by commuting
  isomorphisms. The chosen Borels may have isomorphic underlying group schemes;
  distinctness concerns their embeddings into G.

Searches (msearch.py, Q22 and this item):

- LeanFinder: “The scheme theoretic intersection of the two Borel subgroups
  containing a maximal torus of a reductive algebraic group of semisimple rank
  one is the torus”: eight hits, including root-pairing Cartan subalgebras,
  `frattini` and Lie-theoretic zero-root subalgebras; no group-scheme statement.
- Loogle: `"Borel"`: twelve hits, principally Lie algebra `borelLower`,
  `borelUpper`, and measure-theoretic Borelize declarations; none matches.
- LeanSearch: “Exactly two Borel subgroups contain a maximal torus in a reductive
  group of semisimple rank one”: eight unrelated dimension/index/Cartan-matrix
  results. A preceding longer query also returned unrelated results.
- Mathlib grep via msearch:
  `Borel.*[Ii]nter|[Ii]nter.*Borel|[Oo]pposite.*[Tt]orus`, AlgebraicGeometry:
  zero hits.
- `rg` of the project's `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` for the theorem name and opposite-Borel /
  Borel-intersection patterns finds centralizer intersection and root dichotomy
  modules, not the rank-one assertion. `grep -rn` for this item's id in
  `lean/WeilConjectures` finds no declaration. The supplied example Sheaf compact
  module is withdrawn; its node now points to the upstream compact-object module,
  which was read as the actual example.
- A supplementary search found the landed rank-one-root interfaces and their
  `HasSemisimpleRankOne`. It packages existential radical/quotient witnesses
  with the simpler `IsFppfQuotient`. This theorem instead exposes the witnesses
  explicitly to use the item's recorded `IsFppfGroupQuotient`, retaining exactly
  its universal dimension hypothesis; it declares no competing rank predicate.

There is no statement dispute, new node, dependency repair or statement correction.
Validation: scompile.py compiles the delivered module against the live published
library. Dry-run and delivery outcomes are recorded below after they complete.

## Second reading by Q22

This is a separate rereading by the same dispatched worker; the explicit launcher
instruction forbids starting other agents. It does not claim an independent
reviewer. The maintainer's independent delivery review remains to follow.

With the node and final file reopened, I checked the radical conditions individually:
closed, normal, smooth, connected, derived-series-solvable, and largest by
factorization; none is replaced by commutativity or torus status. Q has the actual
fppf sheaf quotient predicate. Its rank binder says “every maximal torus”, not a
chosen torus or an arbitrary dimension-three group. In the conclusion the two
Borel predicates each retain maximality, both contain the specified T, the
commuting-isomorphism test ensures distinct embedded subgroups, and exhaustion
quantifies over all Borel embeddings containing T. The range equality uses all
commutative test algebras, in the same G(A), not rational points. Checking the
Milne pp.412--415 source confirms these are the two claimed conclusions.
The only compile edit changed subscript plus/minus identifiers to ASCII names;
no mathematical clause changed. No mismatch was found in this rereading.

Validation result: the standalone scompile.py run compiled both sandbox and library
module names cleanly (1.8 seconds each). The prescribed deliver2.py --no-push
printed OK: dry-run commit cccc717f13e passes preflight and compiles. A direct JSON
comparison confirmed that `lean` is the only changed field of the item node.
