## Worker report

The module `Sheaf.AlgebraicGeometry.NormalMultiplicativeLayersCentral` states
`AlgebraicGeometry.normal_multiplicativeType_layers_central`, with its sole proof
`sorry`. No definitions, dependency repairs, new nodes, or statement corrections
are needed. The only change to the existing node is its `lean` record.

Source read: Milne, Algebraic Groups (2017), Lemma 16.43, printed p.340,
Corollaries 12.38 and 12.41, p.244, and Corollary 12.22, p.239. The proof
docstring preserves the node's eight steps, including centrality of N before
the corrected central-kernel argument, quotient-action descent, descent of the
difference family, and descent of centrality back to k. The current blueprint
unit `sk-thm-sf-ctf-stability/_section.md` and its direct-images proof were read;
the item's inherited supporting-lemma route is unchanged.

Hypothesis and conclusion correspondence:

| Node text | Lean rendering |
| --- | --- |
| k is a field | `{k : Type u} [Field k]` |
| All groups are k-group schemes | `G N E Q : Grp (Over (Spec (.of k)))` bundles each scheme over Spec k and its group structure; all displayed arrows are group homomorphisms. |
| All groups are affine and of finite type | `hG`, `hN`, `hE`, `hQ : SolvableGroupStructure.IsAlgebraic ...`; this predicate is exactly `IsAffine ... ∧ LocallyOfFiniteType ... ∧ QuasiCompact ...`. |
| G is connected | `hconnected : ConnectedSpace G.X.left` includes nonemptiness. |
| N is contained in E, which is contained in G; all subgroups are closed | `i : N ⟶ E`, `j : E ⟶ G`, with `hi` and `hj : IsClosedSubgroupScheme ...`; the composite is the inclusion of N in G. |
| N and E are both normal in G | `hNnormal : IsNormalSubgroupScheme (i ≫ j).hom.hom` and `hEnormal : IsNormalSubgroupScheme j.hom.hom`. Normality of N is in G, not merely in E. |
| q represents the fppf quotient E/N | `q : E ⟶ Q` and `hq : SolvableGroupStructure.IsFppfQuotient i.hom.hom q`. The existing predicate says flat, surjective, locally finitely presented, and specifies an isomorphism of N with the scheme-theoretic kernel commuting with its inclusion. Its docstring explains the represented-sheaf quotient identification. |
| N and Q are of multiplicative type | `hNmult` and `hQmult : MultiplicativeType.IsMultiplicativeType ...`; the existing predicate is a closed subgroup inclusion into `splitTorus (AlgebraicClosure k) n` for some natural n. |
| E is of multiplicative type | First conjunct `MultiplicativeType.IsMultiplicativeType E`. |
| E is contained in Z(G) | Second conjunct: every `e : StandardGroupSchemes.affine k A ⟶ E.X` has `e ≫ j.hom.hom ∈ ReductiveTorusCentralizer.centralizerPoints (𝟙 G) A`. The recorded centre theorem identifies this subfunctor with Z(G). |
| Explicit commutation after every A-algebra extension | Unfolding `centralizerPoints` quantifies over every commutative k-algebra B, every `f : A →ₐ[k] B`, and every `t : StandardGroupSchemes.affine k B ⟶ G.X`, and asserts `Commute (StandardGroupSchemes.map k f ≫ (e ≫ j.hom.hom)) (t ≫ (𝟙 G).hom.hom)`. A k-algebra map A→B is exactly an A-algebra extension with its induced k-structure. |
| No smoothness, perfectness, or connectedness assumptions on N,E,Q | None of these occurs among the binders or inside the predicates used. |

Dependency declarations read and reused:

- `Mathlib.Algebra.Field.Defs`: `Field` (inherited through imports).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` and
  `CategoryTheory.Grp` for group schemes and bundled group homomorphisms.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsSubgroupScheme`, `IsClosedSubgroupScheme`, and
  `IsNormalSubgroupScheme`, whose algebra-point signatures and docstrings were read.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `LocallyOfFiniteType` and
  `QuasiCompact`, the finite-type components used by `IsAlgebraic`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`,
  underlying closed subgroup inclusions.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`;
  `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosure`, `IsAlgClosed`.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `MultiplicativeType.baseChange`, `splitTorus`, `IsMultiplicativeType`;
  rank zero is the actual monoidal-unit group object.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`:
  `StandardGroupSchemes.affine`, `map`, `multiplicative`, `multiplicativeGroup`.
  The split torus uses the existing Laurent-polynomial multiplicative group.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `Sheaf.AlgebraicGeometry.SolvableGroupStructure`:
  `SolvableGroupStructure.IsAlgebraic`, `IsFppfQuotient`.
- `Sheaf.AlgebraicGeometry.AffineGroupCentreBaseChange`:
  `exists_affine_group_centre_baseChange`, which uses
  `ReductiveTorusCentralizer.centralizerPoints` defined in the publicly imported
  `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`. Its full
  all-algebras definition was read and is used directly, without a second centre
  definition or an arbitrarily selected representing subgroup.

Plain proof imports retain the stated proof-dependency modules: affine flatness,
faithfully flat spectrum criteria and base change, affine pullbacks, the fpqc
precoverage, its axioms and subcanonicity, the recorded base-change conventions,
`ConnectedPointGeometricallyConnected`, `CommutativeMultiplicativeTypeExtension`,
and the field-extension tensor-injectivity module. Statement dependencies which
also occur in the proof are public imports. The two proof nodes
`lem-sfb-split-torus-subgroups-diagonalizable` and
`lem-sfb-diagonalizable-hom-family-rigidity` have no recorded Lean module on the
read base, so there is no module to import for them; their proof uses are retained
in the docstring and DAG.

Edge cases checked before writing:

- N=E, with Q trivial, is allowed. The theorem then specializes to centrality of
  a normal multiplicative-type subgroup. N trivial, E trivial, and rank-zero tori
  are allowed by the same binders; there are no positivity hypotheses on ranks.
- Nonreduced multiplicative-type kernels such as μ_p in characteristic p remain
  included: closed immersions and the kernel condition are scheme-theoretic,
  and centrality tests every algebra rather than only geometric points.
- Disconnected N, E, or Q and imperfect k remain included. The only connectedness
  requirement is on G, matching Milne 16.43. The disconnected normalizer of a
  torus illustrates why this requirement on G must not be dropped.
- The empty scheme cannot be a group scheme over a field, due to its unit
  section, and ConnectedSpace expressly excludes emptiness.
- All universe variables and binders are explicit (`set_option autoImplicit false`).
  The universe-polymorphic statement follows the recorded scheme/test-algebra
  convention `Type u`; testing arbitrary algebra extensions in that universe
  detects the universal affine conjugation identity, and thus the centre as a
  subgroup scheme. No equality between previously independent universes is imposed.

Duplicate searches actually run:

- `msearch.py`, LeanFinder: “A normal subgroup of a connected affine group scheme
  with multiplicative type kernel and quotient is central and of multiplicative
  type”. Eight hits, including `upperCentralSeriesStep_eq_comap_center` and
  `GroupExtension.normal_inl_range`; these concern abstract groups, not this
  group-scheme statement.
- `msearch.py`, LeanSearch: “A normal subgroup of a connected algebraic group with
  multiplicative type kernel and quotient is central and of multiplicative type”.
  Eight hits, including `Subgroup.instNormalCenter`, `QuotientGroup.ker_mk'`, and
  `Subgroup.normal_centralizer`; none states the scheme-theoretic assertion.
- `msearch.py`, Loogle: `"GroupScheme", "center"`; zero hits.
- `msearch.py`, Mathlib grep in AlgebraicGeometry:
  `multiplicative.type|diagonaliz.*normal|normal.*diagonaliz`; zero hits.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and the upstream-name index:
  `multiplicative.*layers|layers.*central|16\.43|normal_multiplicative|lem-sfb-normal-multiplicative-layers-central`;
  no existing statement. The explicit node-id grep in `lean/WeilConjectures`
  likewise found none.
- Further `rg` for `IsMultiplicativeType|IsFppfQuotient|centralizerPoints` in
  `lean/Sheaf/AlgebraicGeometry` found the dependency definitions and related
  centralizer/structure statements, which were reused. A search for
  `normal.*multiplicative|multiplicative.*normal` in `lean/WeilConjectures` found
  no alternative upstream statement.

No statement dispute or node fault was found. The historical CompactObject
example is now a withdrawn module on the read base; this delivery follows the
current module-mode header rules and the active dependency modules instead.

Validation: the prescribed `scompile.py` checks this single file against the live
published build, with only the expected declaration-uses-sorry warning permitted.
The first check caught a nested-comment delimiter in a docstring's ASCII Laurent
exponent notation; this was replaced by the mathematical ± glyph without changing
the statement. The final dry run and delivery run perform the required preflight
and repeat the file compile.

## Second reading by Q87

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
