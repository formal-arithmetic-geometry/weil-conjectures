## Worker report

States `AlgebraicGeometry.maximal_parabolic_reflections` in
`Sheaf.AlgebraicGeometry.GroupScheme.MaximalParabolicReflections`. The only theorem
proof is `sorry`. There are no new definitions, dependency repairs, or statement
corrections. Source read: Milne, Algebraic Groups (2017), Proposition 21.88 and its
proof, printed p.452, and the opening of Lemma 22.24, p.469. The PDF was read by
pdftotext in the item's scratchpad. Proposition 21.88 explicitly quantifies over
every normalizer representative and assumes semisimplicity throughout this section.

Hypotheses and conclusions, clause by clause:

- Algebraically closed field: `{F : Type u} [Field F] [IsAlgClosed F]`.
- Group schemes over F: `G T B : Grp (Over (Spec (.of F)))`; their morphisms are
  group-scheme homomorphisms, not arbitrary maps of point sets.
- Smooth, connected, affine, finite type, semisimple G: `hG : IsSemisimpleGroupScheme
  G.X`. Its definition uses `Smooth`, `ConnectedSpace`, `IsAffine`,
  `LocallyOfFiniteType` plus `QuasiCompact`, and triviality of every smooth connected
  solvable normal closed subgroup. `IsSolvableGroupScheme` means termination of the
  scheme-theoretic derived series, rather than solvability only on field points.
- Split maximal torus: `iT : T ⟶ G`, `hT : IsMaximalTorus iT`, and `hsplit` giving
  an isomorphism to `splitTorus F m` for some natural m, including zero.
- Borel containing T: `iB`, `hB : IsBorelGroupScheme iB.hom.hom`, `j : T ⟶ B`,
  and `hj : j ≫ iB = iT`. The Borel predicate is maximal smooth connected solvable
  closed subgroup, with the same scheme-theoretic solvability convention.
- Roots, coroots, pairing and simple base as in the recorded Borel-pair node:
  the two `IsCommMonObj` witnesses provide the additive Hom-group structures;
  `aG`, `aB`, `haG`, `haB` specify actual conjugation actions; `Φ`, `P : RootDatum`,
  `b : P.Base`, `hroot`, `hpair`, `hΦ`, `hpos` are precisely the root-datum component
  of `reductive_borel_pair_structure`. In particular hpair fixes the integer
  pairing by composition of actual group-scheme morphisms, hΦ fixes all roots as
  exactly the nonzero adjoint character weights, and hpos fixes positivity from B.
  These data make explicit the node's phrase "as in" that dependency; no arbitrary
  root system or unrelated positivity is substituted. Finite-rank and reducedness
  facts need not be repeated as premises because the groups and actual root weights
  already determine them.
- Every simple index i: `∀ i : b.support`. This uses the simple roots themselves
  instead of an irrelevant enumeration α₁,...,αᵣ, and includes the empty base.
- Existence of smooth connected closed subgroup P_i: `∃ (H : Grp ...) (k : H ⟶ G)`
  followed by `IsClosedSubgroupScheme k.hom.hom`, `Smooth H.X.hom`,
  `ConnectedSpace H.X.left`.
- B ⊆ P_i: `∃ f : B ⟶ H, f ≫ k = iB`. This is factorization of subgroup schemes,
  not just inclusion of rational-point sets.
- P_i ≠ G: `¬ IsIso k`. A closed subgroup equals G exactly when its inclusion is
  an isomorphism. This imposes no properness condition on a morphism to the base.
- All other simple reflections: `∀ l : b.support, l ≠ i → ∀ n : normalizer iT`.
  `normalizer` is the existing scalar-extension normalizer on actual rational points.
  The antecedent `∃ e : T ≅ T, ...` says that conjugation by n restricts to e on T
  as a scheme morphism, and on every actual character its pullback is
  `χ - (P.toLinearMap χ (P.coroot l.val)) • P.root l.val`. This is precisely n
  representing the simple reflection. The usual Weyl action uses inverse
  conjugation; the two coincide here because a simple reflection is involutive
  (the root-coroot pairing is two). Characters separate morphisms of the split
  torus, so this criterion is equivalent to its class in N(F)/T(F) being s_l.
  The existential is part of the antecedent selecting representatives, not an
  assumption supplying an arbitrary action or excluding representatives.
- Membership n ∈ P_i(F): `n.val ∈ pointImage k (𝟙_ (Over (Spec (.of F))))`.
  The terminal test scheme is Spec F. Image membership is exactly existence of an
  F-rational lift through the subgroup embedding.
- No characteristic or simply connectedness hypotheses occur; u is explicit and
  arbitrary. All test algebras in the existing normalizer have the field's universe.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field`; Mathlib.FieldTheory.IsAlgClosed.Basic:
  `IsAlgClosed` (the recorded algebraic-closure node also names this predicate).
  Its definition by splitting is equivalent to the node's root condition.
- Mathlib.CategoryTheory.Monoidal.Grp: `Grp`, `GrpObj`; upstream
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs: `IsSubgroupScheme`,
  `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`. Their full definitions and
  docstrings were read; the group and closed subgroup nodes need no interface repair.
- Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure:
  `reductive_borel_pair_structure`, `semisimpleGroupScheme_isReductive`.
  Full signatures and proof docstrings read, including the actual character lattices,
  composition pairing and character weight conditions.
- Sheaf.AlgebraicGeometry.GroupScheme.Semisimple: `IsSemisimpleGroupScheme`,
  `IsSolvableGroupScheme`, `GroupSchemeDerivedLength`; GroupScheme.Borel:
  `IsBorelGroupScheme`; ReductiveTorusCentralizerTerminology: `IsMaximalTorus`.
- Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces: `normalizer`,
  `pointImage`, `torusInNormalizer`, `Weyl`; full definitions read. The already
  landed `def-sfb-rank-one-root-interfaces` is added to stmt_deps to record direct
  use of this terminology; no module or node is duplicated.
- Proof-only imports: ReductiveRootSubgroupParametrizations,
  BorelRootProductCoordinates, ReductiveRankOneReflections, and Mathlib's
  RootSystem.BaseExists (the recorded root-base-rational-integral-spans match).
  The first three full theorem statements and docstrings were read. The unstated
  proof-only nodes semisimple-roots-span and cocharacter-limit-smooth-structure
  currently have neither a Lean record nor a Mathlib match, hence have no module
  to import. Their five-step argument remains in the theorem docstring.

Edge cases checked before writing: an empty simple base gives no i; in rank one
P_i may be B and there is no other reflection condition. For SL3 the usual maximal
parabolic contains the other simple reflection and its entire torus coset. Every
representative is included, not merely a chosen lift. The trivial semisimple group
falls under the empty-base case. Characteristic two and characteristic dividing
the integral denominator-clearing factor cause no change: character weights are
integers, not tangent differentials. No perfection of the Killing form is assumed.
Nonreduced test algebras remain in the normalizer definition and conjugation is
an equality of actual scheme morphisms.

Searches actually run:

- msearch leanfinder: "A semisimple algebraic group has a proper parabolic containing
  a Borel and representatives of all but one simple reflection". Eight hits,
  including LieAlgebra.IsSemisimple.booleanGenerators, GeckConstruction and abstract
  Weyl induction; none states the subgroup-scheme assertion.
- msearch loogle: `"parabolic"`. Twelve hits, all the unrelated 2×2 matrix
  parabolic predicate and its lemmas.
- msearch grep: `parabolic|Parabolic` restricted to Mathlib GroupTheory. Zero hits.
- msearch leansearch: "A standard maximal parabolic subgroup contains the Borel
  and all other simple reflection representatives". Eight hits including
  CoxeterSystem.subgroup_closure_range_simple and RootPairing.weylGroup; no match.
- rg in lean/WeilConjectures and lean/Sheaf for `maximal_parabolic`,
  `parabolic.*reflection`, and the item id: no existing declaration of the item.
  Broader group-scheme searches identified the reused Borel-pair, semisimplicity,
  rank-one interfaces and StandardParabolicLeviCharts modules. The latter has
  extensive Levi/quotient geometry but does not state this normalizer-representative
  assertion. No duplicate definition is introduced.

Validation: scompile.py NM lem-sfb-maximal-parabolic-reflections on the delivered
file passed both sandbox and library mode (2.7 s and 2.9 s); no errors or unexpected
warnings. `set_option autoImplicit false` and `universe u` enforce explicit binders.
No statement dispute or source error found.

## Second reading by NM

Self-check by the assigned worker, not an independent agent: the dispatcher brief
forbids starting agents and delegates the independent reading to the maintainer.
I reread Milne 21.88, the DAG statement and the resulting signature. The main
checks were that b.support really selects simple roots, hΦ and hpos pin the
root datum to G and B rather than an arbitrary abstract datum, the representative
condition uses equality of scheme morphisms, and the subgroup is proper by
non-isomorphism of its embedding. The reflection direction agrees because the
reflection is involutive, and the terminal-scheme point image is precisely P_i(F).
All five original conclusion clauses are present. No change was needed after the
first successful compile. No independent review is claimed in this section.
