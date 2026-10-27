## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.BorelOppositeRootDichotomy` states
`AlgebraicGeometry.RankOneRoots.borel_opposite_root_dichotomy`, with one `sorry`
and no other declarations. No proof is supplied in stage 2. The declaration's
docstring carries all five DAG proof steps, including their dependency IDs.

Source checked: Milne, Algebraic Groups (2017), printed pp.428--429
(Theorem 21.11(b),(c)), p.433 (Lemma 21.28), and p.434 (proof of Proposition
21.29). The PDF is present locally; its text was read using pdftotext. Lemma
21.28 gives the root-group dichotomy, Theorem 21.11(c) translates inclusion of
root groups into inclusion of their Lie spaces, and Proposition 21.29 explicitly
uses the resulting Lie-space dichotomy. No source correction is needed.

Hypotheses and objects, clause by clause:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
  There is no characteristic hypothesis.
- `G T B : Grp (Over (Spec (.of F)))` are actual group schemes; `iT`, `iB`,
  and `j` are group-scheme homomorphisms. `hG : IsReductive G` includes affine
  finite type, smoothness, geometric connectedness, and absence of nontrivial
  smooth connected normal unipotent subgroups. Over the algebraically closed
  field this is the node's reductivity convention. Its unipotence is the existing
  faithful-matrix geometric unipotence predicate, not abstract group solvability.
- `hT : IsMaximalTorus iT` includes the closed subgroup condition, the torus
  condition, and maximality by factorization of closed torus inclusions. The
  existing geometric split-torus definition is equivalent to the node's split
  definition over algebraically closed F. Rank zero is allowed.
- `hB : IsBorelGroupScheme iB.hom.hom` includes closed subgroup, smoothness,
  connectedness, scheme-theoretic derived-series solvability, and maximality.
  B and T inherit affine finite type as closed subgroups of G. These consequences
  are not additional assumptions.
- `hj : j ≫ iB = iT` expresses that the specified B contains the specified T.
  The factorization j is unique because iB is a closed immersion.
- `∃ a : ModObj T.X G.X, a.smul = adjointMap iT ∧ ...` supplies the internal
  conjugation action, pinned to the explicit conjugation morphism from the
  existing interface. Thus a is not an arbitrary representation or additional
  action assumption. `weight T G a χ` differentiates that action on dual-number
  tangent points. It uses actual characters `χ : Character T`, never their
  differentials. `GrpObj.Lie` and `GrpObj.differential` are the upstream tangent
  space and tangent homomorphism.

Conclusions, clause by clause:

- `roots T G a` is exactly the nontrivial torus characters whose weight spaces
  are nonzero. `(roots T G a).Finite` is finiteness of Φ.
- `∀ α ∈ roots T G a, ∃ β ∈ roots T G a, β.hom.hom = α.hom.hom⁻¹`
  says that the inverse character (additive notation -α) is a root. Equality of
  the underlying morphisms is equality of characters, since the bundled
  homomorphism structure is propositional.
- Every occurrence of Ψ_B is written explicitly as the subtype
  `{χ : Character T // χ ∈ roots T G a ∧ weight T G a χ ≤
  (GrpObj.differential iB.hom.hom).toLinearMap.range}`. Its membership is
  precisely root-space containment in Lie(B).
- `iSupIndep` of the family indexed by `Option Ψ_B` expresses the internal
  direct sum: `none` is the range of the tangent map from T, and `some χ` is
  the χ-weight space in Lie(G). The following equality says that Lie(B),
  identified with its tangent-map range, equals Lie(T) plus the supremum over
  Ψ_B. Independence plus equality is the displayed direct-sum assertion;
  a supremum alone would not express its directness.
- The final `Set.ncard ... = 1` is exactly the cardinality of
  Ψ_B intersected with {α,-α}. The condition in braces includes root membership,
  containment in Lie(B), and equality to α or its inverse character. This set
  is finite by root finiteness, so ncard is ordinary finite cardinality.

Dependency declarations read and reused:

- Mathlib.Algebra.Field.Defs: `Field`.
- Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosed`; the algebraic-closure
  node also records `AlgebraicClosure`/`IsAlgClosure`, but F itself, rather than
  an extension chosen for F, is the field in this statement.
- Mathlib.CategoryTheory.Monoidal.Grp: `GrpObj`, `Grp` and bundled morphisms.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Defs:
  `IsClosedSubgroupScheme`, `IsSubgroupScheme`, `IsNormalSubgroupScheme`.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: `LocallyOfFiniteType`;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: `QuasiCompact`.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth`.
- Mathlib.Topology.Connected.Basic: `ConnectedSpace`.
- Sheaf.AlgebraicGeometry.StandardGroupSchemes: `multiplicative`, its Laurent
  coordinate group structure and `affine` test schemes.
- Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology:
  `ReductiveTorusCentralizer.IsReductive`, `IsMaximalTorus`.
- Sheaf.AlgebraicGeometry.GroupScheme.Borel: `IsBorelGroupScheme`, reusing
  `IsSolvableGroupScheme` from Sheaf.AlgebraicGeometry.GroupScheme.Semisimple.
- Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces:
  `RankOneRoots.Character`, `weight`, `roots`, `adjointMap`.
- Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights: `weightSpace`.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Basic / Lie.Differential:
  `GrpObj.Lie`, `GrpObj.differential` (ranges identify closed-subgroup tangents).
- Mathlib.Order.SupIndep: `iSupIndep`; Mathlib.Data.Set.Card: `Set.ncard`.

Four existing, already recorded definition nodes were added to stmt_deps:
`def-sfb-rank-one-root-interfaces`, `def-sfb-borel-subgroup-scheme`,
`def-sfb-reductive-torus-centralizer-terminology`, and
`def-sfb-torus-character-tangent-weights`. Their modules and full definitions
were read. This uses the rule allowing additions of landed statement dependencies;
there is no new definition, dependency repair, or change to the mathematical statement.

The stated proof dependencies are imported with plain `import`:
ReductiveRankOneReflections, TorusCentralizerBorelIntersection,
MultiplicativeCharacterAntiduality, and upstream ProjectiveSpace. The local
records for `lem-sfb-split-rank-one-classification` and
`lem-sfb-solvable-proper-fixed-point` currently have no Lean module; neither is
needed to type the statement, so their imports await their statements. Their
proof-dependency IDs and uses remain intact, and are named in the proof docstring.

Edge cases checked before writing: Φ empty (a torus, including the trivial
rank-zero group) reduces the direct sum to Lie(B)=Lie(T); the `Option` index
still contains its toral summand. Characteristic two does not identify inverse
characters even when their differentials coincide (SL2 has weights ±2χ).
PGL2 tangent directions survive modulo scalar matrices in characteristic two.
Central torus factors and B=G when G is a torus are included. No independent
small universe of test algebras is imposed; every group, base field and tangent
space uses the shared universe u, as in the recorded interfaces.

Searches for an existing statement (msearch.py, group Q20, this item):

- leanfinder: "A Borel subgroup of a reductive group containing a maximal torus
  has exactly one of each pair of opposite character root spaces in its Lie
  algebra". Eight hits, including RootPairing.GeckConstruction and
  LieAlgebra.IsKilling declarations. No group-scheme result; the Killing API
  requires extra assumptions, including characteristic zero in several hits.
- leansearch: "The Lie algebra of a Borel subgroup contains precisely one of
  each pair of opposite torus character root spaces". Eight hits in abstract
  Lie-algebra root theory, including `LieAlgebra.rootSpace` and
  `cartan_sup_iSup_rootSpace_eq_top`. No exact arbitrary-characteristic result.
- loogle: `"Borel", "root"`. Zero hits.
- grep: `Borel|borel|IsBorel`, Mathlib/AlgebraicGeometry. Zero hits.
- rg in lean/WeilConjectures and lean/Sheaf for Borel/opposite/root-dichotomy:
  no existing declaration of this theorem. Sheaf has the component notions and
  other statements about Borel pairs; those were reused. The exact node-ID
  search in WeilConjectures found no declaration. DAG searches found the four
  definition nodes above, avoiding any new private copy.

Validation: scompile.py compiled the module in both sandbox and library mode
against the live published server library, with no errors or warnings (4.1 s
and 3.9 s respectively). `set_option autoImplicit false` enforces explicit
binders. No STATEMENT-DISPUTED flag or node fault is present.

## Second reading by Q20

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
