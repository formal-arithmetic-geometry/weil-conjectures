## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.RankOneReductiveGeneration` states
`AlgebraicGeometry.rankOne_reductive_generation`. Its only theorem has proof `sorry`.
The separate definition module `GeometricCoroot` has real Prop-valued data and no theorem
or sorry. The original statement and proof plan are unchanged. The item's stmt_deps gains
`def-sfb-geometric-coroot`, for the previously unbundled geometric coroot relation.

I read the complete item and its seven proof steps, every statement dependency's node,
and the recorded declarations and their docstrings. I read Milne's Theorem 23.31 and
Remark 23.33 (printed p.494), the preceding description of T_alpha and G_alpha, and
Theorem 21.11(d),(e) (pp.428--430). The current blueprint ancestor returned by
`python3 tools/blueprint_refs.py ancestor lem-sfb-rank-one-reductive-generation` is null;
the new node preserves that ancestor and prepends this item to the inherited via chain.

Hypothesis and clause correspondence:

- Algebraically closed F: `{F : Type u} [Field F] [IsAlgClosed F]`, using the Mathlib
  declarations recorded by def-weil-field and def-weil-algebraic-closure. No characteristic
  restriction is imposed.
- H and T are actual F-group schemes: `H T : Grp (Over (Spec (.of F)))`. `hH` is the
  existing `SolvableGroupStructure.IsAlgebraic H`, namely affine, locally of finite type
  and quasi-compact. `hsm` and `hconn` supply smoothness and connectedness of H.
- The torus inclusion is `iT : T ⟶ H`; `hT` is the existing closed maximal-torus
  predicate. `hsplit` gives an isomorphism with `MultiplicativeType.splitTorus F r`
  for some natural r, including zero. The explicit `IsCommMonObj` witnesses express
  the commutativity inherent in a torus and G_m. They are Prop-valued structure witnesses,
  not extra mathematical restrictions: commutativity transports along the split-torus
  isomorphism. The upstream Borel-pair interface uses the same witnesses to expose the
  additive Hom lattices.
- X is `Additive (RankOneRoots.Character T)` and Y is the analogous additive cocharacter
  Hom group. These abbreviations are the actual group-scheme Hom sets. `P.toLinearMap`
  in the conclusion is pinned by the composition-power identity, for every character
  and cocharacter, to the integer pairing in the node. The finite-module clauses are
  the lattice mixins required for Mathlib's RootDatum; they follow from the given split
  torus and retain all central torus directions.
- `D : Finset X` is the finite set, `hDzero` excludes zero, and `hDind` is Z-linear
  independence of the subtype-indexed inclusion into X.
- `J`, `jH`, `tJ`, `hJclosed`, `hJred`, `hJtorus` and `hJinc` give the closed split
  reductive rank-one subgroups with the very same torus T. Splitness follows from
  `hsplit`; smoothness and geometric connectedness are included in the recorded
  reductivity predicate. Over the algebraically closed base, geometric connectedness
  and the geometric unipotent-radical condition are equivalent to the node's conventions.
- `aJ` and `haJ` specify the conjugation actions. `hJroots` says their nonzero tangent
  character weights are exactly alpha and negative alpha. These are characters, not
  differentials of characters, so no roots are lost in characteristic two or p.
- `c` and `hc` specify the actual geometric coroots of these pairs, by the local Weyl
  reflection characterization in Theorem 21.11(d),(e). Pairing two alone would not
  identify the central component; the new definition retains the local centralizer.
- `U alpha true/false` and `uJ` are the two root groups. `hU` says they are closed,
  smooth, connected, T-stable and have tangent image the corresponding root weight
  space, exactly the characterization in the recorded root-subgroup theorem. Its
  uniqueness identifies these with the canonical root groups and implies their G_a
  parametrizations, so no arbitrary unipotent subgroup is substituted.
- `hcomm` is Commute of the two universal point morphisms on
  `U alpha false × U beta true`, mapped into H, for all distinct alpha,beta. Thus the
  commutator morphism is the unit morphism on the whole product scheme, not just on
  F-points or geometric points.
- The existential `G,gH,tG,jG` gives a closed subgroup containing T and every J_alpha,
  with the specified factorization identities. The universal `K,kH` clause gives
  minimality among ALL closed subgroup schemes containing them, including nonreduced
  subgroups; it adds no smoothness, reducedness or connectedness condition on K.
  Factorization uniqueness follows from the closed immersion kH.
- `Smooth G.X.hom`, `ConnectedSpace G.X.left`, the existing IsReductive predicate and
  `IsMaximalTorus tG` give the asserted smooth connected split reductive structure.
  The given split torus remains T itself. The finite root set Phi and reduced RootDatum
  P have exactly the actual character weights (`aG`, its conjugation identity, and
  the root membership equivalence). P.root is the inclusion of Phi into X.
- The support clause says exactly that the simple roots indexed by `b.support` are D;
  the existing `RootPairing.Base` supplies independence and the same-sign integral
  expansions. No spanning of the entire character lattice is required.
- Every P.coroot is pinned to its geometric coroot predicate, and the alpha/rho clause
  says the coroot of every original alpha is its given c_alpha.
- The final universal K,kG,tK,aK clause covers ANY split reductive closed rank-one
  subgroup of G with maximal torus T and roots ±rho for any rho of G. Every geometric
  coroot d in K equals `(P.coroot rho).toMul`. It is not restricted to the given J's,
  to simple roots, or to a chosen Borel.
- `D = ∅ → IsIso tG` explicitly identifies the generated subgroup with T in the empty
  case. The containment identity makes this an identification over H.

Dependency declarations used:

- Mathlib.Algebra.Field.Defs: `Field`.
- Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosed`.
- Mathlib.CategoryTheory.Monoidal.Grp: `CategoryTheory.GrpObj`, `CategoryTheory.Grp`;
  Mathlib.CategoryTheory.Monoidal.Mon: `CategoryTheory.IsCommMonObj`.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Defs:
  `AlgebraicGeometry.IsClosedSubgroupScheme`, with actual bundled homomorphisms.
- Sheaf.AlgebraicGeometry.StandardGroupSchemes: `multiplicative`, `multiplicativeGroup`,
  `affine`, and the additive group appearing in the imported root-subgroup theorem.
- Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure:
  `AlgebraicGeometry.reductive_borel_pair_structure`, whose signature spells out the
  character/cocharacter Hom lattices, integer pairing, reduced root datum and base.
- Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations:
  `AlgebraicGeometry.TorusCharacterTangent.reductive_root_subgroup_parametrizations`,
  supplying the exact closed/smooth/connected/stable/tangent-image characterization.
- Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology: `IsReductive`,
  `IsMaximalTorus`, `centralizerPoints` (all in namespace ReductiveTorusCentralizer).
- Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights: `weightSpace`, `IsStable`.
- Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces: `Character`, `Cocharacter`,
  `roots`, `weight`, `adjointMap`, `pointImage`, `normalizer` (namespace RankOneRoots).
- Sheaf.AlgebraicGeometry.ToriMultiplicativeType: `splitTorus`, `IsLargestSubtorus`.
- Sheaf.AlgebraicGeometry.SolvableGroupStructure: `IsAlgebraic`, and the smooth matrix
  geometric unipotence notion used through the existing reductivity predicate.
- Mathlib.LinearAlgebra.RootSystem.Defs/Base/Reduced: `RootDatum`, `RootPairing.Base`,
  `RootPairing.IsReduced`.

All stated proof-dependency modules are imported, with plain imports where only the
proof plan uses them. The Mathlib matches for smoothness, connected components of
geometrically connected products, and smoothness of geometrically reduced group schemes
are imported as well. Still-unstated proof nodes are named in the docstring and are not
restated here: solvable-normal-subgroup-products, contracting-rank-one-cell,
simple-root-limit-retractions, triangular-reflection-orbits,
triangular-root-subgroup-detection, simple-root-generation-mixed-commutation,
smooth-unipotent-solvable and solvable-proper-fixed-point. None is a statement prerequisite.

Edge cases checked: D empty; the trivial rank-zero torus; nontrivial central torus
factors; singleton D (mixed commutation is vacuous); characteristic two (opposite
characters are still distinct in the integer character lattice); all positive
characteristics; arbitrary nonreduced test algebras; arbitrary closed competitor
subgroup schemes. The field, schemes, and algebras use the common explicit universe u,
so test algebras are not in a potentially smaller independent universe. Every universe
and variable is explicitly bound, and both modules disable autoImplicit.

Searches made through the prescribed msearch.py wrapper (raw results are copied into
the new node's mathlib_searches, and the wrapper saved searches.jsonl):

- LeanFinder: compatible rank-one reductive algebraic subgroups generating a reductive
  group. Eight hits in abstract root systems/GeckConstruction; no group-scheme theorem.
- Loogle: `"coroot"`. Twelve hits, beginning with LieAlgebra.corootSpace and
  LieAlgebra.IsKilling.coroot. Those are Lie algebra elements, not cocharacters.
- Mathlib grep: `IsCoroot|rankOne.*generat|rank_one.*generat|reductive` in
  AlgebraicGeometry. No hits.
- LeanSearch: geometric coroot characterized by the local normalizer reflection.
  Eight abstract RootPairing/LieAlgebra hits; no geometric coroot predicate.
- LeanFinder: `coroot cocharacter algebraic group normalizer reflection centralizer
  kernel root`. Eight abstract root-pairing/Lie-algebra hits; no group-scheme predicate.
- Project rg over lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for
  `IsCoroot|rankOne.*generat|rank_one.*generat`: only unrelated derived-module rank-one
  generators. Searching the item id in WeilConjectures gives no hit.
- Further project searches for coroot/characterization found the existing
  `redutive_rankOne_reflections` statement (spelled `reductive_rankOne_reflections`
  in Lean), whose full signature and docstring were read. It states existence with
  all geometric data, but defines no reusable coroot relation. The new predicate
  packages its source's local-reflection characterization without restating the theorem.
- DAG `rg -l` for geometric-coroot/coroot-characterization terms found only unrelated
  normalization, lattice and Frobenius nodes. `tools/blueprint_refs.py search coroot`
  reported zero matching blueprint nodes. No existing definition node carries this
  predicate. The existing rank-one-root-interfaces definition gives normalizers,
  characters, cocharacters and SL2Hom, but not the coroot relation.

Validation: both delivered modules compiled individually in dependency order through
scompile.py, including both sandbox and actual library module names, with no errors or
warnings. One initial syntax error from the reserved MonObj gamma token was repaired
by renaming the root index to rho. There is one postponed theorem and no other sorry.
No statement dispute or source correction was needed.

## New nodes

`def-sfb-geometric-coroot` defines `AlgebraicGeometry.RankOneRoots.IsGeometricCoroot` in
`Sheaf.AlgebraicGeometry.GroupScheme.GeometricCoroot`. Its source is Milne,
Theorem 21.11(d),(e), pp.428--430. It requires a nontrivial character, pairing two,
and the reflection identity from an actual normalizing rational point in the
scheme-theoretic centralizer of the largest subtorus of the character kernel.
The relation uses the existing character, cocharacter, universal normalizer,
point-image, largest-subtorus and scalar-extension centralizer definitions.
The searches above found neither an existing predicate nor another definition node
for it. This extra node is needed to give both coroot assertions their geometric
meaning; an arbitrary abstract root datum on the correct root set would not suffice.
All data of the predicate is written in full, with no choice of a group or map and
no postponed proof. Its normalizer-centralizer condition and reflection formula are
identities over every test algebra, so infinitesimal behavior is retained.

## Second reading by Q25

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
