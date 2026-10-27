## Worker report

This delivery states `AlgebraicGeometry.BottSamelson.bottSamelson_gallery_geometry`
in `Sheaf.AlgebraicGeometry.GroupScheme.BottSamelsonGalleryGeometry`. Its proof is
`sorry`. The only helper, `BottSamelson.previous`, is the explicit preceding-coordinate
function with the initial coordinate equal to 1; its data is fully defined. There are
no new independent notions, dependency replacements, or statement corrections. The
node copy differs from the repository only in `lean`.

Source read: Brion--Kumar, *Frobenius Splitting Methods*, 2.2.1, printed pp.64--66,
equations (1)--(8), open-cell and subsequence paragraphs; the opening of 2.2 expressly
allows characteristic zero for 2.2.1--2.2.2. Author-hosted source:
https://www-fourier.univ-grenoble-alpes.fr/~mbrion/fbook.pdf (PDF pp.73--75).
The six-step proof in the declaration follows every proof step of the node, including
its additional fixed-fibre induction and the separate empty-word convention. The
current blueprint ancestor and the node's source/proof were read; this is a supporting
node, not the unit's own statement.

Hypotheses and clauses, in source order:

| Node | Lean rendering |
| --- | --- |
| Algebraically closed field F | `{F : Type u} [Field F] [IsAlgClosed F]` |
| Group scheme over F | `Grp (Over (Spec (.of F)))`; products, inverses, units and maps are the existing internal group structures |
| Smooth, connected, affine, finite type, no smooth connected solvable normal subgroup | `hG : IsSemisimpleGroupScheme G.X`, using the actual scheme-theoretic derived-series definition |
| Simply connected, including finite nonreduced central kernels | `hsc` quantifies semisimple `G'`, group maps `f`, `Surjective f.left`, `IsFinite (GrpObj.ker f).hom`, and commutation of every kernel point with every group point over every F-algebra |
| Split maximal torus in a Borel | `iT`, `hT`, `hsplit`, `iB`, `hB`, `j`, `hj`; the commutativity witnesses are the ones furnished by the Borel-pair interface |
| Actual character roots, positive roots, simple roots | `aG`, `aB`, `haG`, `haB`, `Φ`, `D`, `base`, `hred`, `hroot`, `hpair`, `hΦ`, `hpos` pin the exact root datum, pairing and character weight spaces from the dependency |
| Root subgroups Uα | `U`, `iU`, `hU` use the recorded closed smooth connected stable root-subgroup characterization and exact tangent weight spaces |
| Q = G/B | `Q`, `π`, `hQ`, `hπflat`, `hπsurj`, `hπinv`, `hπtorsor` are the proper finite-type right B-torsor interface of the dependency |
| W = normalizer / T(F), representatives | actual `RankOneRoots.Weyl iT`, `RankOneRoots.normalizer iT`, `n`, `hn`; `act` and `hact` pin conjugation on the actual torus |
| Simple reflections s_i | `s : base.support → RankOneRoots.Weyl iT`, with `hs` identifying the action on every character with `D.reflection` |
| Arbitrary finite word, with no reducedness requirement | `m : ℕ`, `word : Fin m → base.support` |
| Generated closed subgroups P_i | existential `P`, `iP`, `bP`; contains B and U_{-α}, and factors through every closed subgroup containing those same subgroups |
| Two disjoint double cosets after every algebraically closed extension | the `pointImage` set equality and `Disjoint` clause, with literal B n_s B formulas over `K` |
| Twisted right B^m-action on the product | existential `ρ`, whose coordinates on every test scheme are `(previous b k)⁻¹ * p_k * b_k`; `previous` is 1 in the first slot |
| Represented fppf quotient Z | `Presheaf.IsSheaf` on `Scheme.fppfTopology.over (Spec F)`, and `ηq` from the presheaf coequalizer of `yoneda.map (fst _ _)` and `yoneda.map ρ` universal for maps into every Type-u fppf sheaf; this is precisely sheafification of the orbit presheaf |
| Smooth integral projective over F | `Smooth Z.hom ∧ IsIntegral Z.left ∧ IsProjective Z.hom` |
| Empty word gives Spec F | `m = 0 → Nonempty (Z ≅ 𝟙_ (Over (Spec F)))`; the terminal over-object is Spec F over itself |
| Successive Zariski locally trivial P1-fibrations | finite `tower`, transition maps `f`, terminal initial stage and final-stage isomorphism to Z; each point has an open neighborhood `v` and an isomorphism from the pulled-back fibration to `ProjectiveLine V` commuting with the projection to V |
| Multiplication endpoint | `endpoint : Z ⟶ Q`, with the equation on every test scheme `p ≫ q ≫ endpoint = (List.ofFn (...p_k...)).prod ≫ π` |
| Proper endpoint | `IsProper endpoint.left` |
| B action on first factor and equivariance | `aZ`, first-coordinate `p'` formula, `aQ` pinned to left multiplication on G/B, and `aZ.smul ≫ endpoint = (𝟙 B.X ⊗ₘ endpoint) ≫ aQ.smul` |
| Open dense locus of all open double-coset factors | `O`, `o`, `IsOpenImmersion o.left`, `DenseRange o.left`, and the iff for tuple K-points with every factor in B n_s B |
| Isomorphic to A_F^m | `Nonempty (O ≅ Over.mk (AffineSpace (ULift (Fin m)) (Spec F) ↘ Spec F))`; this is the recorded affine-space construction, over F |
| Reduced-word condition ℓ(w)=m | every list of simple reflections with the same product has length at least m; no reducedness hypothesis is imposed on the other clauses |
| Reduced-word image of the open locus is C_w | under that length condition, a Q(K)-point lifts to O iff it is b n_w B, for every algebraically closed K/F; this is the node proof's explicitly pointwise image formulation |
| Fixed classes indexed by ε_j in {0,1} | `c : (Fin m → Bool) → Hom(Spec K,Z)`, injective, each c ε represented by factors 1 or the chosen n_s |
| Exactly the fixed points, fixed after all scalar extensions | the iff quantifies every `A : Over (Spec F)`, map `f : A ⟶ Spec K`, and `t : A ⟶ T.X`; this includes every commutative K-algebra extension and its nonreduced cases |
| Exactly 2^m such points | injectivity and the exact range iff give a bijection between the fixed points and the Boolean m-cube, whose cardinality is 2^m |
| Endpoints e_(product of selected reflections) | the last equation uses the ordered product in the actual Weyl group and the chosen representative `n`, composed with π |
| Every characteristic | no characteristic assumption; fixedness is through full torus character points, not differentials |

Dependency declarations read and reused:

- `Field` in Mathlib.Algebra.Field.Defs and `IsAlgClosed` in
  Mathlib.FieldTheory.IsAlgClosed.Basic; the algebraic-closure node's recorded
  `AlgebraicClosure`/`IsAlgClosure` interface was read (F itself is already closed).
- `CategoryTheory.GrpObj` / `Grp` in Mathlib.CategoryTheory.Monoidal.Grp;
  the group-scheme interpretation and kernels in
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `AlgebraicGeometry.reductive_borel_pair_structure` and
  `semisimpleGroupScheme_isReductive` in
  Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure.
- `AlgebraicGeometry.bruhat_longest_cell_charts` in
  Sheaf.AlgebraicGeometry.GroupScheme.BruhatLongestCellCharts.
- `RankOneRoots.reductive_rankOne_reflections` in
  Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections; actual characters,
  normalizer, point images and Weyl quotient from its recorded
  Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces.
- `TorusCharacterTangent.reductive_root_subgroup_parametrizations` in
  Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations.
- `IsSemisimpleGroupScheme` in Sheaf.AlgebraicGeometry.GroupScheme.Semisimple,
  reached through the existing rank-one and Borel-pair dependencies.
- `AlgebraicGeometry.ProjectiveSpace` / `ProjectiveLine` in
  WeilConjectures.AlgebraicGeometry.ProjectiveSpace;
  `AffineSpace` in Mathlib.AlgebraicGeometry.AffineSpace.
- `IsProjective` in WeilConjectures.AlgebraicGeometry.Morphisms.Projective;
  `IsProper` in Mathlib.AlgebraicGeometry.Morphisms.Proper;
  `Smooth` in Mathlib.AlgebraicGeometry.Morphisms.Smooth;
  `IsIntegral` in Mathlib.AlgebraicGeometry.Properties.

Proof imports: standard_parabolic_levi_charts, projective_base_change and
IsHProjective.comp in their recorded modules. Proper and smooth base-change,
smooth composition, projective-space properness, fibre products and
IsProper.of_comp are in the already imported Mathlib/upstream modules. The proof-only
nodes lem-sfb-minimal-parabolic-flag-projection and
lem-sfb-simple-bruhat-double-coset-product currently have no recorded Lean module;
they are named in the proof plan and no substitute result is assumed as a hypothesis.

Edge cases checked before writing and again after compilation:

- m = 0: the tuple and B-products are terminal, the ordered products are 1,
  the tower has just its initial/final stage, affine 0-space is Spec F, and the
  Boolean cube is a singleton with endpoint B. The left B-action is trivial.
- Rank zero/trivial G: base.support is empty, so only the empty word can exist;
  the empty-word assertions remain valid, and P_i clauses are vacuous.
- SL2, m = 1: Z is P1, its open locus is A1, and its two fixed flags have
  endpoints B and n_s B. The image assertion concerns O, not the whole proper Z.
- Repeated word (s,s): the quotient is still an iterated P1-fibration, O is A2,
  there are four fixed galleries (two can share an endpoint), and the reduced
  image implication does not apply. No identification of galleries by endpoint.
- Positive characteristic including two: full characters, finite nonreduced kernels,
  and all test schemes are retained. No restriction on root differentials.
- The scheme and coefficient universe is explicitly u; test fields and algebras use
  that same universe, as do the recorded dependencies. u is arbitrary. No independent
  smaller test universe or auto-bound parameter is present.

Searches made using the prescribed msearch.py wrapper:

- leanfinder: `Bott Samelson gallery variety smooth projective torus fixed points
  subexpressions` returned 8 unrelated root-pairing results (EmbeddedG2,
  chainBotCoeff_mul_chainTopCoeff, span_orbit_eq_top, etc.); no variety statement.
- loogle: `"Bott"` returned 12 unrelated bottom/syntax names, no match.
- grep Mathlib: `Bott.Samelson|gallery|Schubert` returned only the art-gallery comment
  in Analysis/Convex/Visible.lean; no match.
- leansearch: `Bott Samelson variety iterated projective line bundles torus fixed
  galleries` returned 8 unrelated group-action, root, Coxeter and vector-bundle
  declarations; no matching algebraic-geometric statement.
- `rg` in both lean/WeilConjectures and lean/Sheaf for
  `Bott.Samelson|bott.Samelson|gallery|Gallery` found no matching declaration;
  the node-id search in lean/WeilConjectures also found none.
- DAG search confirmed that semisimplicity and the actual normalizer/root interfaces
  already have owning nodes; no duplicate definition node was introduced.

Validation: scompile.py compiled this file as a sandbox and as its named library
module against the live published library, with no errors or warnings, within 60 s
(the successful initial statement compile took 27.8 s and 9.8 s respectively).
Final imports and delivery packet are validated again by the required dry run.
No STATEMENT-DISPUTED flag or node fault was found.

## Second reading by NS

This dispatcher assignment forbids starting other agents; this section records the
worker's separate clause-by-clause rereading, not an independent reviewer claim.
The maintainer's independent review follows delivery.

Reopened the original JSON and final Lean file. The table above matches each binder
and every conclusion clause. In particular checked the initial b-coordinate is 1,
subsequent coordinates use b_(j-1), products are List.ofFn ordered products rather
than commutative products, all maps and isomorphisms are over F, and local P1
trivializations commute with projections. Checked that the quotient universal
property uses the twisted ρ rather than ordinary coordinatewise multiplication.
The open-image clause is conditional only there on reducedness and uses b n_w B;
the fixed range is exact and injective, retaining distinct galleries with equal
endpoints. The universal fixedness quantifier includes nonreduced K-algebras.
The helper and all hypotheses reuse dependency notions. No mathematical mismatch
or source correction was found. During compilation the endpoint binder was renamed
from a reserved notation token and explicit quantifier parentheses were repaired;
these were syntax repairs only.
