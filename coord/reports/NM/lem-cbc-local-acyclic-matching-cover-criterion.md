## Worker report

The module `Sheaf.CategoryTheory.LocalAcyclicMatchingCoverCriterion` states
`CategoryTheory.LocalSimplicialPresheaf.local_acyclic_of_matching_cover` with its
whole proof postponed by `sorry`. Its docstring gives all eight proof steps from
the node. No definition or theorem is reproved or copied.

Source checked: [Dugger--Hollander--Isaksen, Section 3, Proposition 3.2 and (3.4)]
(https://arxiv.org/html/math/0205027v2#S3), converse direction. This is the stated
objectwise Kan specialization. The node's proof also follows Dugger--Isaksen,
arXiv:math/0205025, Theorem 6.15(a) and Proposition 7.2, with the explicit finite
cell, finite zigzag and covering-sieve arguments retained in the docstring.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Small category and size convention | Explicit `universe u w`, `{C : Type u} [SmallCategory C]`, values `SSet.{max u w}`. The site and its arrows are small, while the values may lie in any larger universe. No automatic implicit variables. |
| Topology specified by sieves, maximality, pullback stability and transitivity | `(J : GrothendieckTopology C)`, Mathlib's actual Grothendieck topology structure. |
| Simplicial presheaves F and G | `(F G : Cᵒᵖ ⥤ SSet.{max u w})`; `SSet` is the recorded Mathlib functor definition. |
| Every F(V) and G(V) fills all positive-dimensional horns | `hF : ∀ V : C, SSet.KanComplex (F.obj (op V))` and `hG` with G. Read `KanComplex` and `KanComplex.hornFilling` in Mathlib. |
| A map f from F to G | `(f : F ⟶ G)`, a natural transformation. |
| F_n(V) = F(V)_n | The existing `degreePresheaf F n` is F followed by evaluation at `[n]`. |
| Unaugmented matching object Hom(boundary simplex, F(V)), likewise G | Existing `boundaryPresheaf F n` is F followed by coyoneda on the actual `SSet.boundary n`; likewise G. |
| Canonical map to the relative matching pullback | Existing `relativeBoundaryMatchingMap f n` is `pullback.lift` of `boundaryRestriction F n` and the degree-n component of f. The former is boundary inclusion followed by `SSet.yonedaEquiv.symm`. The compatibility proof is naturality of Yoneda. No arbitrary comparison map is supplied. |
| A generalized cover in every n ≥ 0 | `hcover : ∀ n : ℕ, Presheaf.IsLocallySurjective J (relativeBoundaryMatchingMap f n)`. Mathlib's image sieve consists exactly of arrows where the restricted target section has a preimage. |
| f is a local Kan fibration | First conjunct `IsLocalKanFibration J f`, the recorded dependency definition. It quantifies over V, horns of dimension n+1 and every horn index, then a covering sieve with independent strict fillers on every arrow. |
| f is a local weak equivalence on associated π₀ sheaves | Second conjunct `IsLocalWeakEquivalence J f`, whose first clause is `IsIso ((presheafToSheaf J (Type (max u w))).map (whiskerRight f SSet.π₀Functor))`. |
| All positive pointed homotopy sheaves on C/V are isomorphic | The remaining clauses of `IsLocalWeakEquivalence` are local surjectivity and local injectivity of the recorded `Pi` and `piMap` for every V, vertex and degree n+1. These are the dependency node's explicit equivalent slice-sheaf convention. Quantifying over all objects and vertices includes every restriction in every slice. `HEq` in the dependency identifies only basepoints equal by naturality. The local-bijection sheafification criterion gives precisely the stated sheaf isomorphisms. |
| Degree-zero hypothesis is local surjectivity F₀ → G₀ | The all-n hypothesis includes n=0. `SSet.boundary 0` is empty, its map into either value is unique, so the relative pullback is G₀ and the matching map is f₀ under this canonical identification. No augmented matching convention or n>0 restriction is used. |
| h_V tensored lifting-square formulation | The dependency uses the objectwise formulation: Yoneda sends a map h_V × K → F to K → F(V), with restriction along r acting by F(r). Thus it has exactly the same squares and independent fillers. |

Dependency declarations read and used:

- `def-weil-size-convention` is explicitly marked a convention, with no Lean
  declaration; rendered by the explicit universes above.
- `def-weil-pbc-simplicial-set`: `SSet`, `SSet.degenerate`,
  `SSet.nonDegenerate`, `SSet.Subcomplex`, `SSet.Finite` in Mathlib's
  `AlgebraicTopology.SimplicialSet.Basic`, `.Degenerate`, `.Subcomplex`, `.Finite`.
- `def-weil-pbc-sheafification`: `CategoryTheory.presheafToSheaf`,
  `CategoryTheory.toSheafify`, `CategoryTheory.sheafificationAdjunction` in
  `Mathlib.CategoryTheory.Sites.Sheafification`, through the local-map definitions.
- `def-cbc-generalized-cover`: `CategoryTheory.Presheaf.IsLocallySurjective`
  and its actual `imageSieve` in `Mathlib.CategoryTheory.Sites.LocallySurjective`.
- `def-cbc-local-simplicial-presheaf-maps`: `Pi`, `piMap`,
  `IsLocalKanFibration`, `IsLocalWeakEquivalence` in
  `Sheaf.CategoryTheory.LocalSimplicialPresheafMaps`, namespace
  `CategoryTheory.LocalSimplicialPresheaf`. Read the full source and signatures.
- Added landed node `lem-cbc-local-acyclic-matching-generalized-cover` to
  `stmt_deps` solely to reuse its existing `degreePresheaf`, `boundaryPresheaf`,
  `boundaryRestriction`, `boundaryPresheafMap`, `relativeBoundaryMatchingMap`.
  Its module is `Sheaf.CategoryTheory.LocalAcyclicMatchingGeneralizedCover`.
  Its converse-direction theorem is not assumed or applied here. Reading its
  complete helper bodies confirmed exactly the required canonical construction.
  A traversal of all statement/proof edges found no path from that dependency
  back to this item, so this addition creates no dependency cycle.
- Proof-only Mathlib inputs are imported without `public`:
  `Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd` (`SSet.instFiniteTensorObj`,
  the match for `lem-cbc-finite-simplicial-product`), `.Skeleton`
  (`SSet.relativeCellComplexOfMono`, the match for
  `lem-coef-infinity-monomorphism-boundary-cells`), and
  `Mathlib.CategoryTheory.Sites.LocallyBijective`
  (`CategoryTheory.GrothendieckTopology.W_iff_isLocallyBijective`, combined with
  `W_iff` from `.Localization`, the match for
  `lem-cbc-set-presheaf-sheafification-local-bijection`). These full signatures
  were read, and the associated proof steps are in the theorem docstring.

Edge cases checked before writing: n=0 and empty boundary; n=1 with both horns;
m=1 and all basepoints; empty site (all requirements vacuous); empty values
(the degree-zero hypothesis detects any failure to lift vertices); empty
covering sieves (independent fillers are vacuous, consistently with sheafification);
the topology with only maximal covers (identity arrows yield strict fillers);
finite inclusion with empty domain or A=B; zero-length homotopy zigzags (use a
constant cylinder/degenerate edge); arbitrary value universe w. None is excluded
or requires an extra hypothesis. The source theorem is consistent with the
statement. No STATEMENT-DISPUTED finding or statement correction.

Searches performed on 2026-10-17 (all through prescribed wrappers where applicable):

- `msearch.py ... leanfinder "A map of objectwise Kan simplicial presheaves with locally surjective relative boundary matching maps is a local Kan fibration and local weak equivalence"`:
  eight hits, including `SSet.modelCategoryQuillen.J`, `.I`, `.fibration_iff`
  and ordinary lifting results; none states the local-presheaf theorem.
- `msearch.py ... loogle "SSet.modelCategoryQuillen.fibration_iff"`:
  one hit, ordinary Kan fibrations only.
- `msearch.py ... grep "local.*(acyclic|fibration)|relative.*matching"`:
  seven hits in derived-category files about localization of acyclic complexes;
  no simplicial-presheaf criterion.
- `msearch.py ... leansearch "A simplicial presheaf map with locally surjective relative boundary matching maps is a local acyclic fibration"`:
  eight hits, on ordinary local surjectivity, including
  `GrothendieckTopology.W.isLocallySurjective`; none is the item.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and
  `/home/ubuntu/weil-newtargets-shared/lean/Sheaf`, using
  `local.*(acyclic|fibration)|relative.*matching|lem-cbc-local-acyclic-matching-cover-criterion`:
  no upstream match; side hits include the converse-direction module and unrelated
  Reedy/derived results. The converse module supplies the exact matching-map
  helpers and is reused. No theorem states this direction.
- `rg` in `dag/lean_names_upstream.json`, upstream and side CategoryTheory using
  `matching_cover_criterion|relativeBoundaryMatchingMap|local_acyclic_matching`:
  only the existing side matching-map helpers and converse theorem, no collision
  with the new theorem name.

Only the item's `lean` and `stmt_deps` fields changed. No new nodes or dependency
repairs are needed. Validation uses `scompile.py` for the delivered file and then
`deliver2.py NM lem-cbc-local-acyclic-matching-cover-criterion --no-push`.


## Second reading by NM

I independently read the node's complete statement and eight proof steps, its
sandbox module, every statement dependency's node and recorded declaration, and
the proof-dependency signatures. There is no repair note for this item. This
reading found no mathematical mismatch: the theorem says exactly the node's
objectwise Kan specialization of the boundary-cover criterion.

Source checked directly: Dugger--Hollander--Isaksen,
[Section 3, Proposition 3.2 and equation (3.4)]
(https://arxiv.org/html/math/0205027v2#S3), together with Section 2's small-site
setup; and Dugger--Isaksen,
[Section 6.5, Definition 6.6, Lemma 6.8, Proposition 6.9, Theorem 6.15(a),
and Proposition 7.2](https://arxiv.org/html/math/0205025v1).
There is no Stacks source for this node. DHI's result allows arbitrary simplicial
presheaves; the node explicitly states its objectwise Kan specialization. The
source imposes no enough-points, subcanonical, finite-limit, or objectwise
fibration assumption. DI Proposition 6.9 justifies omitting Ex-infinity for
objectwise Kan values, and Lemma 6.8 gives the local-bijection interpretation.

The following is my inventory of all objects, hypotheses, and conclusion clauses,
with the actual Lean rendering and verdict for each.

| Node item | Lean rendering checked | Verdict |
| --- | --- | --- |
| Small category, size convention | `{C : Type u} [SmallCategory C]`, explicit `universe u w` | Exact small-site convention; no hidden instance. |
| Grothendieck topology, with sieve axioms | `(J : GrothendieckTopology C)` | Exact Mathlib sieve topology, with maximality, stability, transitivity. |
| Two simplicial presheaves | `(F G : Cᵒᵖ ⥤ SSet.{max u w})` | Same objects. `SSet` in Mathlib Basic is the functor category on the opposite simplex category. |
| Objectwise Kan property of F | `(hF : ∀ V : C, SSet.KanComplex (F.obj (op V)))` | Exact; Mathlib `KanComplex.hornFilling` covers dimensions `n+1` and every `Fin (n+2)` horn. |
| Objectwise Kan property of G | The analogous binder `hG` | Exact, with no condition on f being an objectwise fibration. |
| The given morphism | `(f : F ⟶ G)` | Natural transformation, as required. |
| Representable h_V and objectwise restrictions | Existing `IsLocalKanFibration` quantifies over maps into `F.obj (op V)` and restrictions by `F.map r.op` | Exact by the Yoneda correspondence for `h_V × K`; independent fillers on a sieve are retained. |
| Standard simplex, unaugmented boundary, horns | Actual Mathlib `SSet.stdSimplex`, `SSet.boundary`, `SSet.horn` inside the imported definitions | Correct objects; no augmented matching object substituted. |
| Degree presheaf F_n | Existing `degreePresheaf F n` evaluates F at `op ⦋n⦌` | Exact. |
| Matching presheaves of F and G | Existing `boundaryPresheaf F n`, `boundaryPresheaf G n`, using coyoneda on `SSet.boundary n` | Exactly maps from the boundary, with restriction by postcomposition. |
| Canonical relative matching arrow | Existing `relativeBoundaryMatchingMap f n` | Its explicit `pullback.lift` projections are boundary restriction and f in degree n. The equality is naturality of Yoneda. No arbitrary map or extra choice hypothesis. |
| Generalized covers in every degree n ≥ 0 | `hcover : ∀ n : ℕ, Presheaf.IsLocallySurjective J (relativeBoundaryMatchingMap f n)` | Exact. Mathlib `imageSieve` consists of precisely the arrows where the restricted section has a preimage. |
| Conclusion: local Kan fibration | `IsLocalKanFibration J f`, first conjunct | Exact local horn lifting with all positive dimensions and no compatibility requirement. |
| Conclusion: isomorphism on associated component sheaves | Component clause of `IsLocalWeakEquivalence J f` is `IsIso ((presheafToSheaf J (Type (max u w))).map (whiskerRight f SSet.π₀Functor))` | Exact. Mathlib π₀ is the quotient by the relation generated by edges. |
| Conclusion: all positive pointed homotopy sheaves on C/V | Positive clauses of `IsLocalWeakEquivalence J f`, quantifying over every V, vertex x, and n+1 | Exact equivalent local-bijection form. For a fixed basepoint on V, apply the clauses at W to its restriction along every W → V. Conversely each condition on V is recovered at the identity object of C/V. |
| Correct homotopy sets and induced maps | Existing `Pi` and `piMap` in `LocalSimplicialPresheafMaps` | Read Mathlib `RelativeMorphism`, `Homotopy`, `HomotopyClass`, and postcomposition. These are simplices constant on the boundary modulo the equivalence relation generated by relative cylinder homotopies. Naturality alone identifies target basepoints via HEq. |
| Degree-zero interpretation | The n=0 instance of `hcover` | Exact: the boundary is empty, both matching presheaves terminal, and the pullback canonically identifies with G₀. The arrow then is f₀. |

Dependency audit: I read the entire landed
`Sheaf.CategoryTheory.LocalAcyclicMatchingGeneralizedCover` module, including
all five helper bodies and the opposite-direction theorem. Its helpers have no
Kan, local-fibration, or local-equivalence hypotheses, so using them does not
assume the conclusion here. The added statement dependency is legitimate reuse
of a landed node. I also read the entire landed
`Sheaf.CategoryTheory.LocalSimplicialPresheafMaps` module against its definition
node. Its definitions have real data, including actual homotopy quotients and
postcomposition maps. The sheafification and generalized-cover dependencies are
the recorded Mathlib notions, not private substitutes. The size dependency is
explicitly a metatheoretic convention. The proof-only imports provide the finite
product result, boundary-cell construction, and locally-bijective sheafification
criterion; their signatures have the expected hypotheses. There are no new
nodes or dependency modules in this delivery, and no statement correction to
audit against citers.

Edge cases checked independently:

- n=0 is included and yields local surjectivity on vertices; n=1 includes both
  horns. Positive homotopy degrees are exactly n+1, so degree one is included.
- The empty category is allowed. Empty values and the terminal simplicial set
  are allowed; there is no `Nonempty` binder. If F is empty and G has vertices,
  the degree-zero cover hypothesis imposes the necessary local lifting condition.
- Empty covering sieves are allowed precisely when J declares them covering;
  both local lifting and sheafification then have their usual vacuous behavior.
  A topology with only maximal covers includes identity restrictions, as needed.
- Finite cell and homotopy arguments include empty domains, equal subcomplexes,
  and zero-length zigzags, addressed explicitly by the proof docstring.
- There are no rings, characteristics, schemes, or nonempty indexing families to
  restrict. The site universe u is arbitrary, and `max u w` allows values in any
  chosen common containing universe, without equating site and value universes.
  All variables and universe levels are explicitly bound; no automatic implicit
  variable supplies a hidden hypothesis.

Independent H4 searches, performed through the prescribed wrappers on 2026-10-17:

- LeanFinder: "A morphism of simplicial presheaves with locally solvable boundary
  extension problems is a local weak equivalence and local fibration". Eight
  results, including `SSet.modelCategoryQuillen.J`, `fibration_iff` and ordinary
  model-category lifting statements; none is this theorem on a site.
- LeanSearch: "Locally surjective relative matching maps imply isomorphisms of
  homotopy sheaves for simplicial presheaves". Eight results on locally
  surjective presheaf/sheaf maps and the sheafification localization, including
  `Presheaf.isLocallySurjective_of_iso`; none states the simplicial criterion.
- Independent rg in upstream `WeilConjectures`, Mathlib AlgebraicTopology and
  CategoryTheory/Sites, and side `lean/Sheaf`, using
  `local.{0,30}(acyclic|kan|fibration)|boundary.{0,25}matching|matching.{0,25}cover`.
  Results included the existing converse and local-map definitions and unrelated
  locally Kan simplicial categories, Bousfield localization and geometric local
  acyclicity. These are different notions or directions. A focused rg over all
  Mathlib, upstream, side modules and `dag/lean_names_upstream.json` for
  `local_acyclic_of_matching_cover|relativeBoundaryMatchingMap|local_acyclic_matching`
  found only the landed converse module and canonical helpers. Thus no exact
  declaration is available to replace this module, and the theorem name does
  not collide.

H5/H6/H8/H9 audit: the delivered file adds one theorem, whose entire proof is
`sorry`; it adds no definitions, helper theorems, instances, or private notation.
The source and blueprint tags are present on the module and theorem. The
statement docstring follows each of the node's eight proof steps, including the
sieve induction, finite zigzag construction, basepoint naturality, and slice
sheafification argument. All Lean lines are at most 100 characters; the imports
are the statement's interface and recorded proof inputs.

Changes in this second reading: no change to the mathematical node statement,
Lean signature, proof docstring, imports, or dependency list was warranted.
The recorded `lean.statement` had exactly the signature's tokens with whitespace
collapsed; I made it literally equal to the multiline signature in the file,
as requested by the brief. This report section is the other change.

Validation: `scompile.py NM lem-cbc-local-acyclic-matching-cover-criterion`
compiled the sandbox and delivered module cleanly (1.8 seconds each), with no
errors or warnings. The dry run and delivery use the prescribed `deliver2.py`
wrapper; their results are recorded below.

Dry run result: `deliver2.py NM lem-cbc-local-acyclic-matching-cover-criterion --no-push`
printed `OK (dry run): commit 38e20638af passes the preflight and compiles; nothing pushed`.
