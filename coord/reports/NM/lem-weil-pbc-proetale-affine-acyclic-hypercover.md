## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover` states
`AlgebraicGeometry.Scheme.ProEt.exists_affine_weaklyContractible_hypercover`, with
`sorry` as its whole proof. No definition or proof is added. The natural-language
statement is unchanged. The existing landed node
`lem-weil-pbc-simplicial-matching-object` is added to `stmt_deps` because its actual
boundary diagram is used, rather than creating another matching-object definition.
No new node and no replacement dependency module is needed.

Source checked: `literature/stacks-project/proetale.tex`, label
`lemma-w-contractible-hypercovering`, clause (2) and its proof (Tag 09A1);
`sites.tex`, labels `lemma-w-contractible` and `definition-w-contractible`
(Tags 090K and 090L). Clause (2) constructs finite families in the qcqs subsite,
then replaces them with finite disjoint unions. The docstring records all four
steps of the node's proof, including the full-site evaluation argument.

Hypothesis and clause mapping:

- The arbitrary scheme is `(X : Scheme.{u})`. No affine, qcqs, Noetherian or
  separated hypothesis is imposed on X.
- The small pro-etale object is `(W : X.ProEt)`. Mathlib's objects are weakly
  etale morphisms to X. The topology is `Scheme.ProEt.topology X` throughout.
- The underlying W is qcqs exactly through `[CompactSpace W.left]` and
  `[QuasiSeparatedSpace W.left]`. These are properties of W, not its arrow to X.
- The augmented simplicial object is `U : SimplicialObject (Over W)`.
  Its terms carry their augmentation in `.hom`; every simplicial operator is a
  slice morphism and hence commutes with it. Functoriality is exactly the
  simplicial face and degeneracy identities. This is equivalent to a simplicial
  object of the site with a natural augmentation to the constant W object.
- Affineness of every degree p is `∀ n, IsAffine (U _⦋n⦌).left.left`.
- Weak contractibility is the second conjunct: for every degree and every
  `f : F ⟶ G` of `Sheaf (topology X) (Type (u + 1))`, `Epi f` implies
  `Function.Surjective (f.hom.app (op (U _⦋n⦌).left))`. These are sheaves on
  the full X site, not on the qcqs subsite or the slice site.
- In degree zero the matching map is precisely the augmentation;
  `Epi ((topology X).yoneda.map (U _⦋0⦌).hom)` has target h_W.
- In degree one, `c : Fan (fun _ : Fin 2 ↦ U _⦋0⦌)` with
  `Nonempty (IsLimit c)` is the product in `Over W`, so its represented sheaf
  is h_U0 ×_(h_W) h_U0. The morphism μ is tied to both faces by
  `∀ i, μ ≫ c.proj i = U.δ i`. Its represented sheaf map is required to be epi.
- In every degree n+2, c is the limit of the existing
  `(SimplicialObject.matchingBoundaryIndex U n).multicospan`, formed in `Over W`.
  This finite diagram has n+3 codimension-one faces with the pairwise overlap
  maps. Its cones are exactly compatible face tuples; lower proper faces are
  then determined by composing face maps. It is the finite presentation of the
  proper-face matching limit, not the unaugmented matching limit over X.
  The equations at every `WalkingMulticospan.left i` determine the matching
  morphism μ, and `Epi ((topology X).yoneda.map μ.left)` is the required epi.
- Representables are exactly `(topology X).yoneda`, whose underlying presheaf
  is `CategoryTheory.yoneda`, i.e. Hom_X(-,V). Subcanonicity of the small
  pro-etale site is supplied by Mathlib. Finite limits in the site slice exist;
  representable sheaves preserve finite limits, as does their induced slice
  functor to sheaves over h_W. Thus choosing matching cones in the site slice
  imposes no additional geometric hypothesis: their Yoneda images are exactly
  the node's sheaf matching objects. Any choices of limit cone differ by the
  canonical isomorphism and give the same epimorphism condition.

Dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `Scheme.Hom`; read their complete structures.
- `def-weil-pbc-proetale-site`: imported recorded module
  `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`; read its recorded
  `Scheme.proEtaleDerivedCategory` definition and docstring. The present
  statement uses only its site, `Scheme.ProEt` and `Scheme.ProEt.topology`,
  whose definitions were read in `Mathlib.AlgebraicGeometry.Sites.Proetale`.
  No coefficient or derived-category notion is needed here.
- `def-weil-size-convention`: convention-only record, no declaration/module;
  explicit universe u and set-valued sheaves in Type (u+1) implement it.
- `def-weil-pbc-scheme-conventions`: convention-only record, no declaration/module;
  the named Mathlib properties `CompactSpace`, `QuasiSeparatedSpace`, and `IsAffine`
  implement the clauses needed here. No second conventions bundle is introduced.
- `def-weil-pbc-simplicial-object`: `Mathlib.AlgebraicTopology.SimplicialObject.Basic`,
  `CategoryTheory.SimplicialObject`, `.δ` and `.σ`. Read all full signatures.
- Added landed dependency `lem-weil-pbc-simplicial-matching-object`:
  `Sheaf.CategoryTheory.SimplicialMatchingObject`, declarations
  `CategoryTheory.SimplicialObject.matchingBoundaryShape` and `matchingBoundaryIndex`.
  Read the entire module, including its zero, one and higher-degree statements.
  Only its actual diagram construction is used; none of its sorry proofs is needed
  to define a term in this statement.
- All four proof dependency nodes were inspected for Lean records; none had one,
  so no unavailable proof-dependency import was added. Their names and proof roles
  are nevertheless all recorded in the theorem docstring.
- Read `coord/pefw-upstream-framework.md` and searched the exact framework under
  the group clone's `lean/WeilConjectures`. No module-object framework substitute
  is needed: this is entirely a theorem about the small site and set-valued sheaves.

Edge cases checked:

- Degree zero is not a product over X: it is h_W itself.
- Degree one is a product in Over W, and hence a fibre product over h_W.
  For disconnected W, it does not introduce pairs with different augmentations.
- n=0 in the final clause means degree two: three faces, with one compatibility
  relation for each of their three pairs. No missing low degree or off-by-one case.
- W empty is permitted by both qcqs hypotheses. Constant empty terms are affine;
  sheaf evaluation at the empty object is a singleton and the epi requirements hold.
- Empty finite families in the source proof give singleton products of sections,
  so the weak-contractibility argument also covers them.
- No independent small test universe makes the quantification vacuous; full-site
  sheaves live in Type (u+1), the standard universe for this site encoding.

Searches made (via msearch.py for this group/item):

- leanfinder, query `Every quasi compact quasi separated pro etale scheme has an
  affine weakly contractible hypercover`: eight hits, including
  `AlgebraicGeometry.QuasiCompactCover`, `quasiCompactCover_iff`, and
  `Scheme.exists_isOpenCover_and_isAffine`. None gives an all-degree weakly
  contractible pro-etale hypercover.
- loogle, query `"hypercover"`: twelve hits, on `PreZeroHypercover` and
  `Precoverage.ZeroHypercover` (including their finite-level helpers).
  None states this theorem or provides an all-degree hypercover definition.
- grep, query `hypercover|weaklyContractible`: twenty-five returned hits, on
  finite-level hypercovers and related sheaf/geometry APIs. No match.
- Local rg over Mathlib, the slopmaster2 `WeilConjectures`, the group's exact
  `lean/WeilConjectures`, and `lean/Sheaf` inspected hypercover, matching and
  weak-contractibility names. The existing generic `SimplicialMatchingObject`
  module provides the needed boundary diagram. The existing
  `IsSemiRepresentableHypercover` is specifically for formal families of
  etale objects and is not a definition for this pro-etale assertion.
- rg for the item id in upstream `WeilConjectures`: no match.
- rg for `exists_affine_weaklyContractible_hypercover` in all four source trees:
  no existing name or statement match.

Validation: server-only scompile.py compiled the delivered module cleanly in
1.5 seconds, nice 19, two threads, 60-second per-file limit. No local Lean or
Lake command was run. All binders and the universe are explicit. There are no
warnings, node corrections, disputed statements, new definitions, or hollow data.

## Second reading by NM

Independent reading against the sandbox node, Stacks proetale.tex
`lemma-w-contractible-hypercovering` (09A1), especially clause (2) and its
qcqs-subsite proof, and sites.tex `lemma-w-contractible` (090K) and
`definition-w-contractible` (090L). The source starts with an arbitrary scheme;
there is no ambient Noetherian, separated, characteristic, or affine assumption.

Object/hypothesis/conclusion checklist (all verdicts: exact):

1. Scheme X: `(X : Scheme.{u})`. Read Mathlib's `Scheme` structure and `Scheme.Hom`:
   locally ringed spaces locally isomorphic to affine spectra, and their morphisms.
2. Full small pro-etale site and its object W: `(W : X.ProEt)`, with `topology X`.
   Opened the recorded `ProEtaleDerivedCategory` module and Mathlib's Proetale module.
   `Scheme.ProEt` is the category of weakly etale schemes over X, with all X-morphisms;
   its topology is the pulled-back weakly-etale fpqc topology and is subcanonical.
   No coefficient or derived-category restriction from that dependency is imposed.
3. W quasi-compact and quasi-separated: `[CompactSpace W.left]` and
   `[QuasiSeparatedSpace W.left]`. These concern the underlying scheme W, not its map
   to X. Read the topological quasi-separated class and the scheme conventions record.
4. Universe convention: explicit `universe u`, `Scheme.{u}`, and sheaves valued in
   `Type (u + 1)`. The site and its Hom sets fit the larger universe. There is no
   independently smaller test universe and no restriction to finite or nonempty schemes.
5. Augmented simplicial object: `∃ U : SimplicialObject (Over W)`. Read the recorded
   simplicial-object node and Mathlib's functor definition, delta and sigma signatures.
   A functor to this slice is precisely a simplicial site object with compatible
   augmentation to W. Functoriality includes every face/degeneracy identity and each
   slice-morphism condition gives commutation with augmentation.
6. Every term affine: `∀ n : ℕ, IsAffine (U _⦋n⦌).left.left`. The two projections
   forget first the slice augmentation and then the map to X. Mathlib's `IsAffine`
   requires the canonical map to the spectrum of global sections to be an isomorphism.
7. Every term weakly contractible: the second conjunct quantifies over every degree,
   every pair of full-site set sheaves F,G and every morphism f, requiring `Epi f →
   Function.Surjective (f.hom.app (op (U _⦋n⦌).left))`. This is exactly 090K(2),
   rather than a test only on the qcqs subsite or on sheaves over W.
8. Degree-zero matching sheaf h_W: `Epi ((topology X).yoneda.map (U _⦋0⦌).hom)`.
   The map is the actual augmentation from the slice object, with exactly target W.
9. Degree-one matching sheaf h_U0 ×_(h_W) h_U0: a limiting two-legged `Fan` in
   `Over W`, and a morphism mu from U_1 satisfying both face projection equations.
   Its represented underlying site map `mu.left` is required to be epi.
10. Each higher matching sheaf: for every n, a limiting cone on
    `(SimplicialObject.matchingBoundaryIndex U n).multicospan` in `Over W`, and a
    map from U_(n+2) whose n+3 face projections are exactly `U.δ i`, with represented
    map epi. Opened the entire recorded matching-object dependency module and node:
    its left objects are U_(n+1), pair objects U_n, arrows d_(j-1) and d_i for i<j.
    The displayed Fin.pred and Fin.castLT indices implement precisely those arrows.
    Compatible codimension-one faces determine every lower proper face; this is the
    proper-face matching limit. No extra compatibility or missing face is introduced.
11. Representable sheaves: `(topology X).yoneda` is the subcanonical Yoneda embedding,
    with underlying presheaf Hom_X(-,V). Read its section equivalence and
    `preservesLimitsOfSize_yoneda`. Since the site has finite limits (read the
    derived instance on ProEt), so does its slice. Yoneda and the induced slice
    functor preserve the matching limits. Thus choosing representing site cones
    instead of sheaf cones adds no hypothesis or stronger conclusion. Epimorphisms
    in the sheaf slice and in the underlying sheaf category agree.

Edge cases: empty W and empty X are allowed, with constant empty simplicial terms;
empty schemes are affine (zero ring allowed). Evaluation at the empty object is a
singleton, so no nonemptiness assumption is hidden in weak contractibility. Degree
zero and degree one are treated separately; n=0 in the last conjunct is degree two,
with three faces and three pair relations. Empty finite families in the source
construction have singleton products of sections. Disconnected W is covered: the
slice product excludes pairs over different points of W. No field, coefficient ring,
characteristic, positive degree restriction, or further universe binder appears.

Independent searches, using words other than the worker's principal search:

- msearch leanfinder: `A quasi compact quasi separated scheme admits an augmented
  simplicial resolution by affine projective objects of its proetale topos` returned
  eight hits, including affine transition limit and open-cover results; none gives
  weakly contractible hypercover existence.
- msearch loogle: `"SimplicialObject"` reported unknown identifier and no hits;
  this unsuccessful query supplies no evidence of absence by itself.
- msearch grep: `WeaklyContractible|IsHypercover|affine.*hypercover` returned six
  finite-level affine Zariski hypercover hits, not this assertion.
- Independent case-insensitive rg for weakly-contractible and affine/hypercover
  combinations over all Mathlib, upstream WeilConjectures, the exact group framework
  lean/WeilConjectures, and project lean/Sheaf found no duplicate assertion or
  reusable weak-contractibility definition. Read the candidate
  `opensPreOneHypercover`/`opensOneHypercover` in the exact framework's
  ProEtale/Comparison/Continuity: these concern finite-level open-cover data and do
  not supply this all-degree theorem. Read `IsSemiRepresentableHypercover` in
  SemiRepresentableObject: it concerns formal etale families, a different category.
  The initial broad rg included a nonexistent upstream Simplicial directory;
  repeated the search on the entire existing upstream tree to cover it correctly.

Read coord/pefw-upstream-framework.md: no module-object declaration is needed here.
Read all statement dependencies and their actual records, including the two
convention-only nodes. Read all four proof-dependency records: none has a Lean
record, so no missing proof import can be added. No new nodes or dependency modules
are delivered; H12/H13 therefore introduce no additional review obligations. There
is no statement_change and no correction requiring citer review.

No mathematical mismatch found. Left the module and node unchanged; appended only
this independent reading. The module has one named theorem whose entire proof is
sorry, no hollow data, correct source/blueprint docstrings and all four natural
language proof steps. Checked explicit binders and signature equality against
lean.statement. Server scompile.py compiled the sole delivered module successfully
in 1.4 seconds, nice 19, two threads, 60-second limit, with no warnings or errors.
