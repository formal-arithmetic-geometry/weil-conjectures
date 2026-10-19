## Worker report

The module `Sheaf.CategoryTheory.RelativeExponentialRestriction` states
`SSet.Enhanced.relativeExponentialRestriction_innerFibration`, with its sole proof
`sorry`. All definitions have real data, including their simplicial identities
and naturality. No statement correction, disputed statement, dependency repair,
or new independent notion is needed.

Clause-by-clause correspondence:

- The four quasicategories in the fixed universe are `(S X Y E : SSet.{u})`
  with the four explicit `SSet.Quasicategory` instances. There is exactly one
  universe variable, `u`; all simplex-category indices are explicitly bound.
- `p : X ⟶ S`, `q : Y ⟶ S`, and the hypotheses
  `hp : cocartesianFibration p`, `hq : cocartesianFibration q` use the recorded
  cocartesian-fibration definition with no altered edge convention.
- `j : X ⟶ Y` is an arbitrary simplicial map. Its degreewise injectivity is
  `hmono : ∀ n : SimplexCategoryᵒᵖ, Function.Injective (j.app n)`.
  The equality `hcomm : j ≫ q = p` is exactly the displayed equation `qj=p`.
- `relativeExponential E p` and `relativeExponential E q` are the two prescribed
  objects. `RelativeExponentialSimplex.sigma : S.obj n` represents the map
  `Δ[n] → S` via Mathlib's Yoneda correspondence. For each opposite-simplex
  arrow `a : n ⟶ m` and `z : Z.obj m`, its field `value a z hz` gives the value
  of `h` on the pullback simplex `(a,z)`, where
  `hz : p.app m z = S.map a sigma` is exactly the pullback equation.
  The arrow `a.unop` represents the corresponding simplex of `Δ[n]` (with
  Mathlib's harmless `ULift` in the representable). The `naturality` field says
  precisely that these values define a simplicial map from the degreewise
  pullback. Conversely any such map gives this natural family. Proof arguments
  are irrelevant, so this presentation adds no data or restriction to `h`.
- `relativeExponentialMap` implements every simplicial operator: the new base
  simplex is `S.map f x.sigma`, and the family is precomposed by `f ≫ a`.
  The identity and composition fields are proved inside the construction;
  they contain no postponed theorem or data.
- `relativeExponentialProjection E p` forgets `value` and returns `sigma`.
  The same definition applied to `q` gives the other projection.
- `relativeExponentialRestrictionMap` keeps `sigma` and replaces `z` by
  `j.app _ z`. Its pullback equation follows from `hcomm`; its naturality
  follows from the naturality of `j` and of `h`.
  `relativeExponentialRestriction` bundles exactly this canonical simplicial
  map, with proved naturality. In particular it lies strictly over `S`, since
  its `sigma` field is unchanged.
- The first two conjuncts of the theorem state that `H_X` and `H_Y` are
  quasicategories. The last conjunct is `SSet.InnerFibration` of the specified
  restriction map. Mathlib defines this by the right lifting property for all
  inner horn inclusions. `HasLiftingProperty` uses actual commutative squares
  and exact triangle equations, so the filler agrees exactly on the horn.
- There are no colimit assumptions on `E`, no fullness assumption on `j`, and
  no requirement that `j` preserve cocartesian edges.

Dependencies read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones` supplies the existing enhanced
  simplicial conventions and its public Mathlib primitives, particularly
  `SSet.Quasicategory`, simplicial maps, and the standard-simplex/Yoneda
  conventions. No replacement notion of quasicategory is defined.
- `Sheaf.CategoryTheory.InfinityFibrations`, declaration
  `SSet.Enhanced.cocartesianFibration`, supplies both `hp` and `hq`; its entire
  definition and the cocartesian-edge definition were read.
- `SSet.InnerFibration` from Mathlib's
  `AlgebraicTopology.Quasicategory.InnerFibration` supplies the conclusion.
- The proof-only nodes `lem-coef-joyal-model-structure` and
  `lem-coef-cocartesian-categorical-base-change` currently have no Lean record,
  so they have no module to import. Both are explicitly named in the complete
  six-step proof docstring, which retains the node's argument. The already
  stated proof dependency `def-cbc-enhanced-diagrams-cones` is imported.

The inline relative-exponential construction belongs to the item's own
statement. Its six helper declarations are listed in `lean.declarations`;
this does not invent an independent definition node. The related unstated
`lem-cbc-enhanced-relative-exponential` proves transport/edge criteria and is
not a declaration defining or proving the current item. The DAG's
`def-cbc-enhanced-cartesian-fibration` concerns sections and Grothendieck
presentations and also does not define this relative exponential.

Edge cases checked before finalizing the signature: empty `X` (restriction
forgets the whole family), empty `Y` (hence empty `X`), empty base (hence empty
total spaces), empty target `E` (maps retained exactly when their pullbacks
are empty), `j=id`, base `Δ[0]`, and arbitrary non-full `j`. There is no
inhabitedness assumption anywhere. In dimensions zero and one there are no
inner horns; the primitive `InnerFibration` imposes only the intended inner
horns in positive higher dimension. The universe of the natural family is
still `u`, since simplex-category arrows are small and `Z.obj m`, `E.obj m`
live in `Type u`.

Searches for an existing declaration:

- `msearch.py`, LeanFinder: "Restriction of relative exponential simplicial
  sets along a monomorphism between cocartesian fibrations is an inner
  fibration". Eight results, all Quillen generating horns/cofibrations and
  fibrations; none is the relative theorem.
- `msearch.py`, LeanSearch: "Relative exponential restriction along a
  monomorphism of cocartesian fibrations is an inner fibration". Eight hits
  include base-change stability of model fibrations, ordinary-category
  cocartesian arrows, and `ExponentiableMorphism`; no matching statement.
- `msearch.py`, Loogle: `"InnerFibration", "pre"`. The single result is
  `SSet.instInnerFibrationAppPreOfMonoOfQuasicategory`. Its full signature was
  read at `AnodyneExtensions/Inner/PushoutProduct.lean:142`: it concerns the
  ordinary internal Hom for a fixed exponent, not varying base simplices.
- `msearch.py`, grep: `relative.?[Ee]xponential|[Cc]ocartesian|isofibration`
  in `AlgebraicTopology`: zero hits.
- `rg` in Mathlib, `WeilConjectures/`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for all seven proposed declaration names:
  no matches. The upstream node-id grep likewise found no match. Concept
  searches in the DAG located the related unstated relative-exponential
  transport theorem and the sections/Grothendieck definition above, neither
  giving an existing declaration for this item.

Sources checked directly: Kerodon 02ZR, especially the isofibration proof
via its relative-exponential correspondence and categorical pushout, and
0472 for the relative-exponential convention. This item asserts only the
inner-fibration consequence. No source-based correction was required.

Validation: the complete module compiled cleanly with `scompile.py`, in both
sandbox and module positions, under the default file limit. The only `sorry`
is the named theorem for this DAG node. The required delivery dry run printed `OK (dry run)` at commit
`2900345bd5`: compilation and preflight passed except for the independent
second reading, which the second reader supplies. Nothing was pushed. A
final dry run repeats these checks after adding the module declaration index.

## Second reading by NE

I independently read the complete node, its six proof steps, and the sandbox module.
I read Kerodon 02ZR, Lemma the project server, especially its proof of the isofibration assertion
for V, and 0472, Corollary the project server. These are Kerodon sources, not Stacks tex.
The node takes the inner-fibration consequence of the same lifting argument for an
arbitrary monomorphism between cocartesian fibrations, with terminal target base.
The source proof uses only the injectivity of that map and categorical-equivalence
base change, so neither fullness nor preservation of cocartesian edges is needed.
No statement correction is needed.

Object, hypothesis, and conclusion audit:

- The four quasicategories in a fixed universe are `(S X Y E : SSet.{u})` with
  the four explicit `SSet.Quasicategory` binders. Verdict: exact, with arbitrary u.
- The two maps to the common base are `(p : X ⟶ S)` and `(q : Y ⟶ S)`;
  `(hp : cocartesianFibration p)` and `(hq : cocartesianFibration q)` are their
  cocartesian-fibration hypotheses. I read `InfinityFibrations.lean`, including
  `IsCocartesianEdge` and the entire `cocartesianFibration` definition, against
  `def-coef-infinity-fibrations`: it requires precisely inner lifting and a
  cocartesian lift of each edge at every source. Verdict: exact dependency use.
- `(j : X ⟶ Y)` is arbitrary subject only to `(hcomm : j ≫ q = p)` and
  `(hmono : ∀ n : SimplexCategoryᵒᵖ, Function.Injective (j.app n))`.
  These render qj=p and degreewise injectivity in every dimension. Verdict: exact.
- For Z=X,Y the pair (sigma,h) defining H_Z is
  `RelativeExponentialSimplex E p n` (or with q). Its `sigma : S.obj n`
  represents Δ[n] → S by Yoneda. For a simplex operator `a : n ⟶ m`,
  `value a z hz` is the value of h on the pair (a,z) in the degreewise pullback;
  `hz : p.app m z = S.map a sigma` is exactly the pullback equation.
  Its `naturality` quantifies over every composable b and asserts the simplicial
  identity for h. Proof irrelevance removes dependence on the proof hz. Thus the
  family is precisely a simplicial map Δ[n] ×_S Z → E. Verdict: exact real data.
- `relativeExponentialMap` changes sigma to `S.map f x.sigma` and replaces a by
  `f ≫ a`; `relativeExponential` supplies the identity and composition laws.
  These are exactly the specified simplicial operators. The proofs inside these
  definitions only discharge their structure laws; there is no postponed data.
  `relativeExponentialProjection` returns sigma. Verdict: exact construction.
- `relativeExponentialRestrictionMap` preserves sigma and sends z to `j.app _ z`
  in h; hcomm supplies the pullback equation. The bundled
  `relativeExponentialRestriction` has the required naturality. It is strictly
  over S because sigma is unchanged. Verdict: precisely the canonical R.
- The first two conclusion conjuncts are `SSet.Quasicategory` of H_X and H_Y;
  the third is `SSet.InnerFibration` of this exact R. I opened Mathlib's
  `Quasicategory/InnerFibration.lean`: it is the right lifting property against
  all inner horns. Its lifting equations are strict, as the node requires.
  Verdict: all three clauses, with no weakening or additional clause.

I read `EnhancedDiagramsCones.lean` and its dependency node: the primitive
quasicategory, simplex, horn, and degreewise simplicial conventions here are
Mathlib's existing ones, not copies. I also read the related nodes
`lem-cbc-enhanced-relative-exponential` and `def-cbc-enhanced-cartesian-fibration`;
neither has a usable recorded declaration defining this relative exponential.
There are no new definition nodes or dependency modules in this delivery.
The six construction helpers belong to the item's displayed definition and are
listed, with the theorem, in `lean.declarations`.

Edge cases: empty X gives vacuous pullback families; empty Y forces X empty;
empty S forces both total spaces empty; empty E permits exactly maps whose
pullbacks are empty. No inhabitedness is assumed. The identity inclusion,
a point base Δ[0], and arbitrary non-full j remain covered. Dimensions zero and
one impose no inner horn conditions; there is no n≥1 restriction on the data.
The theorem is in arbitrary common universe u, and the family over the small
simplex category remains in that universe. Rings, schemes, and characteristic
are not objects in this statement, so their edge cases do not apply.

Independent searches: I used `msearch.py` LeanFinder with "relative exponential
restriction inner fibration cocartesian fibration", LeanSearch with "Simplicial
dependent function object over a base restricts along inclusions of cocartesian
fibrations with exact inner horn lifting", and Loogle with
`"InnerFibration", "pre"`. I also ran its grep for dependent/exponentiable/relative
Hom terminology and used rg over Mathlib, upstream WeilConjectures, project
lean/Sheaf, and dag/lean_names_upstream.json for all seven declaration names and
relative-exponential/dependent-product terminology. No duplicate exists there.
I opened Mathlib's `AnodyneExtensions/Inner/PushoutProduct.lean`: its
`SSet.instInnerFibrationAppPreOfMonoOfQuasicategory` is ordinary fixed-exponent
internal-Hom restriction. It does not define the varying-base relative object
or its restriction. The ordinary-category cocartesian and Kan-Quillen search
hits likewise have different objects or lifting conditions.

One mismatch found and repaired: the worker report says both model-theory proof
dependencies have no Lean record. The current `lem-coef-joyal-model-structure`
does have the recorded module `Sheaf.AlgebraicTopology.JoyalModelStructure`.
I read its complete declaration `SSet.exists_joyal_model_structure` and added
its required proof-only `import`, as stages/2-statements.md §3.7 requires.
`lem-coef-cocartesian-categorical-base-change` still has no Lean record and hence
no module to import. This paragraph supersedes that part of the Worker report.
The theorem's docstring carries all six proof steps, including these two nodes;
every declaration has its source and this item's blueprint tag. Definitions
contain real data; the sole postponed proof is the named main theorem.

I found no mathematical or signature mismatch and changed no statement or node
field. The sole actual citer is
`lem-coef-infinity-fiber-cocone-simplex-extension`; its proof step 2 uses exactly
the inner-fibration conclusion with its inclusion of nerves, so holds: true.
No statement_change or citer correction is necessary.

Validation after the import repair: the required scompile.py wrapper compiled
both sandbox and module positions cleanly under the default 60-second limit,
with no warnings. All variables and universes are explicitly bound. No Lean line
exceeds 100 characters; there is exactly one sorry, on the named main theorem.
The node copy differs from the read-only base only in lean, and lean.statement
is verbatim equal to the declaration signature in the file.
