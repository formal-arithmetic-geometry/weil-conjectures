## Worker report

The module `Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower` states
`AlgebraicGeometry.exists_compactifiable_compatible_tower`, with one `sorry` and no definitions
or proofs. The statement is a conjunction of supplied-compatible existence, stability under
arbitrary base change, and common refinement. The node is unchanged apart from `lean`.

Sources read: Stacks `more-etale.tex`, `lemma-shriek-composition` (Tag 0F7J), its diagram and
common domination argument; upstream `Compactification/Defs.lean`, `Comp.lean`, `Triangle.lean`,
`BaseChange.lean`, `Refinement.lean` and `Constructions.lean`. The source node explicitly uses
the supplied-compactification generalization from upstream Comp and Triangle, so no qcqs
hypothesis on the base is needed or introduced.

Hypotheses and clauses, matched individually:

- Schemes and composable maps: `{X Y Z : Scheme.{u}}`, `f : X ⟶ Y`, `h : Y ⟶ Z`.
- Separated finite-type maps: `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`,
  and the same three instances for `h`. These are exactly separatedness and finite type,
  with finite type expressed as locally finite type plus quasi-compactness.
- Supplied `d=(i,q)` and `c=(a₀,t)`: `d : Compactification h` and
  `c : Compactification (f ≫ h)`. Here `d.i`, `d.g`, `c.i`, `c.g` are `i,q,a₀,t`.
  `Compactification.comm` gives the two factorization equations; its instance fields give
  openness and properness. Although the upstream type permits a non-quasi-compact open map,
  its theorem `quasiCompact_openImmersion_iff` makes these open maps quasi-compact under
  the displayed finite-type hypotheses (composition supplies quasi-compactness of `f ≫ h`).
  Thus the type covers exactly the supplied compactifications in this context.
- Existence of `e=(a,p)`: `∃ e : Compactification (f ≫ d.i)`. The fields are `e.i=a`,
  `e.g=p`; its commutativity and instance fields impose the factorization, open immersion,
  and properness. `QuasiCompact e.i` explicitly states the remaining requirement.
- Proper domination of supplied `c`: `∃ v : e.Z ⟶ c.Z`, `IsProper v`,
  `e.i ≫ v = c.i`, `v ≫ c.g = e.g ≫ d.g`.
- Literal `U=Xbar ×_Ybar Y`: upstream `e.restrict.Z` reduces to `pullback e.g d.i`;
  `b=pullback.fst e.g d.i` and `p_Y=e.restrict.g=pullback.snd e.g d.i`.
  The induced open `c_X=e.restrict.i` is the upstream base-change construction of `(a,f)`.
- Quasi-compactness and openness of both `b,c_X`: the four explicit `QuasiCompact` and
  `IsOpenImmersion` conjuncts. Properness of `p_Y` is `IsProper e.restrict.g`.
- The identities `b c_X=a` and `p_Y c_X=f` are
  `e.restrict.i ≫ pullback.fst e.g d.i = e.i` and
  `e.restrict.i ≫ e.restrict.g = f`.
- Consequently `(c_X,p_Y)` is a compactification: already the type of `e.restrict`,
  with its quasi-compactness explicitly supplied above. The composite compactification
  `(a,qp)` is upstream `d.comp e`; `IsProper (e.g ≫ d.g)` is explicitly included.
- The square `p b=i p_Y` is cartesian: the final `IsPullback` of the first conjunct.
  Its commutativity is included in the `IsPullback` structure, not a separate extra clause.
- Stability concerns the data, not preservation of scheme-theoretic image. For any existing
  tower `T` with proper compatible map `v` to `c`, and any `Z'` and `k : Z' ⟶ Z`, the
  second conjunct constructs `f'` on the actual base-changed `X` and `Y`. The first
  `IsPullback` identifies `f'` with the base change of `f`, and six property conjuncts
  record separated finite type for `f'` and the base-changed `h`.
- `T' : Compactification.Triangle f' (pullback.snd h k)` supplies the pulled-back tower.
  Three `IsPullback` clauses for `rA,rB,rU` identify its ambient schemes and intermediate
  scheme with base changes of the OLD schemes over `Z`. In particular this is stronger
  than merely asserting existence of a fresh tower after changing the base.
  Its six equations identify the pulled-back arrows `a,i,c_X,b,p,p_Y`; commutativity over
  `Z'` of the proper structure maps comes from the three pullback squares. The type of
  `T'` imposes all openness/properness/cartesian conditions, and four quasi-compactness
  conjuncts impose these on its open maps. A proper `v'` refines `c.baseChange k`, with
  equations for its open map, map to `Z'`, and projection to the OLD `v`. Thus the supplied
  compactification and domination arrow base-change as well.
- Any TWO towers: `∀ T : Fin 2 → Compactification.Triangle f h`. This is an arbitrary
  ordered pair, including the case of equal towers. `∃ R` and `∀ j : Fin 2` produce
  proper maps `v,u,w` to each of them. No cartesianness of refinement maps is assumed.
  A `Triangle` has `cf` compactifying `f`, `cg` compactifying `h`, `cfg` compactifying `fh`,
  `q=b`, and `p=p`, and its `isPullback` identifies its `cf.Z` with the required fibre
  product. The use of this existing type therefore allows every tower in the node up to
  the unique projection-preserving isomorphism of intermediate schemes.
- Each of the seven refinement equations, for `R` as tower 1 and `T j` as tower 2:
  `R.cfg.i ≫ v = (T j).cfg.i` is `v a₁=a₂`;
  `R.cg.i ≫ u = (T j).cg.i` is `u i₁=i₂`;
  `R.cf.i ≫ w = (T j).cf.i` is `w c₁=c₂`;
  `R.q ≫ v = w ≫ (T j).q` is `v b₁=b₂ w`;
  `v ≫ (T j).p = R.p ≫ u` is `p₂ v=u p₁`;
  `w ≫ (T j).cf.g = R.cf.g` is `p_Y,₂ w=p_Y,₁`;
  `u ≫ (T j).cg.g = R.cg.g` is `q₂ u=q₁`.
  The first three equations restrict to the identities on the unchanged `X,Y`.
- Arbitrary base: there is no compactness, quasi-separatedness or Noetherian instance on `Z`.

Dependency declarations used (full signatures/docstrings read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`; its imported
  separated/universally-closed classes agree with the defining clauses of the dependency.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd` (scheme pullbacks exist).
- Existing upstream definitions, reused without private copies:
  `WeilConjectures.Compactification.Defs`: `Compactification`,
  `WeilConjectures.Compactification.Comp`: `Compactification.restrict`, `comp`,
  `WeilConjectures.Compactification.Triangle`: `Compactification.Triangle`, and
  `WeilConjectures.Compactification.BaseChange`: `Compactification.baseChange`.
  These extra existing source notions require no new definition node under §1(A): the
  source already gives the notions, and the displayed node statements use compactifications
  as explicitly defined factorization data. No second definition was written.

Proof-dependency imports are included through the public Mathlib imports, the upstream
Triangle/Constructions imports, the private Immersion import (cancellation) and the private
ZariskisMainTheorem import (closed immersion proper). The only unstated proof dependency is
`lem-cbc-compactifiable-cofiltered`, which has no Lean record yet; no module can be imported
for it. Its role is recorded in proof-plan step 5. There are no import cycles.

Edge cases checked before writing: empty schemes (all constructions and existential types
remain valid), identity maps and equal towers (the pair quantifier permits them), non-qcqs
bases (not constrained), arbitrary nonflat base change (only pullback of existing data is
asserted, not density or image preservation), non-dense compactifications with extra proper
components (neither a density condition nor a cartesian refinement condition is imposed),
and arbitrary scheme universe `u` (base changes remain in the same universe). The upstream
`Triangle` type imposes no hypothesis on its ambient schemes beyond those specified by the
compactifications. No statement fault or STATEMENT-DISPUTED issue was found.

Searches actually run:

- `msearch.py`, LeanFinder: “Compatible towers of compactifications of composable scheme
  morphisms with proper common refinements”: eight hits, mainly affine-transition-limit
  comparison lemmas and proper composition; no exact statement.
- `msearch.py`, Loogle: `Compactification, IsProper`: unknown identifier Compactification,
  zero hits. This is Mathlib search, not an upstream-source search.
- `msearch.py`, grep, AlgebraicGeometry:
  `structure.*(Compactification|Tower)|def.*(compatibleTower|compactificationTower)`:
  zero hits.
- `msearch.py`, LeanSearch: “compatible compactification towers of composable scheme
  morphisms”: unavailable, HTTP Internal Server Error (not evidence of absence).
- `rg` in upstream `WeilConjectures/Compactification` found the existing `Triangle` and its
  `ofRestrict`, `inf`, `infFst`, `infSnd`, and `ofComp`/`restrict` in Comp. These cover
  constructions used in the proof, but no single declaration has this node's whole statement.
- `grep -rn lem-cbc-compactifiable-compatible-tower` in upstream WeilConjectures: no hits.
- `rg` in project `lean/Sheaf`, for compactification/tower patterns and the new declaration
  name: no existing statement of this node. The upstream `Tower` is a different object for
  THREE composable maps; `Triangle` is the existing correct object here.
- `rg` in `dag/lean_names_upstream.json` for the declaration name and Triangle: no hits.
- `tools/blueprint_refs.py search 'triangle of compactifications'`: zero blueprint matches.

Validation: `scompile.py NL lem-cbc-compactifiable-compatible-tower` on the delivered file
passed on the project server in 1.5 seconds, nice 19, two threads, 60-second limit, with no
errors or warnings. The delivery dry run printed OK: the server compile and preflight passed except for the
second reading, which is reserved for the independent reader. Nothing was pushed or proved.

## Second reading by NL

I independently read the node's statement and all seven proof steps, Stacks
`more-etale.tex`, `lemma-shriek-composition` (Tag 0F7J), and upstream
`Compactification/Defs.lean`, `Comp.lean`, `Triangle.lean`, and `BaseChange.lean`.
The Stacks lemma assumes qcqs schemes to obtain compactifications. This node explicitly
cites the supplied-compactification generalization: `Comp.ofComp` and `Triangle.inf`
work from supplied compactifications without qcqs hypotheses. The Lean correctly keeps
that generalization rather than adding qcqs assumptions.

Object/hypothesis/conclusion checklist (all verdicts: match):

1. Schemes X, Y, Z and composable f, h: `{X Y Z : Scheme.{u}}`, `(f : X ⟶ Y)` and
   `(h : Y ⟶ Z)`. No assumption on the underlying schemes or their base is added.
2. Separated finite-type f and h: `[IsSeparated f] [LocallyOfFiniteType f]
   [QuasiCompact f]` and the corresponding three binders for h. Finite type is exactly
   locally finite type plus quasi-compactness, not finite presentation.
3. Supplied d = (i,q) and c = (a₀,t): `d : Compactification h` and
   `c : Compactification (f ≫ h)`, with i = d.i, q = d.g, a₀ = c.i, t = c.g.
   `Compactification.comm` supplies factorization; its fields give openness/properness.
   The potentially weaker upstream compactification type causes no missing hypothesis:
   `quasiCompact_openImmersion_iff` gives quasi-compactness from that of h and f ≫ h.
4. Existence of e = (a,p) compactifying if: `∃ e : Compactification (f ≫ d.i)`.
   Thus a = e.i, p = e.g, the correct factorization is built into e, and
   `QuasiCompact e.i` supplies the remaining compactification property.
5. Proper domination of c: the existential `v : e.Z ⟶ c.Z` with `IsProper v`,
   `e.i ≫ v = c.i` and `v ≫ c.g = e.g ≫ d.g` gives precisely va = a₀ and tv = qp.
6. U is the fibre product, not an unrelated scheme: `e.restrict.Z` unfolds to
   `pullback e.g d.i`; b = `pullback.fst e.g d.i`, p_Y = `e.restrict.g`, and
   c_X = `e.restrict.i`. I read `restrict` and the underlying `ofIsPullback` construction.
7. b and c_X quasi-compact and open: the four explicit `QuasiCompact` and
   `IsOpenImmersion` conjuncts name these exact arrows.
8. Proper p_Y: `IsProper e.restrict.g`.
9. bc_X = a and p_Yc_X = f: `e.restrict.i ≫ pullback.fst e.g d.i = e.i` and
   `e.restrict.i ≫ e.restrict.g = f`.
10. Compactification of f: the type `e.restrict : Compactification f`, together with
    quasi-compactness in item 7. Compactification of hf: the open map e.i and proper map
    e.g ≫ d.g; factorization follows from e.comm and d.comm, and properness is explicit.
11. Cartesian p b = i p_Y: `IsPullback e.restrict.g (pullback.fst e.g d.i) d.i e.g`.
    This uses the correct square orientation, with commutativity included in IsPullback.
12. Arbitrary base change of these data: the second conjunct quantifies over any old
    `T : Compactification.Triangle f h`, its proper compatible v to c, and every
    `Z' : Scheme.{u}`, `k : Z' ⟶ Z`. It therefore applies to the tower from the first
    conjunct via `Triangle.ofRestrict d e`; it does not merely find a fresh unrelated tower.
13. Base-changed f and h: f' has source `pullback (f ≫ h) k` and target `pullback h k`.
    The first IsPullback specifies the base change of f, and h' is `pullback.snd h k`.
    Six conjuncts retain exactly separated finite type for f' and h'.
14. Base-changed ambient and intermediate schemes: T' and rA, rB, rU have three
    IsPullback squares over Z. These identify A', B', U' with the base changes of A, B, U.
    The six following equations preserve a, i, c_X, b, p, p_Y. The structure maps over Z'
    commute by the squares themselves. The Triangle type imposes the same cartesian
    tower condition, open maps and proper structure maps; four explicit quasi-compactness
    clauses cover all the designated open maps.
15. Base-changed supplied c and domination: v' targets `(c.baseChange k).Z`, is proper,
    extends the new open map and commutes with the new structure map. Its projection
    equation `v' ≫ pullback.fst c.g k = rA ≫ v` identifies it with the old v pulled back.
16. Any two towers: `∀ T : Fin 2 → Compactification.Triangle f h` is any ordered pair,
    not an arbitrary family nor a restricted pair. The common `∃ R` precedes `∀ j`.
    Each Triangle is equivalent to the node's fibre-product presentation by its
    projection-preserving isomorphism. Its p is proper by `Triangle.isProper_p`.
    Its open maps are quasi-compact from those of f, h, fh and base change of cg.i.
    R therefore has every property required of a refining tower even without repeating
    those derived properties as conjuncts.
17. Proper v, u, w to both towers: the three existential map types and three IsProper
    conjuncts give exactly the ambient-X, ambient-Y and intermediate maps.
18. All seven refinement equations: `R.cfg.i ≫ v = (T j).cfg.i` gives va₁ = a₂;
    `R.cg.i ≫ u = (T j).cg.i` gives ui₁ = i₂;
    `R.cf.i ≫ w = (T j).cf.i` gives wc₁ = c₂;
    `R.q ≫ v = w ≫ (T j).q` gives vb₁ = b₂w;
    `v ≫ (T j).p = R.p ≫ u` gives p₂v = up₁;
    `w ≫ (T j).cf.g = R.cf.g` gives p_Y,₂w = p_Y,₁;
    `u ≫ (T j).cg.g = R.cg.g` gives q₂u = q₁.
    The first three express restriction to identities on X,Y. The statement correctly
    uses explicit maps rather than Triangle.Hom, which would add cartesian conditions.

Dependency check: I opened all five stmt_deps nodes and matched their recorded
Mathlib declarations to the actual definitions: Scheme is locally affine locally ringed
space; IsOpenImmersion is that of locally ringed spaces; IsSeparated means closed
immersion of the diagonal; IsProper extends separated, universally closed and locally
finite type (universal closedness supplies quasi-compactness); LocallyOfFiniteType and
QuasiCompact have their usual affine/topological definitions. I also opened the pullback
and projection signatures and the upstream Compactification/Triangle signatures. None
requires an extra Noetherian, field, density, finiteness or qcqs instance. No new nodes,
dependency modules, hollow definitions or private notions occur in this delivery.

Edge cases: empty X, Y or Z are allowed wherever morphisms and supplied compactifications
exist; no nonemptiness hypothesis occurs. Identities, equal towers and compactifications
with extra proper components are permitted. Fin 2 encodes exactly two choices, so there
is no empty-index limit assumption to check. Zero objects, n = 0 and characteristic are
not parameters of this geometric statement. The universe u is arbitrary, and every
scheme/base-change construction uses it consistently; there is no small test-object
universe that could make a hypothesis vacuous. Arbitrary nonflat k is permitted, without
claiming preservation of schematic density or of a chosen scheme-theoretic image.

Independent searches:

- LeanFinder via msearch: `Extending morphisms to proper compactifications with a common
  dominating diagram` returned affine-transition-limit and unrelated categorical results;
  none is this statement.
- Loogle via msearch: `"IsPullback", "IsProper"` returned zero hits.
- LeanSearch via msearch: `Proper compactifications admitting compatible dominating
  refinements` was unavailable (Internal Server Error); no absence verdict relies on it.
- msearch grep `common.*refin|dominat.*compact|ofComp|Triangle` was too broad (unrelated
  triangle results). I supplemented it with direct rg searches below.
- Direct rg of Mathlib AlgebraicGeometry for `compactification|compactifiable|compactifying`
  found no such notion. Direct rg of project lean/Sheaf and upstream WeilConjectures for
  `compactif.*(tower|triangle)|compatible.*compactif` and the declaration name found the
  upstream Triangle/Comp machinery and the distinct three-map Tower, but no theorem
  containing this node's three clauses. Searching `common.*refin|dominat.*compact` also
  located upstream CommonRefinement and CategoryBaseChange: these concern individual
  compactifications, not this supplied-compatible tower theorem. Existing Triangle and
  compactification constructions are reused; no duplicate definition was introduced.

No mathematical or signature mismatch was found, so the Lean and node are unchanged.
The module has one theorem with sorry, no definitions or proved auxiliaries; its docstring
carries all seven proof steps and source identifiers. No free variable, local notation,
local instance, private definition, or line over 100 characters remains. The signature
was mechanically compared verbatim to lean.statement. Compilation and delivery preflight
results are recorded below.

Second-reader validation: scompile.py compiled the sole delivered module cleanly on the
server in 1.5 seconds, nice 19, two threads, 60-second limit. deliver2.py --no-push
printed OK: preflight passed and compilation passed; nothing was pushed by the dry run.
