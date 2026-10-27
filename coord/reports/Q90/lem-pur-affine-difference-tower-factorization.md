## Worker report

The module `Sheaf.AlgebraicGeometry.AffineDifferenceTowerFactorization` states the complete node in two theorems, `AlgebraicGeometry.AffineDifferenceTower.factorization` and `AlgebraicGeometry.AffineDifferenceTower.exists_compatible_charts`. Both proofs are `sorry`. All helper data are actual constructions. There are no new nodes, dependency-node repairs, or statement corrections.

Source read: main-20261015 blueprint, `sec-smooth-purity/sk-prop-sp-composition/thm-pur-composition-coherence.proof.md`, Step 1, including its Cartesian product identifications and standard etale local coordinates. The node's eleven proof steps are included in the theorem docstrings, split between tower geometry and local existence.

Hypotheses, matched individually:

- The field is `{k : Type u} [Field k]`; schemes are `Scheme.{u}`. The structure maps and compatibility of f,g with k are `Over (Spec (.of k))` and `IsOver` instances.
- Affineness of U,V,T is `[IsAffine U]`, `[IsAffine V]`, `[IsAffine T]`. Their finite type over k is separately `LocallyOfFiniteType` and `QuasiCompact` on each structure morphism.
- The maps are `(f : U ⟶ V)` and `(g : V ⟶ T)`. Pure smooth relative dimensions are `[SmoothOfRelativeDimension d f]` and `[SmoothOfRelativeDimension e g]`, with `(d e : ℕ)` allowing zero. Separatedness, local finite type and quasi-compactness are the corresponding instances for each map, exactly rendering separated finite type.
- The specified charts are `cf : U ⟶ AffineSpace (Coords d) V` and `cg : V ⟶ AffineSpace (Coords e) T`, with `[Etale cf]`, `[Etale cg]`. The equations `hcf`, `hcg` say their composites with the affine projections are f,g. Their coordinates are the pullbacks of `AffineSpace.coord`.

Every construction and conclusion, in node order:

- B is U. `Q f g` is `pullback (f ≫ g) g`; `W f g` is `pullback (f ≫ g) (f ≫ g)`. The existing `DiagonalPasting.a` and `DiagonalPasting.s` are exactly the node's a and s. The map b is `pullback.fst (f ≫ g) g`; t is `pullback.diagonal (f ≫ g)`.
- `Coords r` is only the universe-lifted finite coordinate index. All spaces use the recorded Mathlib `AffineSpace` definition. The already existing `DiagonalPasting.A`, `q`, `first`, and `zero` provide the affine (d+e)-space, ordered last and first block projections, and zero sections. The first embedding uses `Fin.castAdd e`, the second `Fin.natAdd d`.
- G is the existing `DiagonalPasting.differenceSecond e f g cg`, defined by `homOfVector` with coordinates y(v)-y(fu). Its untranslated version is `Graw`.
- R is represented by the node's explicit second description `AffineSpace (Coords d) (Q f g)`, with q_Q its structure projection. J is the new `J`, retaining the first d coordinates and inserting the coordinates of G in the last e positions using `Fin.addCases`. The asserted `IsPullback J q_Q q G` supplies exactly the universal property identifying R with the displayed fibre product; no unspecified equivalence or arbitrary map is assumed.
- `H` is `homOfVector (a f g)` with coordinates x(u')-x(u). `Hraw` has the same base map and untranslated x(u') coordinates.
- F is the existing `DiagonalPasting.differenceTotal d e f g cf cg`. The first conjunct explicitly asserts `H ≫ J = F`; it does not merely identify point values.
- The following five conjuncts assert H followed by q_Q equals a, G followed by P_e equals b, J followed by q equals q_Q followed by G, s followed by G equals z_e, and t followed by F equals z_(d+e).
- The next two universal equalities compute the pullback of each polynomial coordinate by F, separately on the first and last block. The next conjunct says F is over B. Together these give the stated ordered coordinates as scheme morphisms.
- For each of G,H,J,F the theorem separately asserts `Etale`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`; the last two render finite type. The following `IsAffine` conjuncts cover Q,W,R,W_f,V×_T V and all affine spaces appearing in the tower and charts. B,U,V,T are affine by the input instances.
- `IsPullback Graw Q.snd (AffineSpace.map (f ≫ g)) cg` is the specified base change of the g chart. The following equality writes G as that map followed by `AffineSpace.translation` by the negative pulled-back y coordinates.
- `IsPullback Hraw W.snd (AffineSpace.map Q.snd) cf` is the specified base change of the f chart, incorporating the canonical W=Q×_V U identification. The following equality writes H as that map followed by translation by the negative x coordinates pulled back from B to Q.
- `IsPullback J q_Q q G` simultaneously says that R's square is Cartesian and J is the base change of G.
- `IsPullback first q P_d P_e` says independently that q is the base change of P_d along P_e. Four following `SmoothOfRelativeDimension` conjuncts have dimensions d,e,d+e,d for q,P_e,q≫P_e,q_Q respectively.
- H_f is the existing `differenceFirst d f cf`, W_f is `pullback f f`, and the existing `DiagonalPasting.i` is the induced W_f→W map. `includeR` is exactly `AffineSpace.map (s f g)`. The asserted `IsPullback H_f i includeR H` is the required restriction square.
- G_g is the existing `differenceFirst e g cg`. The existing `DiagonalPasting.j` sends (u,v) to (fu,v). `IsPullback G j (AffineSpace.map f) G_g` is the required square over f.
- The final four conjuncts give etaleness of H_f,G_g and both equations sending their diagonals to their zero sections.
- `exists_compatible_charts` uses arbitrary finite-type k-schemes X,Y,Z, with no affineness or absolute separatedness hypothesis. The hypotheses on f,g and their dimensions are the same. For every `(x : X)` it supplies opens U,V,T, each `IsAffineOpen`, containing x,f(x),g(f(x)); `hUV`, `hVT` give the two image containments. It supplies etale charts of sizes d,e with equations over the restricted pair `resLE`. The remaining conjuncts explicitly ensure smooth dimensions, separated finite type for that pair and finite type over k for the three opens, so this is exactly a pair of the preceding form.

Dependency declarations actually used:

- `def-weil-scheme-morphism-properties` is a convention node, not a missing declaration. Its meanings are Mathlib `Scheme`, `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`. Their full definitions/docstrings were read in the named Mathlib scheme morphism modules.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.SmoothOfRelativeDimension` (and its smoothness convention), as recorded by that dependency.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `AlgebraicGeometry.Etale`.
- `def-sbc-affine-space`: `Mathlib.AlgebraicGeometry.AffineSpace`, `AlgebraicGeometry.AffineSpace`; its coordinate index is `ULift.{u} (Fin r)`. The actual APIs `coord`, `homOfVector`, `map`, and `reindex` are reused. `zeroSection` and `translation` come from `WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `pullback`, its projections, diagonal, and universal maps. Cartesian conclusions use `CategoryTheory.IsPullback`.
- The existing graph maps, block maps, and three difference maps come from `Sheaf.Paper.PurityDiagonalSectionPasting`, namespace `WeilConjectures.PurityFiniteSetting.DiagonalPasting`: `a`, `s`, `i`, `j`, `A`, `q`, `first`, `zero`, `differenceFirst`, `differenceSecond`, `differenceTotal`. Their full definitions and surrounding docstrings were read. These are real constructions, not choices from an unproved existence theorem. The node's theorem is not already stated there: `chartGeometry` omits H,J, the factorization, both Cartesian restriction squares and the local existence clause, and has a different interface.
- Proof imports retain the existing normal-form theorem from `Sheaf.AlgebraicGeometry.EtaleLocalNormalForm`, the smooth affine-space instance from `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`, and the finite-limit framework from `Mathlib.CategoryTheory.Limits.MorphismProperty`. The other recorded proof-dependency modules are already imported publicly or transitively by these imports; no statement is copied.

Searches performed (actual results):

- msearch leanfinder, query `etale affine coordinate differences Cartesian tower of two smooth morphisms`: eight hits, chiefly standard-smooth ring maps admitting an etale polynomial chart and etale composition; no full tower statement.
- msearch loogle, query `AlgebraicGeometry.AffineSpace.homOfVector, AlgebraicGeometry.AffineSpace.translation`: zero hits; the service specifically reported unknown identifier for the upstream-only translation, not proof of its absence from the project.
- msearch grep, query `difference.*tower|tower.*factorization|def translation`, Mathlib subdirectory `AlgebraicGeometry`: zero hits.
- Local rg for the item id and `affineDifferenceTower|differenceChart` in WeilConjectures, Sheaf, and upstream-name inventory: no identical statement. Searching coordinates and translation in the upstream affine-space module found the canonical translation and affine-space APIs, which were read and reused.
- Broader rg of purity modules for `AffineSpace|difference.*chart|translated` found `PurityDiagonalSectionPasting`. Reading its graph and coordinate definitions exposed the existing helpers listed above; all equivalent draft copies were removed and replaced with those declarations. A further scoped factorization/difference search found no existing complete statement.

Edge cases checked: d=0, e=0, d=e=0; zero-ring/empty affine schemes; identity maps and the zero-dimensional affine-space model; arbitrary positive characteristic. Coordinates use finite types without `Nonempty`; `Fin.addCases` keeps empty blocks meaningful. The R model and all assertions use schemes and polynomial coordinates rather than ordinary rational points. The local theorem quantifies over x, hence is vacuous for empty X. There is no characteristic restriction or nonemptiness assumption.

Validation: the final module compiled through scompile.py as both the sandbox module and its actual library module with no errors or warnings. There are exactly two postponed named theorems, matching the two parts of this DAG node. No definitions contain sorry.

Import-cycle note for the maintainer: this delivery must import the existing `PurityDiagonalSectionPasting` module to reuse its canonical graph/block/difference definitions. Its node now lists this item in proof_deps. Do not add the reverse proof import from that module to this one: it would close a module cycle (stages/2-statements.md §3 rule 7 explicitly permits omitting and listing such a proof import). No downstream diagonal-pasting theorem or `chartGeometry` proof is used here. Future module refactoring may move these shared constructions to a smaller owning module, but this delivery does not edit the read-only library or duplicate them, and adds no cyclic DAG dependency.

## Second reading by Q90

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
