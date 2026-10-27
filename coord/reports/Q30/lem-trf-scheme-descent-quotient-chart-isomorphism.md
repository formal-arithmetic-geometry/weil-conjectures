## Worker report

The module `Sheaf.AlgebraicGeometry.SchemeDescentQuotientChartIsomorphism` states
`AlgebraicGeometry.AlgebraicSpace.scheme_descent_quotient_chart_isomorphism` with
one `sorry`, and introduces no definitions. The item JSON changes only `lean`.
The source was read in `literature/stacks-project/spaces.tex`: presentation lemma
0262, lemma-when-it-works-it-works (02WV), and theorem-presentation (02WW).
The current blueprint unit under `literature/blueprint/latest/blueprint/` is
`sec-trace-formula/sk-i-curve-zero/_section.md`; this item is an auxiliary
chart-recovery input, not that unit's own statement.

Hypothesis correspondence, in the order of the node:

- `S : Scheme.{u}` is the base. `U X : I → Over S` are the base charts and
  their local schemes; `f : ∀ i, X i ⟶ U i` includes exactly the commuting
  structure-map triangles. An arbitrary local scheme over `U i` determines
  this object of `Over S` by composition, so this adds no hypothesis.
- `hU` is étaleness of every `U i → S`; `hcover` is joint surjectivity on
  underlying scheme points. No member is individually required surjective.
- In `Over S`, `U i ⨯ U j` is the scheme fibre product `U_i ×_S U_j`.
  `R,p,b,hR` specify `R_ij = X_i ×_{U_i}(U_i ×_S U_j)` with its two
  projections by `IsPullback (p i j) (b i j) (f i) prod.fst`. This is the
  universal-property form of the node's chosen pullback, not an arbitrary
  overlap or a replacement relation. Any chosen pullback supplies these
  witnesses, and conversely they determine it uniquely with its projections.
- `theta` gives precisely the isomorphisms `R i j ≅ R j i`. `hleft` and
  `hright` say that their two base coordinates are interchanged.
- `hnormal` tests the restriction to the base diagonal: if the two base
  coordinates of `r : T → R i i` agree, then `r ≫ theta = r`. Such `r`
  are exactly maps factoring through the diagonal pullback. This does not
  require `theta i i` to be the identity on the whole overlap.
- `hcocycle` is the cocycle on every triple overlap. `a` is an `ij` section
  and `a'` a `jk` section with middle chart section equal after `theta i j`.
  The next two equations specify the unique `ik` section `c` with the same
  initial `X_i` section and final `U_k` coordinate. The final two specify
  the unique `ki` section `d` obtained by the successive transitions and
  carrying the initial `U_i` coordinate. The conclusion `c ≫ theta i k = d`
  is exactly the equality of the single and successive transitions.
  The required `c,d` always exist and are unique by `hR`; their use does not
  restrict the triples on which the cocycle is asserted.
- `V,ι,hV` and `W,κ,hW` are the coproducts of `X_i` and `R_ij`, expressed
  by `IsColimit (Cofan.mk ...)`. These universal-property witnesses retain
  the inclusions. Coproducts in `Over S` are the scheme coproducts with
  their induced structure maps; the forgetful functor creates colimits.
- `s,t,hs,ht` give the node's source and target with exactly the prescribed
  components `p_i` and `p_j theta_ij`. The universal properties determine
  `s,t` uniquely; they are not arbitrary maps.
- `F : AlgebraicSpace S` uses the recorded full subcategory of big fppf
  sheaves. `q` is the natural transformation from `h_V`. `hqet,hqsurj`
  use its recorded scheme-test étaleness and surjectivity predicates.
- `hq` is `qs=qt`. `hkernel : IsPullback (yoneda.map s) (yoneda.map t) q q`
  is precisely that the induced map to the kernel pair is an isomorphism.
  No arbitrary identification with a different relation is used.

Conclusion correspondence:

- The first conjunct is `IsIso (prod.lift (yoneda.map (ι i) ≫ q)
  (yoneda.map (f i)))` for every `i`: the **specified natural map** `(q_i,f_i)`.
  Since the site is `Over S`, its product is `F ×_S h_{U_i}`. The unique
  map to `h_S` is terminal, so no structure map is lost. Isomorphism of the
  underlying presheaf map is equivalently isomorphism of the sheaf map.
- The second conjunct identifies the induced transition with `theta` on
  every test scheme. For `r : T → R_ij` and `r' : T → R_ji` with the same
  switched base coordinates, `r theta_ij = r'` if and only if their `X_i`
  and `X_j` sections have the same quotient section. Under the first
  conjunct this is exactly the graph characterization of the transition
  induced by the two chart isomorphisms, including both base coordinates.
- The third conjunct is the individual kernel-pair square, with its top
  arrows `yoneda.map (p i j)` and
  `yoneda.map ((theta i j).hom ≫ p j i)`. Its universal property identifies
  `X_i ×_F X_j` with this very `R_ij` and these very projections.
- The fourth conjunct asserts representable étaleness of every `q_i`.
- The final conjunct expresses joint surjectivity in the scheme-test sense:
  for each `h_T → F`, the schemes `P i` and their displayed pullback squares
  represent `T ×_F X_i`; each projection `v i` is étale and their images
  jointly cover every point of `T`. Individual `q_i` need not be surjective.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`,
  `Scheme.Etale`, and `Scheme.ofArrows_mem_smallEtaleTopology_iff`; its covering
  condition is rendered as étaleness plus joint point surjectivity.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.lift`; the statement uses the
  equivalent `IsPullback` universal-property witness. The slice product
  construction is `Mathlib.CategoryTheory.Limits.Constructions.Over.Products`.
- `Mathlib.AlgebraicGeometry.Limits`: coproduct existence, `sigmaOpenCover`
  and `disjoint_opensRange_sigmaι`, the recorded Mathlib match for
  `lem-weil-pbc-scheme-coproduct-family`; the statement uses the equivalent
  `IsColimit (Cofan.mk ...)` interface rather than a second construction.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `AlgebraicSpace.IsEtale`, `AlgebraicSpace.IsSurjective`; its full signature
  and scheme-test `IsRepresentableWith` definition were read.
- Proof-only project imports are
  `Sheaf.AlgebraicGeometry.RepresentableEtaleFppfLocalLifting`
  (`representable_etale_fppf_local_lifting`) and
  `Sheaf.CategoryTheory.SiteCoveringAxioms` (`Precoverage.IsSiteForCoverings`).
  Other proof dependencies have their recorded Mathlib matches in
  OpenImmersion, Morphisms.Etale and Sites.Fpqc, also imported. Their proof
  uses are carried in the six-step theorem docstring.

Edge cases checked: empty `I` forces empty `S` by `hcover`; coproduct witnesses
then give empty `V,W`, and surjectivity of `q` forces every test pullback empty,
so the final jointly covering assertion is valid. Empty local schemes and empty
overlaps are permitted. Empty test schemes are explicitly included in every
universal property and transition test. There is no separatedness or reducedness
assumption. The identity condition only concerns diagonal sections, including
nonmonic étale covers with nontrivial self-overlaps. The index universe `v` is
independent of `u`, and the coproducts are supplied by their universal properties,
so no universe equality or nonemptiness restriction is imposed. No data are
chosen from a postponed existence theorem.

Searches (2026-10-24): all prescribed `msearch.py` calls used group Q30 and this
item. LeanFinder query “An algebraic space quotient of a scheme descent cocycle
recovers each original chart after base change” returned eight gluing/pullback
lemmas, with no algebraic-space quotient chart theorem. Loogle query
“AlgebraicGeometry.Scheme, CategoryTheory.IsPullback,
CategoryTheory.Limits.prod.lift” returned zero hits. Mathlib grep
“descent.*quotient|quotient.*chart” in AlgebraicGeometry returned zero hits.
LeanSearch query “The charts of a scheme descent datum are recovered by base
change from its algebraic space quotient” returned eight general descent/base
change results, none matching the theorem. `rg` in both `lean/WeilConjectures`
and `lean/Sheaf` for `descent.*quotient|quotient.*chart|schemeDescent|SchemeDescent`
found unrelated chart constructions and the polarized descent theorem, but no
statement of this item. Searching this item's blueprint id in
`lean/WeilConjectures` returned no hits. Read `SchemeCoverDescentDatum.lean` and
`PolarizedSchemeEtaleDescent.lean`: the former concerns sheaf descent data and
the latter the parent theorem with line modules and ampleness. Neither is this
quotient chart theorem. The parent has overlap helper constructions, so this
module deliberately introduces no duplicate overlap definitions; it uses only
Mathlib's universal properties. The original example module CompactObject is
withdrawn in this checkout, so the live algebraic-space and local-lifting
modules supply the current module/header convention.

Validation: the initial module passed both sandbox and canonical-module compiles
through `scompile.py`. The final version is also checked through that wrapper;
no local build or direct compiler invocation was used. No node faults or
statement disputes were found.

## Second reading by Q30

Author's second reading, with the node and final Lean source open; the
maintainer performs the independent review specified by the remote-worker brief.
I checked the normalization against the nontrivial self-overlap case and retained
the diagonal test rather than asserting global identity. I checked every map of
the cocycle against its source and target: `c` has indices `ik`, `d` has `ki`,
and the equality compares morphisms with the same domain and codomain. I checked
the second conclusion against the switched base factors and the third against
both required projections. I checked that the atlas conclusion says joint
surjectivity on all scheme tests, not surjectivity of each member or only a
sheaf epimorphism. The first draft had `I : Type u`; this reading generalized
it to an independent `Type v`, since coproduct universal-property witnesses
already provide the needed objects. No mathematical hypothesis, conclusion,
node field beyond `lean`, definition node, or dependency interface changed.
