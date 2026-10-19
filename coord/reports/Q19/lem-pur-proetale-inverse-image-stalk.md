## Worker report

The delivery states `lem-pur-proetale-inverse-image-stalk` in
`Sheaf.AlgebraicGeometry.ProEtaleInverseImageStalk`, with two named theorems:
`AlgebraicGeometry.Scheme.proEtaleInverseImage_setStalk` and
`AlgebraicGeometry.Scheme.proEtaleInverseImage_abelianStalk`.
Both proofs are `sorry`; no definitions, helper axioms, dependency repairs or new nodes
are introduced. The node changes only in `lean`.

Hypotheses and clauses, matched to Lean:

- Schemes and an arbitrary scheme morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
  There is no finiteness, separation, smoothness or surjectivity hypothesis.
- The chosen compatible size bound: explicit universe `u`, with schemes and the
  geometric field at level `u`, the existing small pro-etale categories at object
  level `u+1` and Hom level `u`, and values in `Type (u+1)` or
  `AddCommGrpCat.{u+1}`. The existing stalk's colimit uses the essentially small
  neighbourhood category in the larger universe. No equality of site object and
  morphism universes is imposed.
- A geometric point in the bound: `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`
  and `(x : Spec (.of Ω) ⟶ X)`. Its image is exactly `x ≫ f`.
- Sets and abelian groups are the two separate theorem coefficient categories.
  `F : Sheaf (ProEt.topology Y) ...` is universally quantified in each.
- The inverse image is exactly the dependency's `proEtaleSheafInverseImage`;
  its unit is that of `proEtaleSheafAdjunction`. No alternative pullback is used.
- The stalks are exactly `proEtaleGeometricStalk`, defined as the colimit of
  `proEtaleGeometricStalkDiagram` over all pointed weakly etale neighbourhoods.
- The comparison is `∃ c : ∀ F, proEtaleGeometricStalk x (f⁻¹F) ≅
  proEtaleGeometricStalk (x ≫ f) F`. Its first conjunct characterizes the canonical
  comparison on germs: for a pointed target neighbourhood `N`, a lift `a` to
  its base change over `x`, whose projection is `N.hom.left`, applying the unit
  section map and then the stalk coprojection and `c.hom` gives the original
  stalk coprojection at `N`. The condition on `a` just identifies the unique
  paired lift by the fibre-product universal property; it is inside the
  universally quantified germ formula, not an extra hypothesis on `f` or `x`.
  This normalization specifies the source's canonical germ comparison, rather
  than existence of arbitrary isomorphisms of unrelated stalk objects.
- Naturality is the second conjunct: `colim.map` of the whiskered inverse-image
  sheaf morphism, followed by `(c G).hom`, equals `(c F).hom` followed by
  `colim.map` of the whiskered original sheaf morphism. Composition `≫` is in
  diagrammatic order, so this is exactly the displayed square in the node.
- Additivity: in the abelian theorem `c F` is an isomorphism in `AddCommGrpCat`,
  so both its hom and inverse are group homomorphisms, with no extra assumption.
- The third conjunct quantifies `h k : F ⟶ G` and assumes equality of their
  inverse images. Its conclusion equates their actual colimit-induced stalk
  maps at `x ≫ f`. Quantifying over every `x` gives every image geometric point,
  without requiring that every geometric point of `Y` lift.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`; the geometric field is `IsAlgClosed` from
  `Mathlib.FieldTheory.IsAlgClosed.Basic` (public through the stalk dependency).
  Read `Scheme.SpecToEquivOfField` in `Mathlib.AlgebraicGeometry.ResidueField` as
  well: the inline field-and-morphism encoding is its geometric-point convention.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: existing `Scheme.ProEt`
  and `ProEt.topology`, exposed through its public imports and the two main
  dependency modules. The recorded derived-category abbreviation is not needed
  for this degree-zero statement.
- `Sheaf.CategoryTheory.SiteCoveringAxioms` publicly supplies the recorded site
  convention and `Sheaf`. Its cohomology components are not needed here.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `proEtaleBaseChange`, `proEtaleSheafInverseImage`, `proEtaleSheafAdjunction`.
  Read their signatures and docstrings; the base change uses the variable factor
  first, so its projection to the original neighbourhood is `pullback.fst`.
- `Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk`:
  `ProEtaleGeometricNeighbourhood`, `proEtaleGeometricNeighbourhoodForget`,
  `proEtaleGeometricStalkDiagram`, `proEtaleGeometricStalk`, and its colimit-size
  instances. Current server source was also checked with `scompile.py --source`.
- `CategoryTheory.Limits.colim.map`, `colimit.ι`, `Functor.whiskerLeft`, and
  `StructuredArrow.mk` are the existing functorial colimit and pointed-index
  constructions, rather than separate stalk definitions.

All already stated proof dependencies are imported. Proof-only imports include
`ProEtaleSheafificationGeometricStalk`, `SiteSheafificationSectionsLocal`,
`IndPrincipalZariski`, `WeaklyEtaleField`, and Mathlib's `Fpqc`, `WeaklyEtale`
and `IsSepClosed`. The module docstrings contain the eight proof steps from the
node, including the fixed-field cover lift, both universal-property maps and
inverse equations, and the naturality/equality argument.

Sources read: [Stacks 05V1](https://stacks.math.columbia.edu/tag/05V1) gives
inverse image/stalk compatibility for morphisms of sites;
[Stacks 0F4F](https://stacks.math.columbia.edu/tag/0F4F) gives the presheaf
colimit comparison. The pro-etale point source
[Stacks 0993](https://stacks.math.columbia.edu/tag/0993) was also opened.
The local Stacks checkout is absent, so these original sources were read online.

Edge cases checked before writing: the empty source has no geometric point, hence
no excluded case; the identity morphism gives the ordinary unit-germ comparison;
empty/terminal set sheaves and the zero abelian sheaf have the expected unique
isomorphism; no nonzero or nonempty sheaf hypothesis appears. Non-surjective
morphisms only assert equality at `x ≫ f`, and the field stays in the fixed bound.
No characteristic, Noetherian or smoothness restriction occurs. Both cases use
all weakly etale pointed neighbourhoods, not only etale ones.

Searches made (the wrapper also records these in `searches.jsonl`):

- `msearch.py leanfinder`: "The geometric stalk of inverse image of a pro etale
  sheaf is naturally isomorphic to the stalk at the image geometric point".
  Eight hits concerning stalks on ringed/topological spaces, no exact match.
- `msearch.py loogle`: `CategoryTheory.GrothendieckTopology.Point.sheafFiberComapIso`.
  Three hits: the general site-point isomorphism and its component equations.
  Read its full signature and docstring in `Sites/Point/Comap.lean`. It uses an
  abstract site point and its comap; identifying these with the recorded geometric
  neighbourhood colimits is precisely additional work, so it is not an existing
  exact statement of this node.
- `msearch.py grep`: `sheafFiberComapIso|pro[Ee]tale.*[Ss]talk|[Ss]talk.*[Ii]nverseImage`
  in `CategoryTheory/Sites`: only the general point-comap declaration above.
- `msearch.py leansearch`: "Geometric stalks commute with the inverse image
  functor on the pro etale site of schemes": service unavailable, Internal Server
  Error; no search verdict inferred from this failure.
- `rg` in the upstream source and `lean/Sheaf`: pro-etale stalk, inverse-image
  stalk and the two proposed declaration names. Existing pro-etale definitions,
  abelian sheafification comparison and unrelated topological/etale stalk results;
  no exact inverse-image comparison. `grep -rn` for this blueprint id in the
  upstream `WeilConjectures` tree found none. Exact proposed names are unused.

No statement correction or mathematical dispute was needed.

Validation uses `scompile.py` and `deliver2.py --no-push`. The initial single-file
compile accepted both theorem types; its docstring line-width warning has been
repaired. The dry-run wrapper recompiles the delivered file and applies the
server's preflight. The worker does not push the delivery; the independent
second reader supplies the second-reading section.

## Second reading by Q19

Independent second reader, 2026-10-16. I read the node and both theorem signatures
with the recorded dependency sources open. The following is my own inventory of
objects, hypotheses and conclusions, with their Lean renderings and verdicts.

1. **Schemes and arbitrary morphism.** `X Y : Scheme.{u}` and `f : X ⟶ Y`
   introduce precisely the schemes and morphism of `def-pc-scheme`. I opened
   Mathlib's `Scheme` declaration, rather than interpreting the name informally.
   There is no added property instance on `f`. Verdict: exact.
2. **Bounded small pro-etale sites.** `ProEt.topology X` and `ProEt.topology Y`
   are the recorded sites. I read `ProEt`, `ProEt.forget`, `ProEt.precoverage`
   and `ProEt.topology` in Mathlib's `AlgebraicGeometry/Sites/Proetale.lean`,
   and the public import and declaration of `ProEtaleDerivedCategory.lean`.
   Objects are weakly etale schemes over the base and covers are the fpqc
   weakly etale covers, with no finite-type restriction. The site has object
   universe `u+1` and Hom universe `u`; neighbourhoods are formed in the larger
   universe. `Type (u+1)` and `AddCommGrpCat.{u+1}` use the selected value bound.
   No equality between the site's two universes is assumed. Verdict: exact
   implementation of the node's compatible size convention.
3. **Geometric point and its image.** `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`
   and `x : Spec (.of Ω) ⟶ X` are precisely the recorded inline convention of
   `def-weil-geometric-point`; I also opened `Scheme.SpecToEquivOfField`.
   Every occurrence of the target point is `x ≫ f`, so it is the prescribed
   composite, with the same field. Verdict: exact; arbitrary characteristic.
4. **Sheaves and coefficient cases.** The two theorems quantify over every
   `Sheaf (ProEt.topology Y) (Type (u+1))` and every
   `Sheaf (ProEt.topology Y) AddCommGrpCat.{u+1}`, respectively. I read
   `SiteCoveringAxioms.lean` and its record's note retaining Mathlib `Sheaf`
   for this component of `def-weil-pbc-sites-and-cohomology`. No module,
   constructibility, torsion or constant-coefficient condition is inserted.
   Verdict: both cases of the node are present.
5. **The inverse image and stalk objects.** I opened the actual declarations
   `proEtaleBaseChange`, `proEtaleSheafInverseImage`, `proEtaleSheafDirectImage`
   and `proEtaleSheafAdjunction` in `ProEtaleInverseImage.lean`. Inverse image
   is the specified Kan-extension/sheafification construction, and its unit
   belongs to that very construction. I independently read
   `ProEtaleGeometricNeighbourhood`, its forgetful functor, the cofilteredness
   and colimit-size instances, `proEtaleGeometricStalkDiagram`, and
   `proEtaleGeometricStalk` in `ProEtaleGeometricStalk.lean`.
   `StructuredArrow (Over.mk x) (ProEt.forget X)` is exactly all pointed
   weakly etale neighbourhoods, and the opposite diagram evaluates the sheaf
   using restrictions. The stalk is its actual colimit in the value category.
   Verdict: the imported objects are the dependency notions, not private copies.
6. **Canonical isomorphism.** `∃ c : ∀ F, ... ≅ ...` gives a simultaneous
   comparison family from the inverse-image stalk at `x` to the original stalk
   at `x ≫ f`, in the stated direction. The first conjunct fixes its value on
   unit germs. I checked the chosen pullback order: the variable neighbourhood
   is first, so `pullback.fst N.right.hom f` projects to `N.right`.
   `a : Over.mk x ⟶ ...` already specifies the other projection to `x`;
   `a.left ≫ pullback.fst ... = N.hom.left` fixes the remaining projection.
   The fibre-product property supplies exactly one such lift. Consequently
   this implication is neither a condition on the scheme morphism nor a
   vacuous choice of lift. The unit section, the coprojection at
   `StructuredArrow.mk a`, and `(c F).hom` compose from `F(N.right)` to
   `F_{x ≫ f}`, equalling the original coprojection at `N`. This is the
   canonical comparison in the source's cocone construction. Verdict: exact
   rendering of 'canonical', without a stronger additional mathematical claim.
7. **Naturality in all sheaf maps.** The second conjunct quantifies over
   `F G` and `h : F ⟶ G`. `colim.map` of the whiskered map of `f⁻¹h`, followed
   by `(c G).hom`, equals `(c F).hom` followed by the colimit map of `h` at
   `x ≫ f`. Since `≫` is diagrammatic composition, this is exactly the node's
   displayed square. Verdict: exact, with a single family `c` for all maps.
8. **Abelian additivity.** The second theorem's `c F` is an isomorphism in
   `AddCommGrpCat`, so both directions are additive homomorphisms. It uses
   colimits in abelian groups, not an arbitrary underlying-set colimit.
   Verdict: precisely the additive clause.
9. **Equality consequence and quantifier order.** The third conjunct quantifies
   over `F G` and `h k : F ⟶ G`, assumes equality of their actual inverse-image
   sheaf morphisms, and concludes equality of the colimit-induced stalk maps
   at `x ≫ f`. The outer theorem already quantifies over every `x`.
   It makes no assertion at a point outside the image and requires no
   surjectivity. Verdict: exact consequence with the required quantifiers.

Source check: the local Stacks checkout is absent. I independently read the raw
upstream `sites.tex` around `lemma-point-functor` (0F4F) and
`lemma-point-morphism-sites` (05V1), and `proetale.tex` around the definition of
pointed weakly etale neighbourhoods, `lemma-cofinal-etale` (0F6B),
`lemma-geometric-lift-to-cover` (0F6C), the stalk definition, and
`lemma-classical-point` (0993), including the surrounding text. The online tag
pages were checked as well. 05V1 assumes a morphism of sites and a source site
point, not finite type, separation, smoothness or surjectivity. The recorded
inverse-image and geometric-stalk dependencies supply those two objects for
any scheme morphism and the fixed geometric point. In particular the warning
after 0993 says classical geometric stalks are not conservative for arbitrary
pro-etale sheaves: the delivered conclusion does not assert conservativity.
No source-based statement correction or citer audit is needed.

Edge cases: an empty source has no `x : Spec Ω ⟶ X`; its vacuous specialization
is correct, not an excluded case. An empty target admits no nonempty source
geometric point over it. Empty set sheaves, the terminal set sheaf and the zero
abelian sheaf require no extra hypothesis. Pointed neighbourhood indexing is
nonempty because `(X,x)` is a neighbourhood, so there is no hidden nonempty
index assumption; the possibility of empty cover families over empty objects
does not discard a pointed object. Identity and non-surjective morphisms are
included. There is no degree `n` or characteristic restriction. The universe
parameter is arbitrary, the geometric field is in the node's chosen bound, and
larger-bound applications are obtained by selecting that bound rather than by
identifying object and Hom universes.

Independent searches used different wording from the worker:

- `msearch.py Q19 lem-pur-proetale-inverse-image-stalk leanfinder
  "The germ of the adjunction unit identifies the fibre of a pullback sheaf at a
  geometric point with the original fibre"`: eight hits, including
  `TopCat.Presheaf.pushforwardPullbackAdjunction_unit_app_app_germToPullbackStalk`
  and `TopCat.Presheaf.germ_stalkPullbackHom`; these are topological presheaves.
- `msearch.py ... loogle '"stalk", "pullback"'`: twelve topological-presheaf
  declarations, including `TopCat.Presheaf.stalkPullbackIso`, whose arguments
  are a map of topological spaces and an ordinary point. Not this statement.
- Independent `rg` over Mathlib, upstream `WeilConjectures`, project
  `lean/Sheaf` and the side `lean/WeilConjectures` framework searched fibre/fiber,
  geometric pullback, stalk inverse image and both proposed full names.
  Existing hits concern topological stalks, etale stalks, the previously
  recorded pro-etale stalk/sheafification definitions and geometric-field
  evaluation. No duplicate of this comparison was found.
- I read all of `Mathlib/CategoryTheory/Sites/Point/Comap.lean`, in particular
  `Point.comap` and `Point.sheafFiberComapIso`. The latter compares the fibre
  of an abstract site point after `comap` with an abstract sheaf pullback.
  It does not construct this pro-etale geometric point or identify the
  composite point with `x ≫ f`, nor directly use the delivered stalk colimits.
  It remains a possible proof tool, not an exact existing declaration of
  this node. The delivered module is therefore retained.

H4/H5/H6/H8/H9 and dependency audit: the delivery has exactly its owning node
and module; it adds no definition node or dependency module needing a separate
stage-1 audit. Both public theorems have `by sorry` as their entire proofs;
there are no definitions, private copies, unbound variables, local notation,
local instances or hidden proofs. Their docstrings carry the source, blueprint
id and all eight proof steps, including separate set/abelian sheafification,
fixed-field lifting, both cocone maps and inverse equations, and naturality.
The main node's `lean.statement` is verbatim the source signature before `:=`;
both declarations are listed in `lean.declarations`. Lines fit 100 characters.
Only `lean` differs from the base node.

Mismatches found: none. I changed no Lean declaration, node statement or
metadata. This second-reading section is the only substantive addition.
Validation: the delivered module is checked with the prescribed `scompile.py`;
the final dry run and delivery additionally apply the wrapper's current
preflight and compilation checks.
