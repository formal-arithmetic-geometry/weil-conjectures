## Worker report

The module states `CategoryTheory.Sheaf.Torsor.etale_torsor_inverse_image_extension`;
its sole proof is `sorry`. No definition is copied or introduced. The existing landed node
`def-sc-torsor-extension-presentation` is added to `stmt_deps` to express the canonical
extension, exactly as the sibling pushout theorem does.

Hypotheses and clauses:

- Schemes X and Y, and arbitrary scheme morphism u: binders `X Y : Scheme.{u}` and
  `f : Y ⟶ X`. No properness, flatness, connectedness, or nonemptiness is imposed.
- Abelian sheaf G on the small étale site: `G : Sheaf X.smallEtaleTopology
  AddCommGrpCat.{u + 1}`.
- G-torsor T: the recorded `Sheaf.Torsor G`, with its sheaf, action, simple transitivity,
  and local nonemptiness. `E : ExtensionPresentation.{u, u} X T` gives the canonical
  quotient, inclusion, natural generators, relation, augmentation, and quotient universal
  property. Its universal property is equivalent to the construction in Tag 03AJ, not an
  arbitrary extension or an assumption about an unspecified map.
- The set inverse image with its transported action is a torsor: existential `T'` under
  `(Etale.upperStar AddCommGrpCat f).obj G`, and `eT` identifying its sheaf with
  `(Scheme.etaleSetPullback f).obj T.sheaf`. The first universal equation sends the
  pulled-back action on g and t to the action of the pulled-back g on the pulled-back t.
  Set sections use the set adjunction unit, and group sections the abelian adjunction
  unit. These equations are for EVERY étale object W and every pair of sections, not just
  global sections. They characterize the pulled-back action: the adjunction unit sections
  generate inverse image locally, and finite-limit preservation identifies inverse image
  of a product with the product of inverse images. Given local sections of both factors,
  represent them locally on base-changed objects and refine to a common fibre-product
  object before applying the displayed equality. Thus no arbitrary action is admitted.
- The identification of inverse image of the constant integer quotient with Z_Y is `γ`.
  Its equation on every integer n and every W identifies pulled-back constant sections
  with constant sections. Sheafification and the adjunction make this precisely the
  canonical constant comparison, including 1, not an arbitrary automorphism of Z.
- The pulled-back sequence is short exact: the existential `hz` binds the zero composite,
  and `ShortComplex.mk (upperStar.map E.inclusion)
  (upperStar.map E.projection ≫ γ.hom) hz |>.ShortExact` is the full assertion. No
  short-exactness hypothesis is added: the canonical presentation forces the original
  sequence to be short exact, by its local description G ⊕ Z.
- The extension attached to the inverse-image torsor exists: `∃ E' :
  ExtensionPresentation Y T'`. This includes the quotient universal property, so it is
  E_{u⁻¹T}, not just an extension with the same class.
- Unique isomorphism of extensions: `∃! e : (upperStar ... f).obj E.middle ≅ E'.middle`.
  The inclusion square is `upperStar.map E.inclusion ≫ e.hom = E'.inclusion`, expressing
  identity on u⁻¹G. The quotient square is
  `e.hom ≫ E'.projection = upperStar.map E.projection ≫ γ.hom`.
- Canonical images of generators: the third condition on e, at every W and t, sends the
  abelian-unit pullback of `E.generator W t` to `E'.generator` of the set-unit pullback
  of t under eT. This is exactly `u⁻¹[t] ↦ [u⁻¹t]`. Naturality, local generation of inverse
  image, and the quotient universal property extend this prescription to all local
  sections of the inverse-image torsor.
- Identity on fibres: `Set.BijOn (fun t => e.inv.hom.app U (E'.generator U t)) Set.univ`
  onto sections whose pulled-back projection is the constant 1. This identifies the
  pulled-back fibre with T' by the inverse-image generator, and e sends this very element
  to the generator of the same t in E'. Hence its restriction is the identity of the
  inverse-image torsor under these canonical fibre identifications.
- Action compatibility on fibres: the last condition, for ALL Y-side étale objects U,
  g and t, equates the generator of `T'.vadd U g t` with the generator of t plus
  `(upperStar.map E.inclusion).hom.app U g`. It explicitly renders equivariance with
  respect to the u⁻¹G-translation action.

Dependency declarations inspected and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and scheme morphisms.
- Mathlib.AlgebraicGeometry.Sites.Etale: `Scheme.smallEtaleTopology`.
- Mathlib.CategoryTheory.Sites.Sheaf: `CategoryTheory.Sheaf`, the full subcategory
  of presheaves satisfying the sheaf condition.
- WeilConjectures.CategoryTheory.Sites.Torsor: `Sheaf.Torsor`, including all its fields;
  `Sheaf.nonempty_equiv_H_one_torsor` has only a nonempty bijection and does not expose
  the quotient extension. The quotient notion already exists on sheaf-dag, so there is
  no need to duplicate or restate that cohomology theorem in this delivery.
- Sheaf.CategoryTheory.Sites.TorsorExtensionPresentation: `Sheaf.Torsor.ExtensionPresentation`;
  read the complete declaration and docstring. It provides the required canonical
  quotient notion, generators, and maps; this landed node is added to the dependencies.
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs: `Etale.upperStar`,
  `Etale.upperStarLowerStarAdjunction`, and the definitionally base-change-evaluated
  `Etale.lowerStar` (full signatures and docstrings read).
- Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures:
  `AlgebraicGeometry.etaleInverseImageAlgebraicStructures`; its abelian/set unit
  agreement explains the two section pullbacks in the statement. Its imports supply
  `Scheme.etaleSetPullback` and the recorded inverse-image definitions.
- Sheaf.AlgebraicGeometry.EtaleInverseImageExact: `Etale.upperStar_abelian_exact`
  (read full source and signature); its exactness is used by proof step 1.
- Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheaf:
  `AlgebraicGeometry.etaleSetInverseImageConstantSheaf` (read full signature and
  docstring); the displayed integer comparison is its abelian lift.

Edge cases: empty schemes/sites, the zero abelian sheaf, trivial torsors, identity
morphisms, and morphisms with no flatness or properness conditions are included.
No local section of T is assumed globally; the unit equations quantify over sections
when they exist. No chosen trivialization is supplied. Coefficients use the project's
standard u+1 universe; all universes and variables are explicitly bound. Objects on
which a torsor has no section are allowed by `Torsor` and its local-nonemptiness field.

Searches (all real tool searches are recorded in searches.jsonl):

- msearch.py leanfinder: inverse image of torsor canonical abelian sheaf extension is
  extension of inverse image torsor. Eight sheaf-Hom, module-Hom, coherent-comparison,
  and module pullback results; none is this theorem.
- msearch.py loogle: `CategoryTheory.Sheaf.Torsor, Functor.mapIso`. Unknown Torsor
  identifier; zero matches.
- msearch.py grep: `torsor.*(pullback|inverse)|ExtensionPresentation`, restricted to
  Mathlib/CategoryTheory/Sites. Zero matches.
- msearch.py leansearch: An inverse image functor on sheaves sends the canonical torsor
  extension to the canonical extension of the inverse image torsor. Service unavailable
  (Internal Server Error); no mathematical verdict inferred from that failure.
- rg on WeilConjectures for inverse torsor, upperStar Torsor, extension, and 03AJ:
  no declaration for this statement or quotient extension. The Torsor module only gives
  torsors, lifting torsors, and existence of the cohomology/Ext bijections.
- rg on lean/Sheaf and DAG: found the already landed ExtensionPresentation and the
  sibling EtaleTorsorPushoutExtension, and used the former. No inverse-image-extension
  statement exists. The proposed full theorem name has no upstream or Mathlib match.
- Exact node-id search in WeilConjectures: no match. The upstream name index has no
  matching declaration. No new definition node is needed.

Source checked: [Stacks Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ), especially
its free abelian sheaf and pushout construction of E. The local literature source named
by the node is not installed on this machine; the official tag was read directly.
The node's functoriality is the standard naturality of that construction, spelled out
in its three existing proof steps. No statement correction or disputed statement.

Validation: the remote single-file compiler passed with no errors or warnings before
recording the final node. The final delivery dry run is run after this report.

## Second reading by U1

Independent reading: opened the item JSON, its complete three-step proof, the delivered
Lean module, every statement dependency's node and recorded declaration, and the landed
`ExtensionPresentation` node and module. No mathematical mismatch found; the Lean and
node record are retained. This section is the only delivery change in the second reading.

Source: read [Stacks 03AJ](https://stacks.math.columbia.edu/tag/03AJ) and fetched the official
`sites-cohomology.tex` into the item's scratchpad. Read `lemma-torsors-h1` and the chapter
introduction: the construction assumes a site, an abelian sheaf and a torsor, with no
Noetherian, characteristic, nonemptiness, or finiteness restriction. The node states the
naturality of that construction, rather than claiming this naturality is explicitly a
separate assertion in 03AJ. The source pushout identifies differences of generators with
G; the recorded quotient universal property is the same construction.

Object/hypothesis/conclusion checklist, in the node's order:

1. Arbitrary schemes X,Y and morphism u:Y→X: `(X Y : Scheme.{u}) (f : Y ⟶ X)`.
   Verdict: same objects, no property assumed on f.
2. Abelian sheaf G on the small étale site: `G : Sheaf X.smallEtaleTopology
   AddCommGrpCat.{u + 1}`. Verdict: recorded site and abelian sheaf category.
3. G-torsor T: `T : Torsor G`. Opened the structure: it includes the natural action,
   zero/addition laws, sectionwise simple transitivity conditional on a chosen section,
   and the covering nonempty sieve. Verdict: local triviality, not global nonemptiness.
4. Canonical extension E_T with inclusion, integer augmentation, and generators:
   `E : ExtensionPresentation.{u, u} X T`. Read all its fields against
   `def-sc-torsor-extension-presentation`: the natural generators and their action relation,
   quotient universal property for every A,k,j, and augmentation are precisely the
   canonical quotient. Verdict: not an arbitrary extension or an extra exactness axiom.
   Any canonical presentation is allowed; its universal property fixes it up to a unique
   generator-preserving isomorphism. Local trivialization gives G ⊕ Z, so the original
   exactness and fibre clause require no added hypothesis.
5. Inverse-image set sheaf with inverse-image action is a torsor: existential `T'` under
   `(Etale.upperStar AddCommGrpCat f).obj G`, and the sheaf iso `eT` from
   `(Scheme.etaleSetPullback f).obj T.sheaf`. The first equation for every W,g,t is the
   action equation on adjunction-unit pullbacks. Verdict: the transported action is
   specified, not arbitrary. Every section of set inverse image locally comes from a
   unit section restricted along an arrow into a base-change object. For a pair g,t,
   refine their presentations to a common object by a fibre product; restrict the equation
   there. The abelian/set unit comparison in `etaleInverseImageAlgebraicStructures`
   then identifies this with inverse image of the original action via product comparison.
6. Constant integer comparison: `γ` is an iso from the abelian inverse image of Z_X
   to Z_Y; its equation for every W,n fixes the constant-presheaf generators after the
   adjunction unit. Verdict: canonical identification including 1; the equation excludes
   a sign change. Local generation and sheafification determine this comparison.
7. The pulled-back sequence is short exact: existential `hz` supplies its zero composite,
   followed by `(ShortComplex.mk (upperStar.map E.inclusion)
   (upperStar.map E.projection ≫ γ.hom) hz).ShortExact`.
   Verdict: the precise two pulled-back arrows, with Z_Y quotient, and full short exactness
   asserted in the conclusion, not assumed.
8. Extension attached to inverse-image torsor: `∃ E' : ExtensionPresentation Y T'`.
   Verdict: same canonical quotient notion. Existential presentation is appropriate because
   this node fixes the construction by universal property, not by a chosen representative.
9. Unique isomorphism of extensions: `∃! e : (upperStar ... f).obj E.middle ≅ E'.middle`.
   Its first equation fixes G, and second equation fixes the quotient through γ.
   Verdict: both squares and uniqueness are present; uniqueness also requires the following
   generator condition, as the node does (extension automorphisms alone need not be unique).
10. Generator prescription: the equation for all W,t sends the abelian-unit image of
    `E.generator W t` to `E'.generator` of the set-unit image under eT.
    Verdict: `u⁻¹[t] ↦ [u⁻¹t]`, with local restriction implicit in naturality.
11. Fibre over 1 and identity on the torsor: for every Y-side U, `Set.BijOn` sends
    t to `e.inv.hom.app U (E'.generator U t)` and identifies its range with the
    fibre of the pulled-back projection over the sheafified constant 1. Applying e sends
    this section to the generator of the same t; the preceding generator equation makes
    this the canonical inverse-image fibre identification.
    Verdict: identity under canonical fibre identifications, not only equality of classes.
12. Compatibility with actions on fibres: last equation for all U,g,t says the inverse
    image of the generator of `T'.vadd U g t` equals the inverse image of the generator
    of t plus the pulled-back inclusion applied to g.
    Verdict: translation by u⁻¹G explicitly respected.

Dependency inspection: `Scheme`/`Hom`, `smallEtaleTopology`, and Mathlib's `Sheaf`
(full subcategory of sheaf presheaves) give the node's schemes, site and category.
Read `Torsor` and `nonempty_equiv_H_one_torsor`: the latter does not encode the quotient
presentation, which is supplied by the existing landed definition node rather than a
private replacement. Read `Etale.upperStar`/`upperStarLowerStarAdjunction`, whose direct
image evaluates on base change; `Scheme.etaleSetPullback` is the same construction for
sets. Read the complete algebraic-structures comparison, exactness theorem, and constant
sheaf comparison: they provide the tools claimed by the three docstring proof steps.
No new definition node or dependency module is delivered. Adding the already landed
`def-sc-torsor-extension-presentation` is permitted by the current stage-2 dependency rule.
No statement correction record is present or needed.

Edge cases: the zero abelian sheaf, trivial torsor, identity map, empty schemes, and
objects with no torsor sections are all admitted. For the empty scheme the empty-cover
sheaf condition makes the relevant section groups trivial; the constant 1 also equals 0
there, so the fibre clause is consistent. No global torsor section is required. No index
set or degree n occurs; the constant comparison quantifies over every integer including
0 and negative integers. No characteristic or base field occurs. The sole universe u is
explicit; coefficients and set sheaves use the recorded u+1 convention. It is universe
polymorphic and includes arbitrary larger data by choosing u larger, with no independent
small test universe or additional typeclass hypothesis. Every variable is bound.

Independent searches (new queries, also logged by msearch.py):

- LeanFinder: `pullback of a sheaf torsor preserves its free abelian quotient presentation`.
  Eight free-module/sheaf pullback results, none a torsor-extension comparison.
- Loogle: `CategoryTheory.Sheaf, CategoryTheory.Functor.map`. Twelve generic sheaf
  composition/sheafification results, none the statement.
- rg of Mathlib Sites, all upstream WeilConjectures, project lean/Sheaf, and the upstream
  name index for torsor with upperStar/inverse image/extension presentation and pullback
  with torsor. Found `Scheme.EtaleTorsor.pullback` and inspected its declaration: finite
  constant-group geometric torsors, with connectedness assumptions, not arbitrary abelian
  sheaf torsors or their extensions. Found the sibling `EtaleTorsorPushoutExtension` and
  the shared `ExtensionPresentation`; neither states this inverse-image theorem. No name
  collision or existing statement was found. The worker's three search kinds remain in
  place; these are additional independent concept and declaration checks.

H5/H6/H8/H9: the module introduces no definition, proves nothing, and has exactly the
named theorem with `sorry`. Its source and blueprint markers occur in both docstrings;
its proof follows all three node steps with dependency names. No file-local notation,
instance, private copy, hidden let/show binder, unused binder warning, or overlong line.
The node's recorded signature agrees verbatim with the file. Server single-file compile
passed with exit code 0 in 3.7 seconds and no warnings. Delivery preflight is run below.
