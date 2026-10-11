## Worker report

The module `Sheaf.CategoryTheory.Sites.ZariskiTorsorExtensionPushout` states
`CategoryTheory.Sheaf.Torsor.zariski_torsor_extension_pushout`, with its sole proof `sorry`.
No statement correction, disputed statement, or unusable recorded dependency was found.
The original statement is unchanged. Its `stmt_deps` gains the new definition below.

Hypotheses and objects, clause by clause:

- Scheme X: `(X : AlgebraicGeometry.Scheme.{uE})`.
- Abelian Zariski sheaves G, G', E: `Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{uE}`.
  The scheme and coefficient groups are taken in a common arbitrary universe, with no
  cardinality or finiteness hypothesis. The auxiliary quotient definition independently
  quantifies the scheme and coefficient universes.
- Coefficient morphism: `(φ : G ⟶ G')`; original injection: `(j : G ⟶ E)`.
- Constant integer sheaf: the target of `p` is
  `(constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{uE}).obj
  (AddCommGrpCat.of (ULift.{uE} ℤ))`.
  ULift changes the carrier's universe, not the integer group. This is sheafification of
  the constant presheaf, rather than the generally non-sheaf constant presheaf itself.
- Short exactness: `hjp : j ≫ p = 0` and
  `hE : (ShortComplex.mk j p hjp).ShortExact`. The former is the zero composite needed
  to form a short complex; it is already entailed by the stated short exact sequence.

Conclusion, including the definitions appearing in the node:

- Pushout quotient E_phi: `pushout j φ`. In an abelian category this is canonically the
  cokernel of `g ↦ (j(g), -φ(g))` into E ⊕ G'. The ordered pushout legs are
  `pushout.inl j φ : E ⟶ pushout j φ` and `pushout.inr j φ : G' ⟶ pushout j φ`.
  This uses the standard categorical pushout, with its universal property, rather than
  postulating an unspecified extension or identifying the quotient sectionwise.
- Induced projection: existential `p'`, the equality `pushout.inl j φ ≫ p' = p`, and
  `hz : pushout.inr j φ ≫ p' = 0` specify the projection uniquely by that pushout
  universal property. The induced injection is the second pushout leg.
- New short exact sequence: `(ShortComplex.mk (pushout.inr j φ) p' hz).ShortExact`.
- Original fibre T: existential `T : Torsor G` and `a U`, natural on restriction,
  with `Set.BijOn (a U) Set.univ {e | p.hom.app U e = ... ⟨1⟩}`.
  The right side is precisely the fibre of sections over the constant section 1,
  obtained using `toSheafify` on the constant integer presheaf at every open U.
  BijOn specifies a bijection onto this fibre, including opens where it is empty.
  The action equality `a U (T.vadd U g t) = a U t + j.hom.app U g` is translation
  through j. Thus T is a presentation of the defined fibre, not an extra hypothesis
  about a pre-existing torsor. Natural sectionwise bijections identify sheaves.
- New fibre: `T' : Torsor G'` and `b U` have the analogous naturality, BijOn, and
  translation requirements for p' and the induced injection. These assert precisely
  that its fibre over 1 is a G'-torsor.
- Contracted product: `q : ZariskiContractedProductPresentation X φ T T'` specifies
  natural quotient maps, the relation `(g +ᵥ t, h - φ(g))`, second-factor translation,
  and unique factorization of every natural invariant map into every sheaf of sets.
  This is the sheafified orbit quotient universal property, not a presheaf quotient.
- Canonical identification: the final equality fixes the quotient map by
  `b U (q.quotient U t h) = inl(a U t) + inr(h)`. Consequently the identification is
  the one induced by the pair map into the extension, and respects the G'-action.
  It is not merely existence of an unrelated isomorphism. The two fibre presentations
  and the quotient universal property determine the usual canonical torsor isomorphism.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` (def-pc-scheme).
- `Mathlib.CategoryTheory.Sites.Spaces`: `TopologicalSpace.Opens.grothendieckTopology`
  (def-sc-zariski-site); `TopCat.Sheaf` in `Mathlib.Topology.Sheaves.Sheaf` is the
  synonymous bundled-space sheaf category; the theorem uses its underlying site form.
- `WeilConjectures.CategoryTheory.Sites.Torsor`: `CategoryTheory.Sheaf.Torsor`, its
  sheaf and action fields (def-sc-gm-torsor). Its `lifts` construction was also read;
  no second lifting-torsor definition is introduced. The theorem describes those
  fibres by natural bijections, avoiding file-local notation or auxiliary definitions.
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`: the signature and docstring of
  `CategoryTheory.Sheaf.H'` (def-sc-topological-abelian-cohomology) were read. This
  result uses the abelian category of sheaves, not a cohomology group, so there is no
  H' application in its signature. `Mathlib.CategoryTheory.Sites.Abelian` supplies
  `CategoryTheory.sheafIsAbelian`; standard abelian-category pushouts are used.
- The new module supplies
  `CategoryTheory.Sheaf.Torsor.ZariskiContractedProductPresentation`.

The source was opened at [Stacks 02FQ](https://stacks.math.columbia.edu/tag/02FQ): its
proof uses the constant integer sheaf, a pushout extension, and a fibre torsor of local
lifts. The item supplies the coefficient-change fibre calculation in its three proof
steps. All three are included, with their DAG inputs, in the theorem's docstring.

Edge cases checked before writing: X empty (only the empty open, whose sheaf sections
are singleton); opens with no lift (BijOn correctly permits an empty fibre); φ = id
(the pushout recovers E and the contracted product recovers T); G' = 0 (quotient
extension is the constant integer sheaf, and the fibre is terminal); G = 0 (the original
extension is the integer sheaf); φ = 0 (the split product fibre). No surjectivity of φ,
nonemptiness of X, triviality of T, or existence of global lifts is assumed. The minus
sign agrees with the stated relation and the canonical pair formula.

Searches for the item: `msearch.py leanfinder` with "pushout of an extension of abelian
sheaves fibre over one contracted product torsor" returned eight unrelated
Mayer–Vietoris/gluing results. Loogle query `CategoryTheory.Sheaf.Torsor.lifts, pushout`
returned zero hits (unknown upstream identifier). Mathlib grep query
`contracted product|pushout.*torsor|classH1.*map` returned zero hits. LeanSearch query
"pushout extension abelian sheaves contracted product fibre" was unavailable (Internal
Server Error). The project/source rg searches for the node id, torsor, pushout,
ContractedProductPresentation, and ZariskiContractedProductPresentation found upstream
lifting torsors and the landed étale analogue, but no theorem for this arbitrary
Zariski extension. New-notion searches are recorded verbatim in the new node.

Validation: both modules compile together locally with the required options, no errors
and no warnings. No local notation, private declaration, local instance, auto-bound
variable, or hollow definition is introduced. Only the theorem is left as sorry.

## New nodes

`def-sc-zariski-contracted-product-presentation` defines the coefficient-change quotient
presentation on the small Zariski site, in its own module
`Sheaf.CategoryTheory.Sites.ZariskiContractedProductPresentation`. Source: Stacks 02FQ
and the item's pushout-fibre calculation, step 2. Its full data are the natural quotient
family; proof fields express invariance, residual equivariance, and the universal
property against sheaves. There is no sorry. Existing
`def-sc-contracted-product-presentation` concerns only the étale site; existing
`def-sc-binary-contracted-product-presentation` concerns two torsors under the same
coefficient sheaf. Neither gives change of coefficients on the Zariski site. DAG grep
and `tools/blueprint_refs.py search 'contracted product'` confirmed these scopes;
LeanSearch was unavailable, LeanFinder returned eight unrelated affine-space/gluing
results, Mathlib grep returned no contracted-product declaration, and source/project
rg returned only the differently scoped presentations. The new node records these
searches, the blueprint ancestor lem-sc-pic-proper-ntorsion, and the correct via chain.
Its independent universes cover all scheme/group sizes; its field signature quantifies
every variable explicitly. It is cited by the item's added stmt_dep.

## Earlier second reading (a previous round; superseded)

Pending the independent second worker. This is the author’s dry run; the author has
not performed or claimed the independent reading, and has not delivered the branch.

## Second reading by C1

I independently read the item and its new definition node, both complete modules,
the statements and recorded declarations of all statement dependencies, and Stacks
cohomology.tex, Section First cohomology and torsors (lines 223–335 in the source copy).
The tags table identifies 02FQ as cohomology-lemma-torsors-h1. The preceding torsor
definition allows empty sections on an open and requires nonempty stalks. Lemma 02FQ
assumes only a topological space and an abelian sheaf. It constructs a pushout extension
by the constant integer sheaf and constructs torsors as sheaves of lifts. The arbitrary
coefficient-change quotient calculation is developed in this item's DAG proof; it is
not a separately stated assertion in 02FQ. No hidden scheme property is needed.

My object/hypothesis/conclusion inventory and its Lean rendering:

- Scheme X: `X : AlgebraicGeometry.Scheme.{uE}`. Exact; no separation, finiteness,
  Noetherian, base field, characteristic or nonemptiness assumption.
- Abelian Zariski sheaves G, G', E: `Sheaf (Opens.grothendieckTopology X)
  AddCommGrpCat.{uE}`. Exact. Opens.grothendieckTopology covers an open pointwise
  by open inclusions, precisely def-sc-zariski-site. The recorded TopCat.Sheaf is
  definitionally this category. I opened Scheme's locally ringed/locally affine
  structure and the site and bundled-space sheaf definitions.
- Coefficient morphism and inclusion: `φ : G ⟶ G'`, `j : G ⟶ E`. Exact;
  no injectivity or surjectivity of φ is assumed.
- Projection to the constant integer sheaf: `p : E ⟶ (constantSheaf ...).obj
  (AddCommGrpCat.of (ULift.{uE} ℤ))`. Exact; ULift preserves the integer group.
  This is the sheafification of the constant presheaf, including on disconnected opens.
- Given short exact sequence: `hjp : j ≫ p = 0` and
  `hE : (ShortComplex.mk j p hjp).ShortExact`. Exact. The former only supplies
  the complex identity inherent in short exactness; it adds no mathematical condition.
- Original fibre T over 1, acted on through j: existential `T : Torsor G`,
  restriction-natural family `a`, `Set.BijOn (a U) Set.univ` onto
  `{e | p.hom.app U e = (toSheafify ...).app U ⟨1⟩}`, and
  `a U (T.vadd U g t) = a U t + j.hom.app U g`. Exact. These data identify T
  with the specified fibre as a sheaf with action, rather than assuming a torsor
  unrelated to the fibre. The constant presheaf section ⟨1⟩ gives the canonical 1.
- Pushout extension E_phi: `pushout j φ`, with first leg from E and second leg
  from G'. Exact. In the abelian sheaf category its universal property is that of
  the quotient of E ⊕ G' by `(j(g), -φ(g))`; it is not a sectionwise quotient.
- Induced injection and projection: `pushout.inr j φ`, existential `p'`,
  `pushout.inl j φ ≫ p' = p`, and witness `hz : pushout.inr j φ ≫ p' = 0`.
  Exact. The two leg equations determine p' uniquely by the pushout property.
- New extension is short exact:
  `(ShortComplex.mk (pushout.inr j φ) p' hz).ShortExact`. Exact.
- New fibre is a G'-torsor: `T' : Torsor G'`, natural family `b`, the analogous
  BijOn fibre condition at 1, and translation formula through pushout.inr. Exact.
  Both torsor types use the recorded upstream CategoryTheory.Sheaf.Torsor; I read
  its action laws, bijective_vadd and local-nonemptiness fields. Its general site
  formulation covers this Zariski case without a second torsor definition.
- Contracted product is the sheafified orbit quotient: existential
  `q : ZariskiContractedProductPresentation X φ T T'`. Exact. I checked every
  structure field: quotient_natural; quotient_invariant with `h - φ(g)`;
  quotient_vadd, with residual translation by k; universal, with unique natural
  factorization of every invariant map to a sheaf of sets. Thus it gives the
  sheaf quotient universal property, not merely an invariant map or presheaf quotient.
- Canonical identification of the new fibre: final formula
  `b U (q.quotient U t h) = (pushout.inl j φ).hom.app U (a U t) +
  (pushout.inr j φ).hom.app U h`. Exact. Together with both fibre bijections and
  the quotient property this fixes the canonical equivariant identification,
  not just an unspecified isomorphism. All conclusion clauses refer to the same
  chosen projection and quotient; existential presentations replace canonical
  constructions up to their uniquely specified identification.

The cohomology dependency's recorded H' signature and docstring were opened in
Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean. No cohomology group occurs
in the present conclusion, so H' itself is not applied. The abelian sheaf category
is the one underlying that dependency, using Mathlib's sheafIsAbelian and standard
pushouts. No dependency module is needed. The theorem docstring reproduces all three
DAG proof steps: quotient/pushout and exactness; local pair representatives and the
relation using stalkwise exactness; local lifts and kernel translation making a torsor.

Edge cases: the empty scheme and empty open have singleton sheaf sections (the
constant integer sheaf there is the zero group, so its 1 is also 0). BijOn covers
this case and also genuinely empty fibres over opens without a lift. G = 0,
G' = 0, φ = 0 and φ = identity give the expected trivial/split/unchanged fibres.
No global lift or surjectivity of φ is required. There is no numerical index n,
index family, coefficient ring or characteristic restriction. The universe uE is
arbitrary and is a common ambient universe for X and the abelian sheaves; the new
presentation has independently bound scheme and coefficient universes u,w. I
investigated separating the theorem's universes, but this required additional
sheafification instance infrastructure; a shared arbitrary ambient universe does
not bound the sizes of mathematical objects. I restored the original signature
rather than adding a hypothesis. All variables and universes are explicitly bound.

Independent searches, with different queries from the author:

- LeanFinder: "extension of abelian sheaves integer sheaf change coefficients torsor
  of lifts" returned eight cohomology/abelian-category results, including Sheaf.H,
  Sheaf.cohomologyPresheaf and SheafOfModules.instAbelian, none the pushout-fibre
  theorem or coefficient-change quotient definition.
- Loogle: `CategoryTheory.Sheaf.Torsor` returned no indexed hit (unknown upstream
  identifier). This is an indexing limitation; the source declaration was read directly.
- Mathlib grep through msearch: `changeOfCoefficients|contractedProduct|orbit.*sheaf|
  torsor.*pushout` returned zero hits.
- LeanSearch: "sheaf quotient of a torsor times a coefficient group by translation"
  was unavailable with Internal Server Error; no absence verdict is inferred.
- Direct rg across Mathlib, WeilConjectures and lean/Sheaf for orbit/sheaf,
  torsor/pushout and contracted-product vocabulary found only upstream Torsor's
  TODO/group-law discussion and the project's distinct contracted-product modules.
  I opened ContractedProductPresentation and BinaryContractedProductPresentation
  and their DAG nodes: the former is on the small étale site, the latter has two
  torsors under the same Zariski group, not change of coefficients. Neither can
  state this quotient without a new notion. Blueprint search "contracted product"
  returned lem-sc-line-bundle-torsor and lem-sc-torsor-h1, neither a quotient definition.
  Direct DAG searches found no general-site or Zariski coefficient-change definition.

New-node reading: def-sc-zariski-contracted-product-presentation has the same
scheme/site/morphism/torsor objects and all quotient fields as its Lean structure.
Its source is the coefficient-change calculation of the item's proof step 2,
using the extension/torsor mechanism of Stacks 02FQ. I clarified the source.place
so it does not imply that Stacks separately states this quotient construction.
The definition is absent from the base DAG, Mathlib and source, as checked above.
Its id, kind=definition, status=split, cited statement dependencies, empty proof
and proof_deps, null mathlib_match, searches, created record, lean_audit=none,
chapter/unit and lean record meet the new-node field rule. The item's stmt_deps
cites it. The item records a short immediate blueprint path. The preflight uses
blueprint_refs.chain to expand that path through parent nodes, and this full
path agrees with the new node as the author wrote it. I restored that full
path after checking the preflight implementation; no blueprint change is
needed in the final delivery.

No mathematical mismatch was found in the final theorem. No statement correction
or disputed flag is needed. Changes: clarified the new definition's source attribution and appended this
independent reading. The blueprint path matches the full chain computed from the delivery base. Both modules'
Lean is preserved. There is no hollow definition: the structure consists of genuine
data and laws and contains no sorry. The theorem's sole proof remains sorry, as
stage 2 requires. The headers, namespace, source/blueprint docstrings, line widths,
imports and absence of local notation, private definitions or local instances were
checked. The node lean.statement is the exact final declaration signature.

Validation: both delivery modules compile together locally under autoImplicit=false
and relaxedAutoImplicit=false, with exit code 0 and no errors or warnings. The final
server compile and delivery preflight are run by deliver2.py.
