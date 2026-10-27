## Worker report

Item: `lem-sfb-site-abelian-torsor-h1`, group Q118, stage 2. The module
`Sheaf.CategoryTheory.Sites.SiteAbelianTorsorH1` states
`CategoryTheory.Sheaf.Torsor.site_abelian_torsor_h1`. This is its sole theorem and
sole `sorry`. The surrounding definitions construct the extension and its named
maps; none chooses undetermined data from a postponed existence assertion.

Source read: `literature/stacks-project/sites-cohomology.tex`, the entire
Tag 01FT global-sections paragraph, Tag 03AH definition of torsor, and Tag 03AJ
statement and proof (free abelian pushout and injective-quotient inverse).
The node's eight proof steps are included in the theorem docstring, including
the supplied inverse, arbitrary-extension, and addition verifications.
No statement correction or dispute was needed.

Clause-by-clause correspondence:

- A site small relative to the coefficient universe is `{C : Type u}` with
  `[Category.{v} C]` and `J : GrothendieckTopology C`, with coefficients in
  `AddCommGrpCat.{max u v w}`. `u`, `v`, `w` are explicitly bound and independent.
  An arbitrary extra coefficient universe is allowed; morphism and object
  universes need not coincide. Passing from a covering site to its generated
  topology is the recorded `SiteCoveringAxioms` convention. The theorem applies
  to every Grothendieck topology, so in particular to every such site.
- An abelian sheaf is `G : Sheaf J AddCommGrpCat.{max u v w}`.
- Global sections are the existing `Sheaf.Γ J AddCommGrpCat`, the right adjoint
  to the constant sheaf functor. Mathlib's `ΓNatIsoLim` and `ΓObjEquivHom`
  identify this with compatible sections and morphisms from the terminal sheaf.
  No final object of `C` is assumed, no `HasTerminal C` instance is introduced.
- The requested derived cohomology is literally
  `((Γ J AddCommGrpCat).rightDerived 1).obj G`, not Ext cohomology with an
  unstated comparison. Mathlib `rightDerived` is computed from injective
  resolutions. `siteAbelianSheafify` and `siteAbelianSheafGrothendieck` are
  explicit wrappers of Mathlib's essentially-small-site results; they supply
  sheafification, enough injectives and injective resolutions in this universe.
  They add no mathematical assumption.
- A torsor is the existing `CategoryTheory.Sheaf.Torsor G`. Its `sheaf`, `vadd`,
  `zero_vadd`, `add_vadd`, `map_vadd`, `bijective_vadd`, and
  `nonemptySieve_mem` fields express the sheaf, natural action, its laws,
  simple transitivity, and local surjectivity to the final sheaf. For each
  section `t`, bijectivity of `g ↦ g+t` is precisely bijectivity of
  `(g,t) ↦ (g+t,t)` on pairs; empty section sets are allowed.
- Isomorphism classes are `_root_.Quotient (Torsor.setoid (G := G))`, using
  the existing equivariant `Torsor.Iso` and its existing setoid.
- `siteIntegerPresheaf` is the constant presheaf on `ULift ℤ`, and
  `siteIntegers` is exactly its `presheafToSheaf` sheafification. The lift only
  changes the universe. `siteOneSection` is the image of the integer 1 under
  the sheafification unit; `siteOne` is the compatible global 1 from the
  constant/global-sections adjunction unit.
- `siteFreeSheaf` is sheafification of `T.sheaf.obj ⋙ AddCommGrpCat.free`.
  `siteRelations` is free on pairs. Existing `T.pairsDiff` sends `(x,y)` to
  `[y]-[x]`; existing `T.pairsSub` sends `(x,y)` to the unique `g` with
  `g+x=y`. `siteDifference` and `siteDisplacement` sheafify those maps.
- `siteExtension` is their concrete categorical pushout. In an abelian category
  it is `(G ⊕ ℤ[T])` modulo `(g,[x]-[y])`, where `y=g+x`. Thus its relation
  subsheaf is exactly the locally generated subsheaf specified in the node.
  Every pair has this form by simple transitivity, and conversely `(t,g+t)`
  gives every relation in the node. `siteInclusion` is `pushout.inr`;
  `siteGenerators` is `pushout.inl`; `siteGenerator` applies the latter to `[t]`.
  This avoids repeating the étale-only or Zariski-only construction as an
  unsupported generic choice. This is the same notion constructed directly
  by the owning node, so these are helpers in this module under the human's
  missing-helper authorization, not new independent DAG notions.
- For every `T`, the theorem provides `p`, `hp`, `hS`. `hp` says `p i = 0`;
  `hS : (ShortComplex.mk i p hp).ShortExact` is the entire short exact sequence,
  including monicity, exactness and epimorphic augmentation. The next clause
  says `p.hom.app U (siteGenerator ... t) = siteOneSection J U`.
  Hence this augmentation is fixed by its values on `G` and the generators,
  rather than an arbitrary map substituted for the canonical augmentation.
- The next clause supplies for every `U` an equivalence between `T(U)` and
  `{x : E_T(U) | p_U(x)=1}`, whose value is precisely the generator `[t]`.
  The generator is natural by its actual construction from the unit and a
  sheaf morphism. Its equivariance is separately asserted by the equation
  `siteGenerator ... (T.vadd U g t) = i_U(g) + siteGenerator ... t`.
- `siteBoundary` is the existing derived connecting morphism
  `ShortComplex.ShortExact.rightDerivedδ` at degree 0, precomposed with the
  existing canonical `Functor.toRightDerivedZero`. Its type is from actual
  global sections to the first right derived global sections, and it uses
  `HasDerivedCategory.standard` for the derived-category choices, with no
  extra universes equated. For left-exact Γ the degree-zero map is the inverse
  of `rightDerivedZeroIsoSelf`. It is the derived LES boundary, not an
  uninterpreted function. The formula is `κ ⟦T⟧ = siteBoundary J hS (siteOne J)`.
- `Function.Bijective κ` gives the canonical classification. Canonicity is
  enforced by the formula on every concrete extension, whose augmentation is
  fixed by the generators. Thus choices of injective embeddings are absent
  from the construction of the class; they occur only in its proof plan.
- For every `E`, `i`, `p`, `hp` and short exactness proof `hS`, the next
  quantified clause produces a torsor `P` with an objectwise equivalence to
  the actual sectionwise fibre of `p` over 1. The two following equations give
  naturality and equivariance for the action through `i`. Thus `P` is the
  actual fibre sheaf with its actual action up to specified equivariant sheaf
  isomorphism, and `κ ⟦P⟧ = siteBoundary J hS (siteOne J)` is exactly the
  arbitrary-extension formula. No extension is restricted to be injective.
- `κ ⟦trivial G⟧ = 0` is the requested normalization, using the existing
  trivial torsor, not a private trivialization.
- For every pair `T,T'`, the final clause gives a torsor `S` and quotient
  family `q`. Its equations express naturality, invariance under
  `(t,t') ↦ (g+t,-g+t')`, and the residual action on the first factor.
  For every sheaf `F` and every natural invariant family `a`, it requires a
  unique sheaf morphism `l : S.sheaf ⟶ F` factoring `a`. This is precisely the
  universal property of the sheafification of the sectionwise orbit quotient;
  it uniquely fixes the quotient sheaf and map, rather than merely assuming
  an arbitrary torsor with an additive class. Its residual action is fixed by
  the equivariance equation. The conclusion is `κ ⟦S⟧ = κ ⟦T⟧ + κ ⟦T'⟧`.

Dependency declarations read and used:

- `def-weil-size-convention`: metatheoretic convention; implemented by the
  explicit universe binders and `max u v w` coefficient sizes.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`: the recorded covering-site
  convention and its `Precoverage.toGrothendieck`/`Sheaf` interface. Imported
  publicly, using its recorded Mathlib sheaf convention.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`,
  `CategoryTheory.Injective`; `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`,
  `CategoryTheory.InjectiveResolution`: the object and resolution definitions,
  reached through the derived-functor imports. Read both full definitions.
- `Mathlib.CategoryTheory.Sites.Sheafification`,
  `CategoryTheory.presheafToSheaf`, `toSheafify`, `sheafificationAdjunction`:
  all free sheaves, integers, displacement descent and generators use them.
- `def-sc-gm-torsor`, already landed on
  `WeilConjectures.CategoryTheory.Sites.Torsor`,
  `CategoryTheory.Sheaf.Torsor`: its declaration is general-site even though
  its DAG node originally arose for units torsors. Its module is publicly
  imported and its node is added to `stmt_deps` under the landed-dependency
  authorization. Its `Iso`, `setoid`, `trivial`, `pairs`, `pairsDiff`, and
  `pairsSub` are reused directly.
- Existing proof dependencies with Lean statements are imported as proof
  imports: `WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor`
  (`Functor.exists_universal_rightDerived_deltaFunctor`) and
  `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`
  (`CategoryTheory.sheafification_sections_local`). Mathlib proof leaves
  (sheafification exactness, Grothendieck enough injectives, derived comparison,
  epi/local-surjectivity, local-bijective/isomorphism) are available through
  the relevant imports, rather than restated.
- Existing `Sheaf.Γ` and `constantSheafΓAdj` in
  `Mathlib.CategoryTheory.Sites.GlobalSections`; its additive instance in
  `WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections`;
  `ShortComplex.ShortExact.rightDerivedδ` in
  `WeilConjectures.CategoryTheory.Abelian.RightDerived.Connecting`.

Edge cases checked before finalizing:

- Empty site: sheaf categories and global-section limits remain defined;
  torsor class sets and cohomology degenerate correctly. No object is selected.
- No terminal object (for example a site with two disconnected objects):
  neither Γ nor its boundary is replaced by evaluation at an object.
- Torsor with no global section: no `Nonempty T(U)` assumption occurs;
  local nonemptiness is exclusively the existing torsor field.
- Object covered by the empty sieve: local nonemptiness does not force a
  nonempty covering index type. All sheaf fibres are still correctly encoded.
- Zero coefficient sheaf: the trivial torsor and zero H¹ fit every clause.
- Nontrivial short exact extensions: no splitting or injectivity of E is
  assumed. Only `hS.ShortExact` is used in the universal extension clause.
- The contracted-product sign was checked on local coordinates `(g,h)`:
  `(g+a,h-a)` has invariant coordinate `g+h`, and residual translation adds
  to that coordinate, agreeing with the asserted addition rather than subtraction.
- Larger coefficient universe: server compilation tested three independent
  levels `u,v,w`, retaining `max u v w` throughout; no extra universe equality.

Searches made:

- `msearch.py ... leanfinder "Abelian sheaf torsors classified by derived first
  cohomology boundary of one on a site"`: eight hits, including `Sheaf.H` and
  `PresheafOfGroups.H1`. These are Ext cohomology and fixed-family nonabelian
  Čech cohomology, not the requested package.
- `msearch.py ... loogle '"Torsor", "H"'`: zero hits.
- `msearch.py ... grep '[Tt]orsor|classH1' CategoryTheory/Sites`: zero hits.
- `msearch.py ... leansearch "Abelian sheaf torsors correspond to first right
  derived global section cohomology on a site without final object"`: eight
  hits, including `Sheaf.H`, `Sheaf.Γ`, Grothendieck sheaf categories, and
  nonabelian H1; no classification theorem with these conclusions.
- `rg` of torsor, cohomology, global sections, free extensions and contracted
  products in the Mathlib site tree, project `lean/Sheaf`, and source
  `lean/WeilConjectures`: found the general torsor definition and terminal-site
  `Torsor.classH1`, and the étale/Zariski specialized extension constructions.
  Read `Torsor.lean`, `ZariskiTorsorFreeExtension.lean`,
  `TorsorExtensionPresentation.lean`, `ContractedProductPresentation.lean`,
  `GlobalSections.lean` and the derived connecting definition. No existing
  declaration has the node's general site, derived target and full package.
- Search for the item id in `lean/WeilConjectures`: no matches. New declaration
  names were checked in Mathlib, WeilConjectures, Sheaf and
  `dag/lean_names_upstream.json`; no exact name conflicts.
- Inspected the existing DAG dependency records, including the existing
  torsor node, so no new definition node duplicates a recorded notion.

Validation: the final module was compiled through the prescribed `scompile.py`
server wrapper in both module checks, cleanly, with no errors or warnings.
The only theorem is deliberately postponed for stage 3. No live source or
shared repository file was edited, and no direct git command was run.

## Second reading by Q118

This is the dispatcher's worker's second pass, not a claim of an independent
worker review; the brief forbids spawning another agent and specifies the
maintainer's independent reading of the delivery. I reopened both the node and
completed file and checked the correspondences above. The first compiler pass
revealed generic universe-instance inference gaps; the final file supplies
existing Mathlib witnesses explicitly and keeps all three universe levels.
The earlier draft used a subtype witness inside the theorem signature; this
was replaced by an equivalence whose underlying function is explicitly `[t]`,
so the final signature contains no postponed proof. No hypotheses restrict the
site to have a terminal object, the torsor to have sections globally, or an
extension to split. Checked the actual pushout relation orientation against
`T.pairsSub` and the antidiagonal sign in the last clause. The universal
factorization clause tests all sheaves of sets in the coefficient universe.
Every non-theorem body is real data, and only the main theorem uses `sorry`.
