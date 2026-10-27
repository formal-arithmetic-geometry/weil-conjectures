## Worker report

The module states resolution pullback on global cohomology for a geometric morphism,
including independence of both resolutions and comparison maps, coefficient naturality,
degree-zero normalization, exactness of the image sequence, and compatibility with the
actual derived connecting maps. Only the theorem `pullback_delta` is postponed; its docstring contains the full
seven-step natural-language proof. All auxiliary definitions
have real data. The sheafification and global-section infrastructure is obtained from
Mathlib, rather than added as mathematical hypotheses.

Source read: `literature/stacks-project/sites-cohomology.tex`,
`section-cohomology-sheaves` (01FT), explicitly including its paragraph without a final
site object, and `remark-before-Leray` (08J6); `cohomology.tex`,
`lemma-functoriality` (01F8); `derived.tex`, `lemma-higher-derived-functors` (015B).
The node is not a blueprint unit's own statement and needs no statement correction.

Hypothesis and clause correspondence:

- Sites: `C`, `D`, their category structures and `J`, `K : GrothendieckTopology`.
  A Grothendieck topology gives the sheaf category of a presenting site; the recorded
  `SiteCoveringAxioms` module is imported. The universes `uC`, `vC`, `uD`, `vD` are independent.
  `[EssentiallySmall.{w} C]` and `[EssentiallySmall.{w} D]` express smallness
  relative to the coefficient universe `w`, allowing objects in `Type (w + 1)`
  and different object/morphism bounds on the two sites. The coefficient category
  is `AddCommGrpCat.{w}`. No `UnivLE` assumption remains.
- Geometric morphism: `f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w))`;
  its actual adjunction and preservation of finite limits are the recorded structure.
- Induced abelian inverse image: `A : AbelianInverseImagePresentation f.inverse`.
  Its natural underlying-sheaf comparison and graph normalizations specify applying
  `f.inverse` to the actual group operations and maps. This is a presentation of the
  induced lift, not a free exact functor. The landed, proved
  `(GeometricMorphism.geometric_inverse_image_exact J K f).2.1 A` gives
  finite-limit and finite-colimit preservation. `inverseLeftExact` and
  `inverseRightExact` project these conclusions; `inverseAdditive` uses preservation
  of binary products to supply additivity. No preservation of injectives is assumed.
- Global sections: the existing `Sheaf.Γ` is used. `sectionGraph J F x` is the same
  section as a morphism from `Sheaf.terminal J Types.isTerminalPUnit`, built from
  `F.ΓRes`; its components are exactly the compatible section family. `terminalIso`
  is the unique terminal-object comparison supplied by `f.leftExact`.
- Cohomology: `(Sheaf.Γ J AddCommGrpCat).rightDerived q`, and likewise for K.
  The three `HasDerivedCategory` instance parameters choose the localizations in
  arbitrary universes `dC`, `dD`, `dA`; they do not change any cohomology or impose
  an equality between the site and coefficient universes.
- Unit/global-section identification: the first conjunct specifies `t` on EVERY global
  section by the equality of terminal-sheaf graphs with
  `terminalIso.inv ≫ f.inverse.map (sectionGraph J F x) ≫ A.underlying.inv.app F`.
  Adjunction identifies this with the unit followed by the global-section
  direct-image identification; it introduces no site functor or final site object.
- For EVERY `F`, `I : InjectiveResolution F`, and target resolution `R`, the second
  conjunct gives a comparison `β`, with
  `A.functor.map (I.ι.f 0) ≫ β.f 0 = R.ι.f 0`. This is precisely augmentation over
  the identity of `LF`, since the other components of the single complex vanish.
- Resolution construction and independence: the third conjunct ranges over EVERY
  such `I`, `R`, `β` satisfying that equation and EVERY `q : ℕ`. It identifies the
  single family `(P q).app F` with `resolutionMap ... I R β q`. That definition is
  `I.isoRightDerivedObj.hom`, homology of `t_I` followed by `Γ(β)`, and
  `R.isoRightDerivedObj.inv`, with Mathlib's explicit composition comparison between
  termwise functors. Thus changing either resolution or β leaves the same map.
- Naturality in F is the type of `P q`, a natural transformation from source cohomology
  to `A.functor ⋙` target cohomology. It covers every coefficient map on the source.
- Degree zero: the fourth conjunct conjugates `(P 0).app F` by the actual
  `rightDerivedZeroIsoSelf` identifications, obtaining `t.app F`; the first conjunct
  therefore makes it the specified inverse image of a global section.
- The fifth conjunct gives `(S.map A.functor).ShortExact` for EVERY short exact S,
  then states the boundary square in categorical composition order for every q.
  The boundary is `ShortComplex.ShortExact.rightDerivedδ`, read in the upstream
  `RightDerived.Connecting` module: its definition applies the derived functor to
  the single-object distinguished triangle and conjugates its homology boundary
  by `singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso`. It is not
  an arbitrary universal delta-functor boundary or a freely chosen family.
- The last two conjuncts give the exact boundary-naturality equation for every
  `φ : S ⟶ T` on the source site and on the target site, respectively.
- No final object of C or D and no functor C → D occur among the parameters.

Dependency declarations read and used:

- `def-weil-size-convention`: metatheoretic record, rendered by explicit universes
  and `EssentiallySmall.{w}`; there is no Lean object attached to that convention.
- `def-weil-pbc-sites-and-cohomology`: `CategoryTheory.Precoverage.IsSiteForCoverings`
  in `Sheaf.CategoryTheory.SiteCoveringAxioms`, together with the retained Mathlib
  `GrothendieckTopology`, `Sheaf` and cohomology conventions documented there.
- `def-trf-geometric-morphism`: `CategoryTheory.GeometricMorphism` in
  `Sheaf.CategoryTheory.Sites.GeometricMorphism`; inverse, direct, adjunction and
  `leftExact` were read in full.
- `def-sp-injective-resolutions`: `CategoryTheory.Injective` in
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic` and
  `CategoryTheory.InjectiveResolution` in
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`; its fields are the
  nonnegative complex, termwise injectivity, augmentation and quasi-isomorphism.
- Added existing statement dependency `def-trf-abelian-inverse-image-presentation`:
  `CategoryTheory.AbelianInverseImagePresentation` in its recorded module. Its full
  `underlying`, `map_add` and `map_zero` fields were read. This adds no new node.
- Added existing statement dependency `lem-trf-geometric-inverse-image-exact`:
  `CategoryTheory.GeometricMorphism.geometric_inverse_image_exact` in
  `Sheaf.CategoryTheory.Sites.GeometricInverseImageExact`. Its complete signature
  and docstring were read; its second conjunct applies to every normalized abelian
  inverse-image presentation. The theorem is proved in the live library.
- All recorded proof-dependency modules are imported, including the horseshoe,
  homotopy, derived-triangle comparison and boundary-naturality interfaces.

Edge cases checked mathematically before writing: q = 0 (the source and target
normalizations have the correct directions); F = 0; split and zero short exact
sequences; identity geometric morphism and identity comparison; different resolutions
and arbitrary augmented comparisons (the universal quantifiers do not pick convenient
ones); sites without final objects, including an empty category; independent site universes and essentially-small sites whose object universe
is above the coefficient universe (including the universe shape of an étale site). No negative degree is claimed or excluded from the
node's nonnegative range. The image of an injective under inverse image is NOT assumed
injective. Exactness, not such a false assumption, is what makes its augmented complex
acyclic in positive degrees.

Searches actually run:

- `msearch.py grep`: `globalSections|[Cc]onnecting|[Pp]ullback`; 1 hits; Mathlib/CategoryTheory/Sites/SheafCohomology/MayerVietoris.lean. No exact match for the full cross-category resolution statement.
- `msearch.py loogle`: `CategoryTheory.NatTrans.rightDerived, CategoryTheory.Sheaf.H`; 0 hits; no hits. No exact match for the full cross-category resolution statement.
- `msearch.py leanfinder`: `Geometric morphism exact inverse image pullback of global sheaf cohomology respects connecting homomorphisms`; 8 hits; SheafOfModules.conjugateEquiv_pullbackComp_inv, SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom, SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom_assoc, SheafOfModules.pullbackComp, TopCat.Sheaf.pullbackIso, CategoryTheory.GrothendieckTopology.MayerVietorisSquare.shortComplex_exact, SheafOfModules.pullbackObjFreeIso_hom_naturality, SheafOfModules.pullbackObjFreeIso_hom_naturality_assoc. No exact match for the full cross-category resolution statement.
- `msearch.py leansearch`: `A geometric morphism induces natural pullback maps on global sheaf cohomology, independent of injective resolutions and commuting with connecting homomorphisms`; 8 hits; TopCat.Sheaf.pullback, CategoryTheory.GrothendieckTopology.overMapPullback, SheafOfModules.pullback, CategoryTheory.Sheaf.ΓRes_naturality, CategoryTheory.Sheaf.ΓObjEquivSections_naturality, SheafOfModules.pullbackPushforwardAdjunction, CategoryTheory.Sheaf.ΓHomEquiv_naturality_left, AlgebraicGeometry.SheafedSpace.Γ. No exact match for the full cross-category resolution statement.
- `rg` in `lean/WeilConjectures/CategoryTheory`, `lean/Sheaf/CategoryTheory`, and
  Mathlib sheaf-cohomology modules for geometric morphisms, global sections, abelian
  inverse image, connecting maps and pullback found the recorded geometric and lift
  interfaces and site-functor cohomology theorems, but no theorem of this statement.
- `rg` for the exact node id in `lean/WeilConjectures` gave no hit; the `lean/Sheaf`
  hit is a downstream Picard naturality proof docstring, not an existing declaration.
- `rg` for `ToposCohomologyPullback`, `pullback_delta`, `resolutionMap`, `sectionGraph`
  in the relevant upstream/project modules and `dag/lean_names_upstream.json` found
  no pre-existing name to conflict with the new namespace.

No STATEMENT-DISPUTED flag or node correction is needed. No dependency is replaced.

## Second reading by Q29

I reread the node and the full module after drafting, matching the hypotheses and
clauses above. In particular I checked the comparison direction `LI → R`, the
augmentation's identity normalization, the direction of both resolution isomorphisms,
the boundary square's composition order, the use of the actual derived boundary, and
separate boundary naturality on both sites. The returned version incorrectly imposed a common object/morphism universe
and `UnivLE`; the repaired version uses essentially-small transport for sheafification,
limits and the Grothendieck property with independent universes on both sites. No source-based mathematical correction was made.
This is the dispatcher's single-worker delivery; the maintainer supplies the independent
review, as specified in the brief. No other agent was started.

## Returned-delivery repair

The returned immutable head was `c4c8a1e4c703`. Comparing its retained sandbox
node with current main showed only the prior added presentation dependency and
Lean record; current main has no Lean record for this item. The accepted natural-language
statement, proof and proof dependencies remain unchanged.

1. H4 + H2: removed the duplicate sorried `inverse_exact` declaration and its
   record entry. Added the landed `lem-trf-geometric-inverse-image-exact` to
   `stmt_deps` and publicly imported its module. Both exactness instances now
   project `(geometric_inverse_image_exact J K f).2.1 A`; additivity follows
   from its finite-product preservation. Only the item's theorem remains sorried.
2. H3: replaced the shared `u`, `v` and `UnivLE` with independent
   `uC`, `vC`, `uD`, `vD` and `EssentiallySmall.{w}` on each site.
   Sheafification uses `hasSheafifyEssentiallySmallSite`, global sections use
   `hasLimitsOfShape_of_essentiallySmall`, and enough injectives use
   `Sheaf.isGrothendieckAbelian_of_essentiallySmall` (with the small-model
   structured-arrow limits supplied by Mathlib). The theorem's full site,
   morphism and presentation parameters are explicit in its source signature;
   `lean.statement` is copied verbatim. The consumer
   `CategoryTheory.RingedSitePicard.picard_h1_natural` was reread: its four
   independent universes and essentially-small assumptions are now supported.

Validation on 2026-10-24: `scompile.py` compiled the delivered module in both
sandbox and library modes successfully, with no errors or non-sorry warnings.
A separate module-mode `ConsumerUniverseProbe.lean`, compiled with the delivered
module through `scompile.py`, successfully elaborated `pullback_delta J K f A`
under (a) four independent site universes and `EssentiallySmall.{w}` and
(b) `C : Type (w + 1)`, `Category.{w} C`, `D : Type (w + 2)`,
`Category.{w + 1} D`, again essentially-small in `w`. Both sandbox and library
probe modes passed without warnings. This verifies the consumer universe shape
and the larger-object-universe case identified in H3. The probe is scratch only
and is not a delivered declaration. No new node or dependency module was needed.
All variables and universes are explicitly bound, and `autoImplicit` is false.
