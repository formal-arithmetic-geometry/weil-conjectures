## Worker report

The module `Sheaf.TraceFormula.TotalSiteFreeModuleResolution` states
`CategoryTheory.totalSiteFreeModuleResolution`, with its sole theorem proof `sorry`.
It includes the assumption package `TotalSiteConstantModuleDiagram` and the transparent
abbreviations `base` and `summands`. Their data are actual geometric morphisms, canonical
module inverse-image lifts, coherent comparisons, and the existing total-system presentation.
No new independent mathematical notion, dependency repair, or statement correction is needed.
The previous ATTACH concerned the reviewed stage-1 split, not an existing Lean declaration.

Hypothesis and clause correspondence:

- The sites C_p and D are `C`, `J`, `D`, `K`, with explicit universe `u` and small
  categories. This is the common ambient small universe in def-weil-size-convention;
  coefficient modules have object universe `u+1`, morphism universe `u`. `T : Type v`
  leaves the total category's object universe independent. Small sites and coefficients
  may be placed in this common bound; no equality between a smaller intrinsic site
  universe and the ambient coefficient bound is asserted.
- The commutative ring is `{Λ : Type u} [CommRing Λ]`; no nontriviality, finiteness,
  characteristic, boundedness, or invertibility hypothesis is imposed.
- `S.geometric f` is the geometric morphism for a simplex map (the arrow `f` is in
  the opposite simplex category). The existing `GeometricMorphism` supplies inverse
  and direct image, their adjunction, and finite-limit preservation.
- The canonical constant-coefficient module inverse image is `S.lift f.moduleFunctor`,
  using `ConstantLeftModuleInverseImageLift`, not an arbitrary exact functor.
  The constant ring sheaves and actual sheaves of modules are exactly `Modules (J i) Λ`.
  `HasWeakSheafify` instances provide the constant ring sheaves in the small universe.
- `geometricId`, `geometricComp`, `pullId`, `pullComp` give the specified identity
  and composition identifications. `id_normalized` and `comp_normalized` identify
  the module comparisons with the given geometric comparisons on underlying sheaves.
  `system.pull_id_left`, `pull_id_right`, `pull_assoc` are their two unit laws and
  cocycle identity. The faithful underlying functors carry these to the geometric laws.
- `S.system` is the existing `TotalSiteSystemData` for the ACTUAL categories of constant-ring
  module sheaves. Its compatible families and compatible morphisms have exactly the
  transitions of the node. Its fully faithful and essentially surjective presentation
  excludes extraneous objects and morphisms. `[Abelian T]` equips this presentation of
  total modules with its abelian structure; it does not posit unrelated component functors.
- `S.augmentation`, `augmentationLift`, `geometricAugment`, and `augment` encode a_p
  and the coherent identifications a_p u_alpha ≅ a_q. `augmentation_normalized` fixes
  their underlying geometric maps; `augment_id` and `augment_comp` are the two
  augmentation compatibility equations. Thus arbitrary module comparisons are excluded.
- The existential functor `a` is the total inverse image a^{-1}. Its component isomorphisms
  `ea` identify each component with `S.base G m = a_m^{-1}G`. The second conjunct gives
  its transition as `S.augment β`. The first conjunct makes this identification natural in G.
- `P : Modules K Λ ⥤ ChainComplex T ℕ` is the free resolution functor before adjoining
  its augmentation. `e G p m` identifies its degree-p, component-m term with
  `∐ S.summands G p m`; `summands` is the CONSTANT family with value `a_m^{-1}G`,
  indexed by ALL `SimplexCategory.mk p ⟶ m.unop`. This is the displayed direct sum.
- The third conjunct gives the map in G on every labelled summand. The fourth gives
  the transition along β: pull back the α inclusion, apply the total transition, then
  use e; the result is `S.augment β` followed by inclusion at `α ≫ β.unop`.
  Lean's composition order is left-to-right, so this label is β∘α in the node.
- `d G p i` is the node's face d_i from degree p+1 to p. Its component formula sends
  α to `SimplexCategory.δ i ≫ α`, namely α∘δ_i, by the identity on a_m^{-1}G.
  The next conjunct identifies the chain differential with the complete alternating sum
  over `Fin (p+2)` with coefficients `(-1 : ℤ) ^ (i : ℕ)`.
- `ε G` is a morphism IN T; its naturality equation is explicit. Its component formula
  is the identity on EVERY degree-zero summand, hence precisely the fold map.
  The faces and fold are total-module morphisms because they are arrows of T, whose
  morphisms are identified with compatible component families by `system.map_bijective`.
- The chain-complex structure includes d²=0. The augmentation composite is explicitly
  zero. `Epi (ε G)` states exactness at a^{-1}G followed by zero; `(P.obj G).ExactAt
  (n+1)` states exactness in all positive degrees; `ShortComplex.mk ... .Exact` states
  exactness at P_0. Together these cover every spot of the augmented complex.
- `Φ p G I` is an `Equiv` between the precise two Hom types in the node. Its forward
  formula is inclusion of the IDENTITY label at component p followed by the component
  of the morphism, using e to identify the chosen coproduct. Its inverse formula on
  the α summand is `augment.inv ≫ lift.map f ≫ system.transition I`, exactly the stated
  pullback-and-transition formula, with the specified a_m^{-1}G comparison.
- The next two equations state naturality of Φ under postcomposition in I and
  precomposition in G. The final equation says that ε corresponds to ea.inv, which
  is the identity of a_0^{-1}G under the component identification ea.

Dependency declarations read and used:

- `def-weil-size-convention`: metatheoretic convention, no declaration or module.
- `def-weil-pbc-simplicial-object`: `Mathlib.AlgebraicTopology.SimplicialObject.Basic`,
  `CategoryTheory.SimplicialObject`, `SimplexCategory`, and `SimplexCategory.δ`.
- `def-trf-geometric-morphism`: `Sheaf.CategoryTheory.Sites.GeometricMorphism`,
  `CategoryTheory.GeometricMorphism` and its inverse/direct/adj/leftExact fields.
- `def-weil-pbc-constant-sheaf`: `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  `CategoryTheory.constantSheaf`, used by the imported Modules abbreviation.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`, the existing abbreviation for `SheafOfModules`.
- `lem-pe-constant-left-module-inverse-image`:
  `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`,
  `CategoryTheory.ConstantLeftModuleInverseImageLift`,
  `CategoryTheory.ConstantLeftModuleInverseImage.Modules` and `.W`.
- `lem-trf-total-site-component-restriction`:
  `Sheaf.TraceFormula.TotalSiteComponentRestriction`,
  `CategoryTheory.TotalSiteSystemData`, `TotalSiteCompatibleSystem`,
  `TotalSiteCompatibleMorphism`, and `totalSiteComponentRestriction`.

The last two already landed nodes are added to stmt_deps because their recorded interfaces
appear in the statement; they were already proof dependencies. The remaining proof node
`lem-trf-total-site-simplex-free-resolution` has no recorded module on the base, so there
is no import to add for it. Its proof is cited in the postponed theorem's docstring;
no object from it is required to TYPE this statement. No other module is modified.

Edge cases read against the formulas: p=0 uses the identity-labelled vertex and its fold;
the differential P_1→P_0 has two signs +1 and -1; component m=0 has precisely one simplex
map for every p and gives the usual alternating identity/zero complex; arbitrary p and m
use all monotone maps, including degeneracies; zero G, the zero ring, empty component sites
and the empty base site are allowed. No connectedness, point, nonempty-site hypothesis,
strictification, or finite-degree truncation is present. Hom sets retain zero objects and
zero morphisms. Coherent pullbacks are kept as isomorphisms rather than forced to equalities.

Searches for existing declarations (no exact match):

- msearch leanfinder: "Exact augmented free module resolution on a total simplicial site
  with summands indexed by simplex maps and identity summand Hom adjunction". Eight hits:
  DoldKan summands/N/Γ₀ splitting, classifyingSpaceUniversalCover.toModule and its extra
  degeneracy, and singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace.
  None constructs this coherent total-site resolution or its identity-summand equivalence.
- msearch loogle: "CategoryTheory.SimplicialObject,
  CategoryTheory.AlternatingFaceMapComplex.obj, HomologicalComplex.ExactAt". Zero hits;
  the second name was unknown (the actual alternating-face namespace was subsequently
  read in Mathlib). The final statement uses an explicit ChainComplex and face sum.
- msearch grep: "TotalSite|totalSite|simplicial.*resolution" in CategoryTheory: zero hits.
- msearch leansearch: "Exact augmented direct sum module resolution of the total
  simplicial site and its identity summand restriction bijection". Eight hits:
  SimplicialObject.Augmented, ordinary module presentation direct sums, DirectSum component
  lemmas, and DoldKan.PInfty_add_QInfty; none is this statement.
- rg in upstream WeilConjectures for TotalSite/totalSite/freeModuleResolution and the
  exact node id: no match. rg for the proposed declaration and package names in upstream,
  dag/lean_names_upstream.json and lean/Sheaf: no match.
- rg in lean/Sheaf for total-module/free-resolution terminology found and led to reuse of
  TotalSiteComponentRestriction, ConstantLeftModuleInverseImage, and RingedSiteModules.
  The other results concern hypercover, Cech, bar, or telescope resolutions, not this node.

Source checked directly: `literature/stacks-project/spaces-simplicial.tex`,
`lemma-restriction-module-to-components-site` (0D72),
`lemma-simplicial-resolution-augmentation-modules` (0D7C), and
`lemma-simplicial-resolution-augmentation` for the face maps and signs.
No STATEMENT-DISPUTED issue or source correction was found.

Validation: scompile.py compiled the final module in both sandbox and library paths
cleanly (6.2 s and 9.1 s), with no errors or warnings. Every variable and universe is
explicit, autoImplicit is false, all lines have at most 100 characters, and the only
postponed theorem has the complete source-based proof in its docstring.

## Second reading by NL

The worker reread the node, the Stacks source and the final file clause by clause using
the correspondence above. This is a worker self-check; no independent reader is claimed.
The dispatcher's brief explicitly prohibits starting other agents and assigns independent
review to the maintainer after delivery.

The rereading replaced an initial simplicial-object output with the node's explicit
chain complex and faces, and made naturality of the Hom equivalence explicit in BOTH
variables. It checked the direction of pullComp, augment, the opposite simplex arrows,
all summand relabellings, the two signs in degree one, the augmentation exactness endpoint,
and the ea.inv normalization. It also checked that the system presentation is fully
faithful and essentially surjective and that the module comparisons are normalized by
the original set-sheaf comparisons. No discrepancy remains in this self-check.
