## Worker report

The module `Sheaf.CategoryTheory.CoproductExtResolutionCohomology` states all clauses
of `lem-trf-coproduct-ext-resolution-cohomology`, as six named theorems with `sorry`.
Two transparent abbreviations specialize existing Mathlib functors; neither chooses
data from a postponed existence theorem. No node statement or dependency list changes.

Hypotheses and clauses, in order:

- The small site in the chosen universe is `{C : Type u} [SmallCategory C]`
  with `J : GrothendieckTopology C`. This is the usual topology encoding of the
  site's sheaf category. The existing `SiteCoveringAxioms` module is publicly imported;
  no new site convention is defined. The size-convention node is metatheoretic:
  site, ring values, module values and coproduct indices use `u`; the family-label
  type `I : Type w` is unrestricted. No extra size equality is imposed on a site
  whose universes were specified differently: the item itself assumes a small site
  in the chosen module universe.
- `R : Sheaf J CommRingCat.{u}` supplies the commutative ring sheaf. Its underlying
  ring sheaf is `(sheafCompose J (forget₂ CommRingCat RingCat)).obj R`. Both `F`
  and every `E i` use the recorded `ringedSiteModules.{u}` abbreviation.
- `coproduct_ext_nonempty_injectiveResolution` states existence of
  `InjectiveResolution F`. This bundles the nonnegative injective complex,
  exact augmentation and quasi-isomorphism. Mathlib's `P.cochainComplex` extends
  its `P.cocomplex` by zero in negative degrees; nothing is postulated about an
  arbitrary unconstructed complex.
- `injectiveResolutionHomComplex P M` is literally the additive Hom functor
  `preadditiveCoyoneda.obj (op M)` applied degreewise to `P.cochainComplex`.
  Thus its q-th term is Hom(M,J^q), its differential is h ↦ h ≫ d_J,
  and it is zero in negative degrees. `injectiveResolutionHomPrecomp P f`
  is the degreewise additive coyoneda map and sends h to f ≫ h.
- For arbitrary module sheaf `M`, `coproduct_ext_resolution_independent P Q M q`
  gives the canonical additive isomorphism on H^q for any two resolutions. Its
  equation identifies the isomorphism with the cohomology map of *every*
  comparison morphism over `𝟙 F`, preventing arbitrary choices of unrelated
  group isomorphisms. The node defines Ext by this Hom cohomology; this
  statement supplies its independence, rather than defining a second Ext.
  The existing Mathlib resolution-to-Ext comparison is imported for its proof.
- For arbitrary `A : Type u` and `i : A → I`, and any specified model
  `e : M ≅ ∐ (fun a ↦ E (i a))`, `coproduct_ext_resolution_complex_iso`
  gives an actual isomorphism of the integer-indexed Hom complexes to their
  categorical product. Its projection equation is precomposition by
  `Sigma.ι _ a ≫ e.inv`. In particular the literal coproduct is obtained by
  taking `M := ∐ ...` and `e := Iso.refl _`. The item explicitly asserts this
  isomorphism of complexes, so it is retained as an actual complex isomorphism,
  which also induces the corresponding derived-category isomorphism.
- `coproduct_ext_resolution_cohomology` gives the abelian-group isomorphisms
  for every `q : ℕ`. Its projection equation is exactly `homologyMap` of
  the same precomposition chain map. Thus the displayed maps are induced by
  restriction, rather than merely unspecified isomorphisms of the groups.
- `coproduct_ext_resolution_degree_zero` gives a family `η` of isomorphisms
  Hom(M,F) ≅ H^0 for every coproduct and every specified model. Its first
  equation identifies η(h) with the class of any cycle whose inclusion is
  `h ≫ P.ι.f 0 ≫ (P.cochainComplexXIso 0 0 rfl).inv`. The last factor is the
  canonical identification with the zero-extended resolution. Such a cycle
  exists because the augmented composite is killed by d, and its lift is
  unique because the cycles inclusion is monic. Hence this equation specifies
  precisely the map h ↦ [ι ∘ h]. The second equation is naturality for an
  arbitrary `f : N ⟶ M`, without any assumption that f preserves summands.
  Taking f to be the chosen isomorphism, its inverse, or an identity between
  different presentations covers all the specified-model compatibilities.
- `coproduct_ext_resolution_vanishing` assumes `IsZero` of the positive
  Hom cohomology of every `E j`, for every `q > 0`, and concludes the same
  for each coproduct model `M`. By the resolution-independence clause these
  hypotheses are exactly the Ext vanishing in the node.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`, and its documented retention
  of Mathlib `GrothendieckTopology` and `Sheaf` for sheaf categories.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, transparently `SheafOfModules` with its
  existing category and abelian structures.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`:
  `CategoryTheory.Injective`; `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`:
  `CategoryTheory.InjectiveResolution`, its `cocomplex`, `ι` and `Hom`.
- `Mathlib.CategoryTheory.Abelian.Injective.Extend`:
  `InjectiveResolution.cochainComplex`, `cochainComplexXIso`, and `Hom.hom'`.
- `Mathlib.Algebra.Homology.HomologicalComplex`:
  `CochainComplex`; `Mathlib.CategoryTheory.Preadditive.Yoneda.Basic`:
  `preadditiveCoyoneda`; `Mathlib.Algebra.Homology.Additive`:
  `Functor.mapHomologicalComplex` and `NatTrans.mapHomologicalComplex`.
- `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`:
  `homology`, `homologyMap`, `cycles`, `iCycles`, `homologyπ`; categorical
  products and coproducts use the existing `Pi.π` and `Sigma.ι`.
- Proof imports: `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`,
  `SheafOfModules.isGrothendieckAbelianOfUniverses`;
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`,
  `IsGrothendieckAbelian.enoughInjectives`;
  `Mathlib.CategoryTheory.Abelian.RightDerived`, `InjectiveResolution.toRightDerivedZero'`
  and `instIsIsoToRightDerivedZero'`, with `InjectiveResolution.of` imported there;
  `Mathlib.CategoryTheory.Abelian.Injective.Ext`,
  `InjectiveResolution.extAddEquivCohomologyClass`;
  `Mathlib.Algebra.Category.Grp.AB`, `instAB4StarAddCommGrpCat`.

Edge cases checked before writing: `A = Empty` gives the initial module and
terminal/zero abelian-group product, including degree zero. No `Nonempty`,
`Fintype`, injectivity or distinctness assumption is put on `A` or `i`.
Repeated labels and infinite sums are therefore included. With `F = 0` the
resolution cohomology and degree-zero Hom are zero. Degree zero is covered by
all comparisons and deliberately excluded only from the positive vanishing
hypothesis/conclusion. Negative degrees are genuinely the zero extension;
no lower-bound assumption on arbitrary unrelated complexes is substituted.
For two coproduct presentations the naturality equation applies to every map,
including maps mixing several summands and identities between presentations.

Sources opened: `literature/stacks-project/sites-cohomology.tex`,
`example-hom-complex-into-sheaf` (07AA) and
`lemma-existence-derived-lower-shriek` (07AC), and the full recorded
Mathlib/dependency declaration signatures and docstrings above.

Searches for an existing statement (all through the prescribed read-only tools):

- `msearch.py leanfinder`, "Cohomology of Hom from a coproduct into an injective
  resolution is the product of Ext groups": eight hits, notably
  `InjectiveResolution.extEquivCohomologyClass`,
  `extAddEquivCohomologyClass`, and `Ext.addEquivBiproduct`. The first two
  compare one resolution with Ext; the last is finite and has the other
  variance. None states this arbitrary-small-coproduct result with the maps.
- `msearch.py loogle`, `CategoryTheory.Abelian.Ext.biproductAddEquiv`: one hit;
  its full signature requires `[Fintype J]`. Its source was opened at
  `Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean:475`, so it cannot
  replace the arbitrary-small-index statement.
- `msearch.py grep`, `homology.*[Pp]roduct|Ext.*coproduct`, scoped to
  `Algebra/Homology`: zero hits. A broader earlier search for coyoneda
  complexes and product cohomology likewise gave no exact result.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the proposed declarations and coproduct/Hom/cohomology expressions:
  no existing declarations with these names or this statement. The nearby
  `AcyclicCoproductExtOrthogonalHom` module proves the consuming acyclicity
  assertion, and uses the same Hom functor; it does not state this lemma.
  `grep -rn` for the exact item id in `lean/WeilConjectures` gave no matches.

Compilation: `scompile.py Q07 lem-trf-coproduct-ext-resolution-cohomology <module>`
passed both its sandbox compile (8.9 seconds) and named-library compile
(8.4 seconds), with no errors or warnings. All variables/universes are explicitly
bound, with `autoImplicit false`. Each theorem proof is `sorry`; neither helper
contains `sorry`. There is no statement dispute, correction, new node or dependency repair.

## Second reading by Q07

Final worker re-reading with the node and completed Lean file open; the dispatcher
expressly forbids starting another agent, and the maintainer performs the independent
review after delivery. This section records the worker's own second pass, not an
independent review by a fictitious second person.

The site/ring/module binders match the node. Existence uses the exact bundled
resolution, and the Hom complex uses its integer zero extension. Independence is
for any M and any two resolutions and is pinned to all comparison maps. The two
coproduct comparisons use the same inclusions composed with e.inv, including the
identity model. Their product projections therefore express the requested restriction
maps in every degree. The degree-zero formula uses the actual augmentation and
explicit cycles/homology projection, while its naturality quantifies over arbitrary
maps between two independently indexed coproduct models. Positive vanishing is
restricted by `0 < q`, and no finite or nonempty index assumptions appear. Both
helpers are transparent applications of the existing functors, with real data.

During compilation, the product notation was corrected to Mathlib's `∏ᶜ`, and the
codomain of the η family was parenthesized to make the intended abelian-group
isomorphism explicit. Neither repair changes the mathematical statement. On the
final pass no hypothesis, clause or edge case was found missing. All eight public
declarations carry this node's blueprint tag and source; the six postponed theorems
have the relevant natural-language proof steps in their docstrings.
