## Worker report

The module `Sheaf.CategoryTheory.SmallSiteImageSubsheafRepresentatives` states
`SheafOfModules.smallSite_image_subsheaf_representatives`, with its entire proof
postponed by `sorry`. The companion definition module supplies actual powerset
codes and their actual subset sheaves, using Mathlib's presheaf submodules.
No mathematical statement correction or dependency repair was necessary.
The retained sandbox initially contained only dispatcher brief markers, no previous
Lean file or node packet. The live node has a stage-1 split review by Q04; that is
the appropriate prerequisite for this stage-2 statement, rather than a completed
stage-2 declaration.

The node's hypotheses and clauses are rendered as follows.

- The chosen universe is the explicit level `u`. A small site has `C : Type u`
  and `[Category.{u} C]`. Its coverings are `T : Precoverage C` with
  `_hT : T.IsSiteForCoverings`; sheaves use `T.toGrothendieck`. This is the
  dependency's recorded site interface, with covering pullbacks only. It does
  not assume global pullbacks or exclude an empty site.
- The sheaf of possibly noncommutative rings is
  `R : Sheaf T.toGrothendieck RingCat.{u}`. Sectionwise modules are precisely
  `ringedSiteModules.{u} R`. The index set is `I : Type u` and the family is
  `P : I → ringedSiteModules.{u} R`. Ring, module, index, object and morphism
  universes are all within the chosen small universe, as the node assumes.
- The product `D_j` is `SectionSubsetFamily (P j)`, definitionally
  `∀ X : Cᵒᵖ, Set ((P j).val.obj X)`. Opposite objects index exactly the
  original object set. No chosen skeleton or abstract subobject quotient is used.
- The subset `E_j` is `ModuleSubsheafCode (P j)`, definitionally a subtype of
  that product. `IsModuleSubsheafCode` requires a `PresheafOfModules.Submodule`
  with exactly the code's carriers and the sheaf axiom for its inherited presheaf.
  Mathlib's existing submodule fields give the sectionwise submodules and
  restriction stability, including semilinearity over the restricted ring maps.
- For each code, `s.submodule` recovers that carrier-determined submodule,
  `s.toSheaf` uses its actual subset modules and restricted maps, and `s.ι` is
  its subset inclusion. There is no arbitrary isomorphic replacement.
  The first quantified conclusion identifies every carrier with `s.val X`.
  Its `∃! N` clause states uniqueness of the inherited submodule presheaf with
  those carriers and the sheaf axiom; the sheaf proof itself is proof irrelevant.
  `Mono s.ι` states that the inclusion is a monomorphism.
- For every target `j`, arbitrary source `M` and arrow `m : M ⟶ P j`,
  `Mono m →` is exactly the monomorphism hypothesis. The next conclusion
  `∀ X, Function.Injective (m.val.app X)` is the sectionwise injectivity.
- The resulting `∃ s : ModuleSubsheafCode (P j)` and
  `∀ X, s.val X = Set.range (m.val.app X)` assert that the actual image family
  belongs to `E_j`. The definition of a code includes its sheaf condition.
- The conclusion `∃ e : M ≅ s.toSheaf, e.hom ≫ s.ι = m` supplies the
  module-sheaf isomorphism and the specified factorization. The following
  sectionwise equation fixes `e` as the induced image map on every element;
  hence this is the node's induced bijection, not an arbitrary isomorphism.
- The final quantified equivalence is for two monomorphisms into the SAME `P j`.
  Its left side is `∃ e : M ≅ M', e.hom ≫ m' = m`; its right side is equality
  of the sectionwise ranges for every `X`. This is exactly isomorphism over the
  specified target if and only if the image families agree.
- Conversely every code is realized by its own inclusion: the code conclusions
  include both `Mono s.ι` and `∀ X, Set.range (s.ι.val.app X) = s.val X`.
- The first two conjuncts are `Small.{u}` for every `D_j`, every `E_j`, and
  `Σ j : I, ModuleSubsheafCode (P j)`. The definitions already place these
  types in `Type u`; the explicit conclusions record the node's size claims.
  This dependent sum, together with `s.toSheaf`, `s.ι` and the range
  factorization clause, indexes actual representatives for all the subobjects.
- Only `Mono m →` arrows get image-sheaf conclusions. There is no assertion
  that the sectionwise image of a general sheaf arrow satisfies the sheaf axiom.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`: read its full docstring and
  definition, including the bind composition and existence of covering pullbacks.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  read its full docstring and abbreviation to `SheafOfModules.{v} R`.
  Both modules are imported publicly and their recorded interfaces are used.
- `def-weil-size-convention` is explicitly recorded as a metatheoretic convention
  with no declaration to import. Explicit universe levels and `Small.{u}` render it.
- New definition node `def-sfb-small-site-module-subsheaf-codes` supplies the six
  public definitions listed in its `lean.declarations`; it is added to `stmt_deps`.
- Mathlib's `PresheafOfModules.Submodule`, `.toPresheafOfModules`, and `.ι`:
  read the full `Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule` source.
  `SheafOfModules`, its `Hom`, and sectionwise morphism components are Mathlib's.
  Read the source's sectionwise-kernel construction immediately before
  `sites-modules.tex` lemma-abelian (Tag 03DA), and the blueprint's paragraph (2).

Edge cases checked before writing: an empty target index set is permitted and
gives an empty dependent sum; an empty category has one empty subset family and
one valid code per target; an empty covering is retained by the sheaf axiom.
For a zero target the unique submodule is zero. A one-object site reduces to
the usual submodules of a module when its topology is trivial. There is no
commutativity, nonzero-ring, nonempty-site or nonempty-index assumption.
The source and all targets have the same section universe, exactly as required.
No statement is disputed.

Searches made (the new node also records its definition searches):

- `msearch.py leanfinder`, query "Subobjects of sheaves of modules on a small
  ringed site are represented by sectionwise submodule subsets, with
  monomorphisms factoring isomorphically through their actual ranges": eight
  results, including `PresheafOfModules.wellPowered`, the sheaf generating-section
  interfaces, and `PresheafOfModules.mono_iff_surjective`. None states the actual
  subset-code classification. Abstract well-poweredness alone omits its data.
- `msearch.py loogle`, query `SheafOfModules, Submodule`: two results,
  `SheafOfModules.Submodule.mk` and `.isSheaf`, referring to
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule`. This module is absent in
  the pinned local source AND `scompile.py --source` returned
  `Module source unavailable: Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule`.
  The search service indexes a newer library; no missing available declaration
  is copied. The pinned presheaf-submodule construction is reused instead.
- `msearch.py leansearch`, query "Families of sectionwise submodules of a module
  sheaf stable under restrictions and satisfying the sheaf axiom, encoded as a
  subset of the product of powersets": eight hits, including `SheafOfModules.mk`,
  sections, and sheaf-condition interfaces; none supplies these powerset codes.
- `msearch.py grep`, query `submodule|subsheaf|wellPowered|range` scoped to
  `Algebra/Category/ModuleCat/Sheaf`: two generator/quasicoherent index-range hits.
- `msearch.py grep`, query `structure Submodule|toPresheafOfModules|def.*ι` scoped
  to `Algebra/Category/ModuleCat/Presheaf/Submodule.lean`: five displayed hits;
  read the module and reused the submodule, subset presheaf, and inclusion.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, for image-subsheaf names,
  subsheaf-code names and sectionwise image/representative text, found specialized
  support, fixed-section and geometric image constructions, not this statement.
  The exact item id has no occurrence in `lean/WeilConjectures`.
- `rg -l -i` in `dag/nodes`, `lean/Sheaf`, and `lean/WeilConjectures`, query
  `subshea(f|ves).{0,45}(cod|subset famil)|cod.{0,30}subshea`: specialized algebra
  subobjects and consumers of smallness, not a definition of these codes.
  No chapter definition node matched `actual.*subsheaf|subset.*code|powerset`.
  `tools/blueprint_refs.py search small-site-module-subsheaf-codes` gave zero hits.
  `tools/blueprint_refs.py ancestor` gives `det-lem-int-integral-heart-triangulated`.

The two delivered modules compiled through `scompile.py`, separately and in
dependency order, with no errors or unexpected warnings. No global build was run.
There is one postponed theorem and no postponed data or auxiliary proof.
The `choose` in code realization eliminates the code's actual existential
membership proof; its submodule is determined uniquely by its fixed carriers.
It never invokes an existence theorem with a postponed proof.

## New nodes

`def-sfb-small-site-module-subsheaf-codes` defines `D(P)`, the subset `E(P)`
of sheaf codes, their carrier-determined presheaf submodule, the actual subset
sheaf and its inclusion. Source: the integral-heart triangulated blueprint proof,
paragraph (2), final sentence, as expanded by the item's actual-image coding
argument. It cites the same size, site and sectionwise-module definitions as the
item. Mathlib's existing restriction-stable submodule is used directly, so this
node supplies only the missing powerset-code/sheaf wrapper and its realization.
The semantic, type-name, Mathlib text, project text and DAG searches above found
no existing definition node or pinned-library declaration for this notion.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and
the maintainer's independent review is the review of this delivery.
