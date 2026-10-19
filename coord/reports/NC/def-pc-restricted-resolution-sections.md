## Worker report

This delivery records the existing declaration
`AlgebraicGeometry.Scheme.Modules.RestrictedResolutionSections` from
`Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices`, lines 68–85. No new module,
definition, theorem, proof, or sorry is introduced. The existing structure is the
notion in this node, already bundled under def-weil-pbc-flat-base-change-open-choices.
Its docstring cites Stacks Tags 01E1 and 01E4. The local sources of both tags were
read: restriction preserves injectives and identifies sections, while higher direct
images are computed from section complexes.

Hypotheses and clauses, checked against the complete existing structure:

- A scheme X: `{X : Scheme.{uOpen}}`; no extra geometric hypothesis.
- An O_X-module F: `{F : X.Modules}`.
- An injective resolution I of F: `(I : InjectiveResolution F)`.
- An open U of X: `(U : X.Opens)`.
- A resolution of F restricted to U: field `resolution : InjectiveResolution
  ((restrictFunctor U.ι).obj F)`.
- An isomorphism to I restricted to U: `comparison`, whose target is
  `((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex`.
- Preservation of augmentation: `augmentation` asserts
  `resolution.ι.f 0 ≫ comparison.hom.f 0 = (restrictFunctor U.ι).map (I.ι.f 0)`.
- An isomorphism of its global-sections complex with the section complex of I on U:
  `sections` compares the complex mapped by
  `RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace ⋙ forget₂ _ AddCommGrpCat`
  with the complex mapped by `RingedSpace.openModuleSections X.toRingedSpace U`.
- The specified comparison components: `components` states, for every `n : ℕ`,
  `sections.hom.f n = Hom.app (comparison.hom.f n) ⊤ ≫
  (restrictAppIso U.ι (I.cocomplex.X n) ⊤).hom ≫
  (I.cocomplex.X n).presheaf.map (eqToHom U.ι_image_top.symm).op`.
  Thus these are fixed by the resolution comparison and canonical restriction
  identification, including transport of the image of the top open to U.

Dependency declarations read in full with their docstrings:

- def-pc-scheme: `AlgebraicGeometry.Scheme`,
  `Mathlib.AlgebraicGeometry.Scheme`; the locally affine locally ringed space.
- def-weil-sheaf-of-modules-category: `AlgebraicGeometry.Scheme.Modules`,
  `Mathlib.AlgebraicGeometry.Modules.Sheaf`; this is `SheafOfModules X.ringCatSheaf`.
- def-sp-injective-resolutions: `CategoryTheory.Injective`,
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic`, and
  `CategoryTheory.InjectiveResolution`,
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`; the latter bundles
  a nonnegative cochain complex of injectives with a quasi-isomorphic augmentation.
  All these are used by the recorded existing structure; no replacement is needed.

Edge cases: U may be empty or top, X may be empty, and F may be zero; the structure
imposes no nonemptiness, properness, affineness, or nonzero condition. The component
formula includes n = 0, and augmentation compatibility is explicitly in degree zero.
The scheme universe is the explicit arbitrary `uOpen`; the module and additive-section
universes agree with the dependency's `X.Modules` encoding. This is a data bundle,
not a claim of existence or a choice made from an unproved existence statement.

Searches performed using msearch.py for this item:

- LeanFinder: `restricted injective resolution on an open with section complex comparison`:
  eight generic injective-resolution, locally-injective, and unrelated section hits;
  none is this comparison-data bundle.
- Loogle: `RestrictedResolutionSections`: unknown identifier, zero hits.
- Mathlib grep: `RestrictedResolutionSections|restricted.*resolution`: zero hits.
- LeanSearch: `restricted resolution sections open subset`: service unavailable,
  Internal Server Error; no mathematical verdict inferred from the unavailable service.
- Source repository rg: `RestrictedResolutionSections|def-pc-restricted-resolution-sections`:
  zero hits. The requested node-id source search was also performed separately.
- Project lean/Sheaf rg: `RestrictedResolutionSections`: the defining structure in
  FlatBaseChangeOpenChoices.lean and numerous users; its entire definition and docstring
  were read and matched above. Therefore recording existing=true avoids a duplicate.
- Upstream-name index rg: `RestrictedResolutionSections`: zero hits.

No statement correction, missing notion, unusable dependency, or disputed statement
was found. The node changes only in its lean field. Server import/type inspection
and the delivery dry run provide the compilation and preflight verification.

## Second reading by NC

I independently read the node, the complete existing structure in
`Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices`, its dependency nodes and
Mathlib declarations, and cohomology.tex at Tags 01E1 and 01E4. This is a
bundle of comparison data, not an existence assertion. My object/hypothesis/clause
checklist is:

- Scheme X: `{X : Scheme.{uOpen}}`; pass. Mathlib's Scheme extends
  LocallyRingedSpace with local affine neighbourhoods. No separatedness,
  Noetherian, properness, or base-field assumption occurs here or in the source.
- O_X-module F: `{F : X.Modules}`; pass. I read `Scheme.Modules :=
  SheafOfModules.{u} X.ringCatSheaf`, its category and Abelian instances.
  This is precisely the scheme specialization of the dependency's general-site
  module-sheaf category, with linear morphisms, not the category of abelian sheaves.
- Injective resolution I of F: `(I : InjectiveResolution F)`; pass.
  Resolution.lean:43 bundles an N-indexed complex, degreewise injectivity,
  homology, an augmentation from single-zero F, and its quasi-isomorphism.
  Basic.lean:32 defines injectivity by extension along every monomorphism.
  No separate choice or extra injectivity hypothesis is imposed on F.
- Open U: `(U : X.Opens)` after I; pass, any open, with its canonical open
  immersion `U.ι`. No affine or quasi-compact restriction.
- Resolution of F restricted to U: `resolution : InjectiveResolution
  ((restrictFunctor U.ι).obj F)`; pass. I read Mathlib Modules/Sheaf.lean:348:
  this functor is actual restriction along the open immersion, with the
  induced structure-ring action, not the unrelated general pullback encoding.
- Augmented complex comparison: `comparison : resolution.cocomplex ≅
  ((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℕ)).obj
  I.cocomplex` and `augmentation : resolution.ι.f 0 ≫ comparison.hom.f 0 =
  (restrictFunctor U.ι).map (I.ι.f 0)`; pass. The direction agrees with the
  node, and equality at degree zero is exactly augmentation compatibility
  because single-zero has no other nonzero components.
- Isomorphism of global-section and open-section complexes: `sections` has
  source the global-sections image of `resolution.cocomplex` on U.toScheme,
  forgetting scalars, and target the `openModuleSections X.toRingedSpace U`
  image of `I.cocomplex`; pass. I opened both functors: the first evaluates
  at top, the second at U. Additive-group complexes express the specified
  section comparison; the component formula pins the actual maps.
- Specified components: `components : ∀ n : ℕ, sections.hom.f n =
  Hom.app (comparison.hom.f n) ⊤ ≫
  (restrictAppIso U.ι (I.cocomplex.X n) ⊤).hom ≫
  (I.cocomplex.X n).presheaf.map (eqToHom U.ι_image_top.symm).op`;
  pass. Mathlib's restrictAppIso identifies sections over top with sections
  over the image of top; the final transport identifies that image with U.
  Thus the isomorphism is induced by the stated comparison, not arbitrary.

Source check: Tag 01E1 assumes only a ringed space and an open subspace;
its proof restricts the injective resolution and identifies sections termwise.
Tag 01E4 computes higher direct images from precisely such section complexes.
The present scheme specialization and packaging as five data fields agree with
both the node and its named existing declaration. Neither source supplies a
hidden finiteness or characteristic hypothesis.

Edge cases: X and U can be empty, U can be top, and F can be zero. Every degree
is covered, including n = 0; no positive-degree or nonempty assumption is present.
There is no index family requiring nonemptiness. The arbitrary universe uOpen
is bound at module level; Scheme.Modules uses the dependency's same-universe
encoding, and the structure lies in Type (uOpen + 1). No variable is unbound.
No new definition, dependency module, theorem, or proof is delivered, so there
is no hollow data, new sorry, private replacement, or new docstring to repair.
The existing structure's source docstring refers to the original bundling node;
reuse preserves that declaration rather than introducing a duplicate for this node.

Independent searches, using different conceptual terms from the first reader:
LeanFinder via msearch, `injective complex restriction open subset global sections
comparison isomorphism`, returned eight Mathlib scheme-restriction/evaluation
lemmas, not this data bundle. Loogle `InjectiveResolution` returned unknown
identifier, so it supplies no positive match. LeanSearch `injective resolution
restriction to open global sections complexes` was unavailable (Internal Server
Error), with no mathematical verdict inferred. Direct rg for
`restricted.*[Rr]esolution|[Rr]esolution.*[Ss]ections|RestrictedResolutionSections|resolution.*restrict`
in WeilConjectures and the project, plus resolution/restriction searches in
Mathlib's Modules and Injective directories and the upstream-name index, found
no alternative upstream definition. The project contains the exact five-field
structure and its users, including the separate existence theorem in
RestrictedResolutionSectionsExist. The latter is not this definition.

No mismatch found; no Lean or node change was needed. In particular there is
no statement correction, new node, or dependency module to review. The node's
lean.statement is verbatim the existing structure signature before `where`.
The explicit scompile.py import/#check/#print probe passed on the server with
all five fields and only the four expected parameters (1.6 s, nice 19, two
threads, 60-second limit), without warnings. I retained the existing attachment
and added this independent reading only.
