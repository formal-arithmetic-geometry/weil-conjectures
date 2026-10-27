## Worker report

The module Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcPropertyAffineCriterion states
AlgebraicGeometry.AlgebraicSpace.fpqc_property_affine_criterion. Its only theorem has
proof `sorry`; no new definitions or independent proof obligations are introduced.
The statement is unchanged. The three already landed definition nodes for chartwise
flatness, schemes as algebraic spaces, and sheaf fibre products are added to
stmt_deps, as authorized by brief-stage2 §5. No dependency record is repaired.

Clause correspondence:

- The base scheme is `{S : Scheme.{u}}`. Objects are the existing `AlgebraicSpace S`,
  the full subcategory of fppf sheaves defined by def-trf-algebraic-space, and all
  arrows are its natural transformations. Explicit `universe u w` and
  `set_option autoImplicit false` implement the size convention.
- The property is `P : MorphismProperty (AlgebraicSpace S)`.
  `[P.RespectsIso]` expresses isomorphism invariance, using Mathlib's stability under
  precomposition and postcomposition by isomorphisms. These give invariance under
  arbitrary commuting isomorphisms of arrows.
- Hypothesis (1) is `hcoprod`: `J : Type u` and `[Finite J]`, families `Xj`, `Yj`,
  and arrows `fj`; the two `IsColimit (Cofan.mk ... )` conditions say exactly that
  `X.obj` and `Y.obj`, with their displayed coprojections, are the coproducts of
  the underlying sheaves. `a j ≫ q = fj j ≫ b j` characterizes the induced
  coproduct arrow. The implication `(∀ j, P (fj j)) → P q` is finite-union closure.
  This quantifies over every presentation of the sheaf coproduct, equivalently
  the canonical one because P respects isomorphisms; it assumes no global
  coproduct instance or extra existence hypothesis. `J` need not be nonempty.
  For `J` empty the two cofans are initial and `q` is the empty-to-empty arrow.
  Every finite set has a representative in Type u (a finite ordinal), and
  reindexing a cofan by an equivalence preserves its colimit, so no finite set
  is excluded by this index convention.
- Hypothesis (2) is `haffine`: for every X, Y and f, `P f` iff for every
  `Z : Over S`, `[IsAffine Z.left]`, and `g : schemeSpace Z ⟶ Y`,
  `P (enlargedFibreProductFst g f)`. The latter is literally the projection
  `Z ×_Y X → Z` of the sheaf pullback, isomorphic over Z to `X ×_Y Z → Z`.
- Hypothesis (3) is `hdesc`: the target and its cover are arbitrary objects
  `Z Z' : Over S`, each affine. The arrow `g : Z' ⟶ Z` has `Flat g.left`
  and `Surjective g.left`. For arbitrary algebraic-space X and f into
  `schemeSpace Z`, P of the canonical base change implies P of f. The scheme
  arrow is sent to the actual Yoneda natural transformation `yoneda.map g`.
- The conclusion quantifies over `{I : Type w}`, arbitrary X, Y, f, spaces Yi
  and arrows g. `hflat` says each g is flat on compatible etale scheme charts,
  exactly the item’s first covering condition, via `MapIsFlat`.
- `hrefine` is the second covering condition, with every affine scheme T over S
  and arbitrary `a : schemeSpace T ⟶ Y`. It gives `n : ℕ`, schemes Tj indexed
  by `Fin n`, arrows `q j : Tj j ⟶ T`, indices `k j : I`, and arrows
  `b j : schemeSpace (Tj j) ⟶ Yi (k j)`. The first two conjuncts assert affine
  Tj and flat qj. The third, `∀ t, ∃ j s, (q j).left s = t`, is joint
  surjectivity on scheme points. The fourth is the commuting triangle over Y.
  Fin n encodes exactly an arbitrary finite refinement, including n = 0.
  This is Stacks 03MQ, not merely a jointly-surjective family of flat maps.
- The resulting iff is `P f ↔ ∀ i, P (enlargedFibreProductFst (g i) f)`, the
  required equivalence for all members of the fpqc covering. Surjectivity for
  scheme refinements is on actual scheme points, as specified. No additional
  representability or finite-presentation condition is put on the cover arrows.
  General space point-surjectivity is the existing field-extension definition;
  the finite-refinement clause already forces it, so it is not imposed twice.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  Mathlib.AlgebraicGeometry.AffineScheme: `AlgebraicGeometry.IsAffine`.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicSpace`, `IsAlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, `IsSurjective`.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: `Flat` and its stalkwise equivalence
  `Flat.iff_flat_stalkMap`.
- Mathlib.AlgebraicGeometry.Sites.Fpqc: `Scheme.fpqcPrecoverage` (the scheme
  covering convention; the space covering condition is expanded in hrefine).
- Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity:
  `AlgebraicSpace.IsJointlySurjective`, whose definition was read in full.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers:
  `fibreProduct_isAlgebraicSpace`, including the sheaf pullback universal property.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties: `MapIsLocally`,
  `MapIsFlat`. Its already landed node def-sfb-space-morphism-properties is cited.
- Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite: `schemeSpace`,
  `schemeSheaf_isAlgebraicSpace`, `enlargedFibreProduct`,
  `enlargedFibreProductFst`. The owning definition node of `schemeSpace` and its
  algebraic-space property proof is def-trf-scheme-algebraic-space (Q87,
  2026-10-18, existing:true). The owning definition node of `enlargedFibreProduct`
  and its first projection is def-sfb-space-sheaf-fibre-product (NK, 2026-10-23,
  existing:true). Both records point to this same module. These constructions
  contain actual Yoneda/sheaf-pullback data; neither is an object constructed
  from the enlarged-site theorem's conclusion. The statement cites these two
  definition nodes rather than lem-trf-space-enlarged-etale-ringed-site-model.
- Proof-only imports supply all recorded proof dependencies: Mathlib's
  AlgebraicGeometry.Limits (`HasColimitsOfShape`, `sigmaOpenCover`,
  `disjoint_opensRange_sigmaι`, `sigmaSpec`, `ι_sigmaSpec`, finite `IsIso`),
  AlgebraicGeometry.OpenImmersion (`IsOpenImmersion`),
  Sheaf.AlgebraicGeometry.FppfSheafCoproductPartition
  (`Scheme.fppfSheaf_coproduct_partition`, read with its full signature), and
  Mathlib.CategoryTheory.Sites.LeftExact (`SheafOfTypes.finitary_extensive`).
  The statement's docstring gives all five DAG proof steps and their inputs.

Sources: read spaces-descent.tex, lemma-descending-properties-morphisms (041J),
including its proof, and spaces-topologies.tex, definition-fpqc-covering (03MQ).
The node intentionally strengthens the source's binary closure hypothesis to
finite closure including the empty union; that accepted node statement is kept.

Edge cases checked before writing: empty I, empty J, n = 0, empty test scheme,
singleton covers, disconnected affine refinements, arbitrary nonrepresentable
space morphisms, arbitrary base scheme and no finite-presentation assumptions.
For empty I all finite refinement indices force n = 0, and joint surjectivity
forces every affine test of Y empty; the initial cofan clause provides the
necessary P(empty → empty). The affine descent clause allows X to be a space,
not only a scheme. There are no unbound variables and no universe equalities
restricting the site; `w` is independent and used only for the covering family.

Searches for existing statements (2026-10-24):

- msearch.py leanfinder: "Property of algebraic space morphisms fpqc local on
  target affine testing finite disjoint union faithfully flat affine descent".
  Eight hits; `AffineTargetMorphismProperty.IsLocal`, `HasAffineProperty`, and
  `HasAffineProperty.descendsAlong_of_affineAnd` are scheme-only results.
- msearch.py leansearch: "Affine test criterion for fpqc descent of algebraic
  space morphism properties". Eight hits, all scheme affine-property results;
  no algebraic-space statement.
- msearch.py loogle: `CategoryTheory.MorphismProperty.RespectsIso,
  AlgebraicGeometry.AlgebraicSpace`. Zero hits; AlgebraicSpace is not a Mathlib
  identifier. RespectsIso was separately read in MorphismProperty/Basic.lean.
- msearch.py grep: `fpqc_local|fpqc.*criterion|AlgebraicSpace`, subdirectory
  AlgebraicGeometry. Reported zero hits. Direct rg of upstream/project Lean and
  dag/lean_names_upstream.json for `fpqc_property_affine_criterion`,
  `fpqc.*affine.*criterion`, and `AlgebraicSpace.*fpqc` found no exact statement.
  Project FpqcLocalOnBaseCriterion is a scheme theorem. AlgebraicSpaceFpqcSheaf
  is descent of sections, and FourPropertyFppfDescent addresses four fixed
  properties under fppf covers; neither is this generic fpqc criterion.
- Direct rg of the item id in lean/WeilConjectures found no declaration.
  Searches in lean/Sheaf for flatness/coproducts/coverings found the existing
  chartwise flatness and canonical pullback interfaces reused above.

No STATEMENT-DISPUTED issue, correction, missing definition, or unusable dependency
was found. No new definition node or dependency module is delivered.

Validation: prescribed scompile.py compiled the sandbox and final library module
against the live published server build, respectively 1.6 s and 1.5 s, with no
errors or unexpected warnings. Dry-run and delivery results are recorded below.

## Second reading by Q146

I reopened the node and the completed file for a separate clause-by-clause self
check; no additional agent was started, as required by the dispatch brief. The
maintainer provides the independent review. I checked the base, property,
isomorphism invariance, all three hypotheses, covering flatness, finite affine
refinement data, commuting triangles and both directions of the conclusion.
The cofan conditions are in sheaves, not presheaves; the pullback projections
land in the test/cover object; affine flat descent has an algebraic-space source;
and there is no Nonempty assumption. The only representable maps used are
Yoneda images of supplied scheme maps. No mismatch or change was found.

Dry run: deliver2.py --no-push returned `OK (dry run)` at 34e91914d6a;
server preflight and compilation passed, with nothing pushed at that step.


## Repair of returned head a5b0c1cdfdae

H2: replaced the added statement dependency
lem-trf-space-enlarged-etale-ringed-site-model with the already landed definition
nodes def-trf-scheme-algebraic-space and def-sfb-space-sheaf-fibre-product. Read
both complete node statements and lean records, then reopened schemeSpace,
schemeSheaf_isAlgebraicSpace, enlargedFibreProduct and enlargedFibreProductFst
in their owning module. The definitions have actual representable-sheaf and
sheaf-pullback data, with only their Prop-valued algebraicity supplied by the
existing theorem. Their ownership, rather than the enlarged-site theorem, now
appears in stmt_deps. The retained def-sfb-space-morphism-properties owns
MapIsFlat. No new node or dependency module is needed.

Compared the retained delivery node with current main: all fields outside lean
and stmt_deps agree. Rebuilt the node copy from current main with the repaired
stmt_deps and retained lean record. Verified the theorem signature against
lean.statement byte for byte; the Lean module and mathematical statement are
unchanged from the returned head. The original review accepted their mathematics.
Re-read the repaired dependency list and this report: both definition owners are
cited, and the obsolete theorem dependency and ownership explanation are removed.
Fresh prescribed compilation, dry run and delivery follow this repair.

Repair validation: scompile.py compiled the sandbox (1.6 s) and library module
(1.5 s) cleanly against the current live server build.
