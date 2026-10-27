## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceAtlasSheafDescent` states Tag 05YY as
`AlgebraicGeometry.AlgebraicSpace.atlasSheafRestriction_isEquivalence`, with its
proof postponed. Its named constructions implement the restriction functor,
including canonical overlap comparisons, on the actual small étale sheaf categories.
The accepted stage-1 split and natural-language statement are unchanged. The earlier
worker's BLOCKED was a stage-1 split refusal; the current brief §0 explicitly permits
stage 2 after that passing split. The current queue assigns this item to stage 2,
and its live node has no Lean record.

Hypotheses and clauses, individually:

* Base scheme B: `{S : Scheme.{u}}`. Space H over B: `H : AlgebraicSpace S`.
  This is the existing full subcategory of fppf sheaves with representable diagonal
  and a surjective étale scheme atlas, not a substitute notion of algebraic space.
* Universes and small representatives: explicit `u w`; sheaf values are
  `Type (max (u + 1) w)`, the coefficient universe of the recorded enlarged-site
  comparison. The existing sites retain their object and morphism universes;
  no universe equality or finiteness is imposed. The singleton is `Unit`.
* Scheme W and representable étale p: `W : H.EtaleSite` contains precisely an
  `Over S` scheme `W.obj.left`, its Yoneda map `W.obj.hom` to H, and
  `W.property : IsEtale W.obj.hom`. `IsEtale` already includes representability.
  The remaining hypothesis `hs : IsSurjective W.obj.hom` is exactly surjectivity
  of its scheme tests. No quasi-compactness, separatedness, Noetherianity or atlas
  finiteness is assumed anywhere in the signature or helper construction.
* Small étale sheaves: global objects are literally
  `Sheaf H.etaleTopology (Type (max (u + 1) w))`. The unique local object in
  `AtlasSheafDescent H W` is literally a sheaf on
  `(schemeSpace W.obj.left).etaleTopology`, the small scheme-object étale site
  of the representing scheme W. No enlarged-site sheaf is substituted for G.
* Double and triple overlaps R,T and their projections: Mathlib's intrinsic
  `Pseudofunctor.DescentData` specifies the transition on every common test object
  over H, and its pullback naturality. Evaluating its `iso` on R with p1,p2 gives
  the displayed alpha. R is the existing `enlargedFibreProduct p p`; the recorded
  fibre-product dependency says it is represented by a scheme. The iterated fibre
  product similarly gives T. Conversely alpha determines each common-test transition
  by its universal map to R; the naturality condition states exactly that pullback.
  Thus quantifying over common test objects does not introduce independent data.
* Cocycle: `DescentData.hom_comp` on T says p12(alpha) followed by p23(alpha)
  equals p13(alpha), in Lean's left-to-right composition order. `pullHom_hom`
  uses the identity-on-sections composition comparisons of
  `atlasSmallSheafPseudofunctor`. The `hom_self` field is redundant normalization:
  pull the invertible cocycle to the triple diagonal and cancel alpha. Conversely
  `DescentData.iso` obtains invertibility using `hom_self` and `hom_comp`. This
  is the same category of cocycle pairs, without requiring a diagonal hypothesis.
* Morphisms of pairs: Mathlib `DescentData.Hom` is a sheaf map of the sole local
  object with `comm`, exactly the square commuting with alpha. There is no
  restriction on the morphism's injectivity, surjectivity, or invertibility.
* Restriction F maps to p inverse image F: `atlasSheafRestriction` is
  `toDescentData` for the singleton `atlasToBase H W`. Its sole object is
  `atlasSmallRestriction`, the existing `chartwiseEtaleMap` followed by Mathlib's
  `sheafPushforwardContinuous`; the presheaf is literal precomposition, hence the
  inverse image of 03LP. `atlasBaseObject H` has underlying space H, so its fibre
  is definitionally the stated global sheaf category.
* Canonical alpha_F: `DescentData.ofObj` identifies the restrictions along the
  two atlas legs with their common composite to H by the pseudofunctor's
  composition constraints. Those constraints are identities on section presheaves,
  exactly the canonical identification in the first proof of 05YY. Morphisms are
  the same inverse images of the original sheaf maps.
* Equivalence: `(atlasSheafRestriction H W).IsEquivalence` asserts equivalence of
  exactly that functor. Essential surjectivity says every pair is effective, with
  its specified overlap isomorphism. Fullness and faithfulness say compatible maps
  glue uniquely. An equivalence reflects isomorphisms; alternatively glue the local
  inverse and use faithfulness on the composites. This renders all three final
  consequences without an additional choice of equivalence or any extra assumption.

Dependency declarations read and used:

* `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`,
  `IsSurjective`, `EtaleSite`, `etaleTopology`, and their docstrings/signatures.
* `def-weil-size-convention`: its Lean record is a metatheoretic convention;
  there is no declaration to import. The explicit universe levels implement it.
* `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`
  and its public Mathlib sheaf imports. Reached through the recorded space model.
* `Sheaf.AlgebraicGeometry.SmallEnlargedEtaleModules` and its public import
  `EnlargedEtaleRingedSite`: `IsChartwiseEtale`, `EnlargedEtaleSite`, `schemeSpace`,
  `enlargedSchemeInclusion`, `enlargedEtaleObject`, `chartwiseEtaleMap`,
  `enlargedLocalization_equivalence`, `enlargedPostcompose_continuous`,
  `enlargedPostcomposeSchemeIso`, `enlargedEtale_localization`, and
  `enlargedSetEquivalence`. These give the exact small/enlarged site objects and
  localization interpretation. The existing module/ring comparisons remain public.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme`; imported through the model, used in the proof plan
  and in identifying the intrinsic double/triple tests with the statement's schemes.
* `Sheaf.CategoryTheory.SetSheafCoverDescent`: `setSheafCoverDescent`, plain
  proof import, and its actual `Pseudofunctor.DescentData` interface.
* `lem-trf-space-enlarged-site-scheme-density` has no recorded Lean declaration
  on this base and so has no proof import. The accepted proof plan still names it;
  nothing about the statement construction waits on this unformalized proof input.

Edge cases checked before drafting: H empty and W empty are allowed, and the small
étale sheaf category then gives the terminal descent situation; the singleton index
is still present and imposes no nonempty-scheme condition. For the identity atlas,
the diagonal cocycle cancels to identity and restriction is the identity equivalence.
For Spec(k') over Spec(k) finite Galois, R is the full kernel pair, not W: equal cover
indices are allowed with different legs in `DescentData`, retaining the nontrivial
Galois transitions. Infinite disjoint scheme atlases are allowed; no compactness,
finite cover, or finite products indexed by the atlas are imposed. The empty sheaf
on a nonempty scheme, empty section sets on tests, and arbitrary sheaf maps require
no choices of elements. Identity and arbitrary enlarged test arrows are retained.

Searches made (the recorded declarations and docstrings were opened, not inferred
from their names):

* msearch leanfinder: “Sheaves of sets on an algebraic space are equivalent to
  sheaves on an etale scheme atlas with an isomorphism satisfying a cocycle on
  the triple overlap”: eight sheafed-space/topological gluing results, no match.
* msearch loogle: `"Sheaf", "Descent"`: one hit,
  `Pseudofunctor.DescentData.subtypeCompatibleHomEquiv_toCompatible_presheafHomObjHomEquiv`;
  this is a morphism identity, not the algebraic-space theorem.
* msearch grep on CategoryTheory/Sites:
  `AlgebraicSpace|sheaf.*[Dd]escent|[Dd]escent.*sheaf`: three hits in Subsheaf
  and DescentData; no algebraic-space theorem.
* msearch leansearch: “Small etale sheaves on algebraic spaces form a pseudofunctor
  under etale restriction with canonical composition isomorphisms”: eight hits,
  including `GrothendieckTopology.pseudofunctorOver` (slices of a single site),
  scheme module restriction and small étale topology; no small-space-site functor.
* rg through project Sheaf and WeilConjectures for atlas/sheaf descent and 05YY:
  the existing `SpaceCoverSheafDescent` is 0ADT, algebraic-space objects over a
  space rather than arbitrary small étale sheaves. `AlgebraicSpaceInvertibleDescent`
  is line modules, and `EtaleSheafSpaceAtlasBootstrap` proves fppf sheaf conditions.
  None states this result. grep of the item ID in WeilConjectures found nothing.
* Exact-name rg through both project source roots for `AtlasSheafDescent`,
  `atlasSmallSheafPseudofunctor`, `atlasSheafRestriction`, `enlargedArrow_chartwise`,
  `chartwiseEtaleMap_continuous` found no declarations. The actual model source
  has `chartwiseEtaleMap` but neither of the two additional interfaces below.

No statement correction, new independent definition node, or disputed statement.
All theorem proofs in this delivery are `sorry`. The other proofs are only laws
needed to assemble the explicit definitions; no theorem of the paper is proved.

## Dependency modules

`lem-trf-space-enlarged-etale-ringed-site-model`: the recorded
`SmallEnlargedEtaleModules` publicly retains the whole enlarged ringed-site model
but gives no usable `IsContinuous` instance for `chartwiseEtaleMap`, and no
chartwise-étaleness interface for an arbitrary arrow between enlarged objects.
`Sheaf.AlgebraicGeometry.AtlasEtaleRestriction` imports that entire recorded module
unchanged, and states `enlargedArrow_chartwise` and `chartwiseEtaleMap_continuous`.
Both are consequences of the node's localization assertion: 03LP says small-site
postcomposition is continuous, and 04LY uses étale cancellation for arrows between
objects étale over the same base. Their docstrings give the complete proofs. These
are interfaces to notions already in that dependency, not new notions. Its copied
node changes only `lean`, retains every former declaration in `lean.declarations`,
and explains the missing interface in `lean.note`. The main module then constructs
coherent restriction explicitly with identity-on-sections comparisons, with no
arbitrary maps, choice of a merely nonempty object, or extra assumptions.

## Second reading by Q09

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
