## Worker report

Stage 2, direct delivery by Q74. The module
`Sheaf.AlgebraicGeometry.SpaceAffineModuleHigherImageVanishing` states
`AlgebraicGeometry.AlgebraicSpace.isZero_moduleHigherDirectImage_of_affine`.
Its single proof is `sorry`; there are no new definitions, instances, auxiliary
axioms or extra nodes. I read the accepted five-step split and preserved it.
The node changes only in `lean` and the addition of two already landed statement
dependencies, `def-sfb-space-small-ringed-model` and
`def-sfb-space-derived-module-calculus`. There is no statement correction.

I read Stacks `spaces-cohomology.tex`, lemma-affine-vanishing-higher-direct-images
(Tag 073H), including its proof using representability and scheme affine
vanishing. I also read `sites-cohomology.tex`, lemma-cohomology-modules-abelian-agree
(Tag 03FD): it compares module and additive cohomology globally and on every
object. This is the comparison required by the item's module interpretation;
the theorem does not silently replace module direct image by abelian direct image.

The Lean correspondence, hypothesis by hypothesis and clause by clause, is:

- `S : Scheme.{u}` is the arbitrary base scheme, and `V W : AlgebraicSpace S`
  are algebraic spaces over it, with their original fppf-sheaf definition.
  `a : V ⟶ W` is the named morphism over the base.
- `ha : IsRepresentableWith (fun _ _ p ↦ IsAffineHom p.left) a.hom.hom`
  requires a representing scheme pullback with affine projection for every
  scheme test over W. Reading `IsRepresentableWith` showed it includes the
  representing pullback square, not just a conditional test on pullbacks that
  happen to exist. This exactly expresses the item's affineness.
- `M : V.Modules` is an arbitrary sheaf of modules over the actual small-etale
  structure sheaf. `hM : M.IsQuasicoherent` is Mathlib's local presentation
  predicate, the predicate underlying the recorded `QCoh` full subcategory.
  The resolution is in the category of ALL module sheaves, never in QCoh.
- `q : ℕ`, `hq : 0 < q` covers exactly every positive integer q. There is no
  assertion about degree zero and no loss of any positive degree.
- Mathlib `Functor.rightDerived` is defined by applying the functor to injective
  resolutions and taking cohomology. The instance supplied explicitly to it
  is `InjectiveResolution.instHasInjectiveResolutions`, using
  `IsGrothendieckAbelian.enoughInjectives` and
  `SheafOfModules.isGrothendieckAbelian V.smallStructureRings`. These are real
  existing declarations, not new obligations or assumptions. In particular,
  no `[EnoughInjectives ...]` or chosen abelian structure is added as a binder.
- `smallModuleDirectImage a` is the existing conjugate
  `V.smallModuleEquivalence.inverse ⋙ moduleDirectImage a ⋙
  W.smallModuleRestriction`. Its input is the restriction of M. The target
  `smallModuleEquivalence.inverse.obj` transports the higher image back into
  the original `W.Modules`. The conclusion is `IsZero` of this MODULE object.
  Restriction is an equivalence, hence exact and preserves injectives; deriving
  this conjugate and transporting back is precisely the injective-resolution
  higher image of the original chart-limit direct image. No independently
  selected functor, coefficient lift or cohomology construction is introduced.

I opened the complete recorded declaration and docstring in
`AlgebraicSpace.lean` (AlgebraicSpace, IsRepresentableWith, EtaleSite, structureSheaf,
Modules), `AlgebraicSpaceQuasiCoherentModule.lean` (QCoh and its original-universe
slice instances), `AlgebraicSpaceModuleOperations.lean` (ModuleDirectImageModel,
moduleDirectImage and its universal-property normalization),
`RingedSiteModules.lean` (ringedSiteModules), and Mathlib's
`Preadditive/Injective/Resolution.lean` (InjectiveResolution). I additionally
read `AlgebraicSpaceSmallRingedModel.lean` (smallModuleRestriction,
smallModuleRestriction_isEquivalence, smallModuleEquivalence, SmallModules) and
`AlgebraicSpaceDerivedModules.lean` (smallModuleDirectImage and its additive
instance), and Mathlib `Abelian/RightDerived.lean` and
`Abelian/GrothendieckCategory/EnoughInjectives.lean`. The existing small model
retains section universe u even though the original site's object universe is
u+1. Nothing forces those universes equal.

All stated proof dependencies have imports, including the module/additive
forgetful comparison, chartwise permanence, enlarged-site restriction,
chart-limit comparison, injective-module additive acyclicity, sheafified higher
images, acyclic resolutions and homology preservation. The remaining proof
node `lem-sfb-space-affine-higher-direct-image-vanishing` has no Lean record or
Mathlib match on the read base, so there is no module to import for it yet.
It is a proof prerequisite only; it is not needed to elaborate this statement.
The theorem docstring retains all five accepted proof steps and the caution
that forgetting injective modules need not give injective abelian sheaves.

Edge cases checked against the source and the signature: empty source or
empty target when a morphism exists; M=0; q=1 and arbitrarily large q;
identity affine maps; affine maps that are not finite type; arbitrary base
characteristic; no Noetherianity, properness, coherence or flatness.
There is no nonemptiness assumption and no dependence on an empty universal
family to make the conclusion vacuous. Injective resolutions really exist by
the explicit Grothendieck argument in the signature.

Searches (executed with msearch.py, recorded in searches.jsonl):

- LeanFinder: `For an affine morphism of algebraic spaces the positive right
  derived direct images of a quasi coherent structure module vanish`.
  Eight hits: affine scheme limit/localization facts, scheme module abelianness
  and pushforward additivity, and vanishing on injective objects. None gives
  the algebraic-space quasi-coherent module theorem.
- Loogle: `"SheafOfModules", "rightDerived"`: zero hits.
- grep: `affine.*(rightDerived|higherDirectImage)|(rightDerived|higherDirectImage).*affine`:
  zero Mathlib hits.
- LeanSearch, second phrasing: `Positive derived pushforwards of quasi coherent
  module sheaves vanish for affine maps of algebraic spaces`: eight hits,
  consisting of underived module pushforwards, section formulas and adjunctions.
- I searched the project `WeilConjectures/` and `Sheaf/`, the upstream name
  index, and Mathlib for the new declaration name and affine higher-image
  concepts. The upstream
  `AlgebraicGeometry.Scheme.Modules.isZero_higherDirectImage_of_isAffineHom`
  is about Zariski scheme modules, not algebraic spaces on the small etale
  site; I read its full signature and docstring. The item's blueprint tag has
  no project declaration. There is no exact existing attachment.

Validation: the delivered module compiled cleanly via batch2/scompile.py in
module mode, both as the sandbox and as its final library module (6.1 seconds
and 2.4 seconds). Scratch probes established the same small-model instances
without an extra hypothesis; they are not delivered. The dry run and push
are run with batch2/deliver2.py as prescribed.

## Second reading by Q74

This is the direct-delivery worker's self-check, not a claim that a second agent
read the file. The maintainer provides the independent review. I reopened the
node and the final signature together. Each named object is unchanged: the
base S, morphism a, original module M, and the quasi-coherence and affine
hypotheses all occur explicitly. I unfolded the existing smallModuleDirectImage
and smallModuleEquivalence source to check that the expression derives the
specified direct image, rather than an arbitrary functor. I checked that the
outer inverse equivalence returns an object of W.Modules, so IsZero asserts
module vanishing. I checked the chosen resolution instance is obtained from
existing Grothendieck and enough-injectives declarations, without a postponed
helper theorem. The only interface adjustment is adding the two landed model
nodes to stmt_deps; the accepted mathematical statement and proof are intact.
There is one theorem and one sorry, no lets or local instances in the signature,
and no declaration name collision. No mathematical mismatch or statement
dispute was found.
