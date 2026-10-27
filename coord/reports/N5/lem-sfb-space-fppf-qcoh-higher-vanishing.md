## Worker report

Stage 2, group N5, item lem-sfb-space-fppf-qcoh-higher-vanishing. The accepted
Q25 stage-1 split is preserved. The inherited BLOCKED ending referred to an
obsolete stage-1 assignment, not to the present statement task. The live queue
lists stage 2, the item had no Lean record, and no repair note exists. This follows
coord/brief-stage2.md section 0, the stage-handoff instruction of 2026-10-22.

The delivery adds SpaceFppfQCohHigherVanishing.lean and the genuinely missing
normalized comparison definition in SpaceFppfRingedComparison.lean. The only
postponed proofs are space_fppf_qcoh_higher_vanishing and the auxiliary
SpaceFppfRings.directImage_additive, owned and described by the new definition
node. The definition module contains real structure/predicate data; its enough
injectives instance is the existing Grothendieck-category theorem applied to
module sheaves on the chosen small site. No object is chosen from a sorry.

Statement correspondence, hypothesis by hypothesis and clause by clause:

- A scheme S: `{S : Scheme.{u}}`, Mathlib's locally affine locally ringed space.
- An algebraic space W over S: `W : AlgebraicSpace S`, the existing full
  subcategory of fppf sheaves with representable diagonal and an étale atlas.
- A module on the small étale site: `M : W.Modules`; its quasi-coherence is
  `hM : M.IsQuasicoherent`, the same Mathlib local-presentation predicate used
  by `AlgebraicSpace.QCoh`. No finite presentation or finite generation occurs.
- The enlarged étale model is reused through `enlargedSchemeInclusion`,
  `ObjectProperty.ι`, and `SpaceFppfSite.etaleIso`; its owning recorded module
  AtlasEtaleRestriction is publicly imported by the definition module.
- The chosen small big site is `B : SpaceFppfSite W`. `B.C` is a small category
  in the ambient `u+1` universe, presented by a fully faithful essentially
  surjective inclusion into spaces over W in the fixed universe bound.
  `etaleInclusion` and `etaleIso` are the inclusion of the same étale scheme
  objects. Essential surjectivity expresses a skeleton of all spaces in that
  fixed bound, rather than arbitrary test objects with no atlas refinements.
- The covering condition is `B.coverings_iff`: the arrows of a covering
  presieve give exactly `IsFppfCover`, the existing predicate for chartwise
  flatness, local finite presentation and joint surjectivity. Empty families
  are not excluded. `B.topology` is its generated Grothendieck topology.
- The ring sheaf is `R.rings` for `R : SpaceFppfRings B`. Its `sections T`
  bijection identifies values with `spaceRegularSections` of the actual source
  space. These are Mathlib's compatible global sections of its existing étale
  structure sheaf. The zero, one, add, mul and restriction fields identify
  every operation and every pullback on all commuting scheme charts. They
  specify regular functions, not an unrelated abstract ring sheaf.
- `R.smallRings`, `smallSections`, and `smallRestriction` give the canonical
  lifted structure sheaf on the SAME small étale site. `ringRestriction` and
  `normalization` fix the structural ring comparison by ordinary pullback of
  functions on every scheme chart. This retains coefficient and site sizes:
  small étale objects have universe `u+1`, morphisms `u`, and the big-site
  module carriers use `u+1`. No equality of those universes is imposed.
- The morphism of topoi is `R.geometric`, with `geometric_direct` fixing its
  direct image to actual precomposition. Together with the specified ring
  comparison this is the canonical ringed morphism in adjoint direct-image
  form. `R.directImage` is literally Mathlib's `SheafOfModules.pushforward`
  of `R.ringRestriction.hom`; its underlying objects and arrows are restriction.
  This uses the supplied generic geometric-morphism notion, not an arbitrarily
  selected module functor. The specialized generic RingedToposMorphism record
  fixes both hom universes equal; it is imported but not redefined or forced
  onto the existing unequal-universe small étale category. The concrete
  continuous-functor/ring-map construction already supplies the required
  morphism of ringed topoi without changing that dependency record.
- `F : SheafOfModules.{u+1} R.rings` and
  `_hF : IsSpaceFppfSectionExtension R M F` are the module sheaf called M^a.
  Its sections field identifies F(V) with the actual global sections of
  `(moduleTensorPullback v).obj M`. The zero, add and smul fields fix its
  additive and scalar structures. Its restriction equation says on every chart
  that restriction is `moduleTensorSection h ... 1`, followed by the recorded
  `moduleTensorComposition` and the equality of the structure arrows in the
  slice (`Over.w`). Thus the extension is specified on EVERY object, operation,
  and restriction; it is not an arbitrary sheaf with a convenient property.
  The node says to let M^a be this sheaf, so the theorem quantifies over any
  presentation with these exact bijections, rather than postulating acyclicity
  or constructing an arbitrary choice. No additional comparison theorem is
  assumed. The normalized model is independent of the desired conclusion.
- Higher direct images computed by module injective resolutions are
  `R.directImage.rightDerived i`. The enough-injectives instance comes from
  `SheafOfModules.isGrothendieckAbelian` and
  `IsGrothendieckAbelian.enoughInjectives`; Mathlib's rightDerived uses
  `InjectiveResolution`, not an alternative cohomology theory.
- Every strictly positive degree is `i : ℕ`, `hi : 0 < i`.
- Vanishing as a module sheaf is
  `IsZero ((R.directImage.rightDerived i).obj F)`, in the small étale module
  category with the canonical common ambient lift of the ring. Such a lift
  changes the universe encoding of carriers, not the site or ringed topos.
- There is no quasi-compactness, separation, noetherian, finite-generation,
  characteristic, or bounded-rank hypothesis on W or M.

Dependency declarations read and reused:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicGeometry.AlgebraicSpace,
  IsAlgebraicSpace, EtaleSite, etaleTopology, structureSheaf, Modules.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule:
  AlgebraicGeometry.AlgebraicSpace.QCoh, with Mathlib's
  SheafOfModules.IsQuasicoherent and its local-presentation docstring.
- Sheaf.AlgebraicGeometry.AtlasEtaleRestriction: chartwiseEtaleMap_continuous;
  its public SmallEnlargedEtaleModules/EnlargedEtaleRingedSite chain gives
  enlargedSchemeInclusion, EnlargedEtaleSite and the normalized structure sheaf.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: AlgebraicGeometry.Flat, with the
  affine formulation and its stated stalkwise equivalence.
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:
  AlgebraicGeometry.LocallyOfFinitePresentation.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations:
  ModuleDirectImageModel, moduleChartScalar, ModuleChart,
  moduleTensorPullback, moduleTensorSection and their unit normalization.
- Sheaf.CategoryTheory.RingedSiteModules: ringedSiteModules is exactly
  SheafOfModules. The latter's pushforward is from Mathlib's
  Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous.
- Sheaf.CategoryTheory.RingedToposMorphism: RingedToposMorphism, read in full;
  for this concrete site presentation the ringed morphism is expressed by the
  existing GeometricMorphism and the explicit structural-ring comparison.
- Mathlib.CategoryTheory.Preadditive.Injective.Basic and Resolution:
  CategoryTheory.Injective and InjectiveResolution.
- def-weil-size-convention is the recorded metatheoretic convention, expressed
  by explicit u and u+1 universes rather than an extra object.
- New definition inputs reuse IsFppfCover in AlgebraicSpaceFppfCoveringCalculus,
  moduleTensorComposition in SpaceFlatDirectImageBaseChange, and
  CategoryTheory.GeometricMorphism in Sites.GeometricMorphism. All were read
  with their full signatures and source/proof docstrings.

All already-stated proof dependencies are imported, publicly when also used in
statement data and privately otherwise. Mathlib-only proof matches are imported
through their recorded source modules. The ringed cohomology-sheafification and
new affine-scheme fppf acyclicity nodes have no Lean attachment yet and therefore
supply no import. The proof docstring carries all five accepted proof steps,
including the abelian-resolution transport and the warning that forgetting
module structure need not preserve injectives.

Edge cases checked before writing: i=0 is deliberately excluded (direct image
of a nonzero M is generally nonzero); every positive i is included. M=0 is
allowed. No bound on a set of local generators appears. W empty is allowed,
with empty covering families retained in the covering iff. Non-quasi-compact
and nonseparated spaces remain valid inputs. Test-chart and coefficient
universes are not made artificially equal; the site and all of its slices are
small relative to the common ambient coefficients. No statement correction or
STATEMENT-DISPUTED flag is needed.

Searches made (all through the prescribed wrapper where applicable):

- leanfinder: "Quasi coherent modules on algebraic spaces have vanishing higher
  direct images from the big fppf site to the small etale site": 8 hits, led by
  SheafOfModules.isQuasicoherent and Scheme.Modules.instAbelian; no match.
- loogle: `"SheafOfModules", "rightDerived"`: 0 hits.
- Mathlib grep: `fppf|Fppf` in AlgebraicGeometry: 7 hits in Fpqc,
  Cover.QuasiCompact and FlatDescent; no algebraic-space higher-image theorem.
- rg in lean/WeilConjectures and lean/Sheaf: fppf/big-site and higher-vanishing
  searches find scheme fppf material, fppf covering calculus and enlarged étale
  models, but no big-fppf module comparison or this vanishing theorem.
- rg for this item's blueprint id in lean/WeilConjectures: no declaration.
- The additional missing-notion searches are recorded verbatim in the new
  node's mathlib_searches, including LeanSearch, LeanFinder, Mathlib grep,
  project grep and DAG/blueprint searches.

Validation: scompile.py compiled EACH delivered file in sandbox and library
module mode against the live server build, with its private sibling overlay.
Both files passed cleanly (only postponed theorem proofs remain). Line lengths
are at most 100; autoImplicit is false and u is explicitly declared. No live
source was edited, no direct Git command or global build was run.

## New nodes

`def-sfb-space-fppf-ringed-comparison` defines the normalized chosen small big
fppf site, its regular-function ring sheaf, concrete restriction direct image,
and the tensor-section-extension predicate. It follows the actual morphism a_X
and section formula of spaces-more-cohomology.tex, section-fppf-etale-modules,
Tag 0DGN(1),(3); coverings are Tag 03Y8. It is not a second definition of
algebraic space, quasi-coherence, fppf covering, module sheaf, tensor pullback,
or tensor-composition map: each is the recorded existing declaration.

The search for "fppf ringed comparison" found zero blueprint nodes. The related
DAG nodes about flat-object derived sections, affine fppf cohomology, fibred
fppf inverse image and scheme big-site admissibility do not define this
comparison. LeanSearch's 8 hits concern scheme sites, structure sheaves and
quasi-coherent presentations. LeanFinder's 8 hits concern scheme ringed
morphisms, sites and limit lemmas. The exact-name Mathlib and project grep
found zero hits. Full results and queries are in mathlib_searches. No generic
notion is copied. The model fixes all values and restriction maps and includes
no vanishing assumption or finiteness restriction. The auxiliary additivity
statement is the structural verification of the concrete direct-image
construction; its proof is sorry with its complete proof docstring and is
listed in this definition node's lean.declarations.

## Second reading by N5

A separate full second pass was performed by the same worker because this
assignment expressly forbids starting other agents; no independent worker
review is claimed. The maintainer's delivery review remains independent.

I reopened the source lemma, node and both final files. The node asks only for
a_W, not epsilon_W, so the theorem asserts exactly the former vanishing and
does not silently add the other clause of 0DGN(7). It does not assert vanishing
of module-to-abelian direct images or change coefficients to the base field.
I checked S, W, M and quasi-coherence against their four binders, the chosen
site against coverings_iff/etaleIso, every ring operation and restriction
against SpaceFppfRings, the geometric direct image against geometric_direct,
and all tensor-section restrictions against IsSpaceFppfSectionExtension.
The final IsZero is in module sheaves and rightDerived uses module injective
resolutions. Positive i, arbitrary W and arbitrary quasi-coherent M are
retained. All definitions contain actual structure/predicate data, and the
only sorrys are named, source-documented theorem declarations owned by the
recorded nodes. I checked the two universe levels separately and retained the
canonical ambient ring lift on the same small site. No hypothesis is an
acyclicity assumption in disguise.

The compiler-guided corrections made before this pass were an explicit
category argument to sheafPushforwardContinuous, an explicit local continuity
instance inside the direct-image definition, and transparent carrier casts in
the scalar formula. These correct elaboration without changing the
mathematical statement. The last compile passed both modules separately.

A final edge-case audit caught and repaired an overstrong ring-normalization
condition: a commuting map to a scheme object must be the map specified by
`B.etaleIso`, not any map over W. For a disconnected étale object with a deck
automorphism, the latter would wrongly require invariance of all regular
functions. The final `normalization.hg` explicitly uses the chosen inclusion
isomorphism. The accepted mathematical statement is unchanged; this is a
correction of the new definition's encoding before delivery.
