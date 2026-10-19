## Worker report

This packet retains the repair of returned head b1db180d12d1 and now repairs
the definition-ownership return on head f535b5a8d4dc. The initial saved-packet dry run passed
mechanically (84527a02c9), but its abstract-category statement still had the
returned mathematical defects. That packet was not pushed. The replacement is
`lean/Sheaf/Paper/RingedRefinementCoefficientSquare.lean`, with the sole postponed
proof `SheafOfModules.ringedRefinementCoefficientSquare`.

The theorem asserts existence of the canonical presentation and its laws, for
ordinary sites and for ringed diagram sites. Presentation structures are
conclusion data, not hypotheses restricting the node's schemes, coefficients or
inputs. They use the existing module/derived constructions and characterize every
comparison independently of the desired square. No construction is chosen from
an unproved mere-existence theorem. Helper definitions and structures all belong
to this node, have source/blueprint docstrings, and are in `lean.declarations`.
No statement correction is required. The returned-head repair below adds a
definition-node re-export for the already existing ringed operation declarations.

Clause-by-clause reading:

* Schemes are `Scheme.{u}`. For a fixed ambient `T`, `Over T` describes arbitrary
  schemes mapping to it. Take `T=T₂`, `Z=Over.mk (𝟙 T₂)`, `Y=Over.mk u`, and
  `X=Over.mk j₂` to obtain precisely the node's triangle. `Laws.square`, `left`,
  `right` and `Refinements.map` bind `u,j₁,j₂`, `IsProper u.left`, both
  `IsOpenImmersion` and both `QuasiCompact` hypotheses, and `h : j₁ ≫ u = j₂`.
  No cartesian assumption is made on this original triangle.
* `Rings .ordinary T` is literally commutative ring sheaves on `T.ProEt`.
  `a : A ⟶ B` is universally quantified in the square and its coherences.
  `Coefficients.rings W` is the actual canonical ring-sheaf inverse image along
  `W.hom`, including its action on `a`. Ring compositors are fixed sectionwise
  by `Coefficients.sections`; `pull` is their adjoint conjugate, and
  `structural` is its specified ring-adjunction transpose.
* `category c W A` is `ProjectionRestriction.Der` of that inverse-image ring:
  ordinary unbounded `DerivedCategory` of the recorded module sheaves. Sites
  have objects in `Type (u+1)` and morphisms in `Type u`; coefficient elements
  are in `Type (u+1)`, modules/derived objects in `Type (u+2)`, and derived
  morphisms in `Type (u+2)`. Categories are never parameters in `Type u`.
* `Calculus.operation` uses the landed `ProjectionRestriction.Operation` for
  the actual site base-change functor. `Calculus.coefficient` fixes its ring
  map to `structural`. Pullback, direct image, their module adjunction, exact
  derived inverse image, right derived direct image and derived adjunction are
  those constructions, not freely supplied functors/adjunctions. `OpenModel`
  is the exact fully faithful left adjoint of this same open restriction.
  `Calculus.shriek` is its termwise exact localization; `openAdjunction` is the
  existing exact localization of that ordinary adjunction.
* `Calculus.scalar W a` is the recorded
  `DerivedChangeOfRingsCochainModel.{u+1,u,u+1,u+2,u+2}`. Its object/map equations,
  universal cochain counit and K-flat computation fix scalar extension.
  `ScalarComparisons.insertion` fixes the ordinary adjunction at `1 tensor x`;
  `restriction_sections`, `ordinary_mate` and `representative` fix the
  inverse-image/scalar comparison before any refinement law is stated.
* `Shape` has `V,b,q,s`, both the scheme and over-category pullback properties,
  `s ≫ q = 𝟙 X`, `s ≫ b = j₁`, open-immersion properties and clopen range.
  `Package.shapes` supplies such data for every permitted triangle. These data
  are used by `OpenComparisons.h`, including its `beta`, `pi`, `sectionPull`
  and `openFactor` factors.
* `OpenComparisons.pi_image` is the open-unit equation on the selected component;
  `pi_complement` is zero after restriction to every complementary open.
  Together they characterize the identity/zero clopen projection on all inputs.
  `beta_inverse` characterizes beta by the normalized open unit and the actual
  pullback compositor. `OpenComparisons.h` is the displayed three-factor
  geometric map (with the final section and open-composition identifications).
* `Refinements.adjunct` fixes every `r_D` to the `u^-1 ⊣ Ru_*` adjunct of this
  `h_D`. The returned counterexample `r_A=1,r_B=0` is consequently unavailable.
* `ScalarComparisons.delta_inverse` characterizes each delta using the open
  unit and canonical inverse-image/scalar comparison. `ScalarComparisons.chi`
  is defined by `mateEquiv` from that comparison and the two canonical derived
  adjunctions. Its counit transpose is exactly the node's chi. It is a natural
  transformation, with no invertibility or flatness hypothesis.
* `left` is `S(r_A)`, then chi on `j₁! M`, then `Ru_*(delta₁)`.
  `right` is delta₂ then `r_B` at `S_X M`. `Laws.square` equates these natural
  transformations on the whole derived category, hence at every unbounded M.
* `Laws.natural` is the actual input-morphism naturality equation.
  `coefficient`, `open_coefficient`, `coefficient_identity`, `open_identity`
  and `coefficient_square` are separate coefficient pasting, unit and commuting
  coefficient-square equations. `ScalarComposition.pure`, `representative`,
  `unit_pure` and `unit_representative` normalize the balanced identifications.
  They do not repeat the refinement square.
* `Laws.refinements` is the actual equality between the composite refinement
  and the two successive r maps with the canonical direct-image compositor.
  `refinement_identity` is its normalized identity case.
  `spatial_coefficient` is the chi/direct-image-composition equation. The
  compositors are defined from sectionwise ordinary direct image by
  adjunction conjugation and exact localization. Thus these equations specify
  compatibility of the coefficient squares under successive refinements.
* `Shifts` gives scalar shifts normalized by the cochain counit, and separate
  `NatTrans.CommShift` assertions for the inverse/scalar comparison, delta,
  chi, beta, pi, r, and the two square composites, for every integer shift.
* `Mode.systems` uses the actual vertical sequence site `ℕ × T.ProEt` and its
  topology from `OpenTensorNormalization`. A ring sheaf there retains all
  ring transitions, and module sheaves retain the semilinear module transitions.
  The same definitions and separate laws hold on its ordinary unbounded derived
  module category, before evaluation, total limit or normalization.
* `finiteRing` is the actual constant ring on this diagram site.
  `finiteDirect`, `finiteInverse`, `finiteScalar` and `finiteSystemScalar` use
  constant sections and sheafification. `FiniteRealization` identifies strict
  constant-coefficient towers with these modules, fixes all additive sections
  and transition maps, and fixes the action of constant scalars.
  `FiniteComparison` fixes ordinary direct image on sections, inverse image
  by its ordinary adjunction unit, derived inverse image on cochain
  representatives, derived direct image by the adjunction comparison, and
  shriek by the open unit. `FiniteNormalization` equates the transported actual
  `StrictTower.gamma`, including the identity-proper `rId` identification,
  with `Refinements.map`. This is a comparison with the dependency's map,
  not another square assertion and not an arbitrary equivalence of arrows.

Dependency interfaces used in types and constructions:

* Mathlib's `Scheme`, `IsProper`, `IsOpenImmersion`, `QuasiCompact`, `ProEt`,
  `IsPullback`, sheaf inverse image/adjunction, module sheaves and
  `DerivedCategory`; `CategoryTheory.conjugateIsoEquiv`, `mateEquiv`,
  `Functor.mapDerivedCategoryNatIso`, compositors and representative factors.
* `Sheaf.Paper.RingedProjectionRestriction`:
  `AlgebraicGeometry.Scheme.ProjectionRestriction.Mod`, `Der`, `Operation`,
  `Operation.pullback`, `.pushforward`, `.left`, `.right`, `.moduleAdjunction`
  and `.derivedAdjunction`. The new definition node `def-pur-ringed-module-derived-operations` owns this existing interface and is cited in `stmt_deps`; the restriction theorem node is not a statement dependency.
* `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel`, `.E`, `.T`, `.ε`, `.obj_eq`
  and its universal/K-flat conditions.
* `Sheaf.SixFunctors.OpenTensorNormalization`:
  `Mode`, `Site`, `topology`, `baseChange`, their continuity/size instances,
  and `exactDerivedAdjunction`.
* `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`:
  `SheafOfModules.SuccessiveDerivedQuotient.pure`, to normalize actual
  tensor insertions, balanced coefficient multiplication and identity maps.
* `Sheaf.Paper.SemilinearDerivedSections`:
  `WeilConjectures.SemilinearSections.AdjunctionEvaluation`, with its actual
  left/right unit and counit comparison equations, for finite realization.
* `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus` and its imports:
  `AlgebraicGeometry.ProEtale.StrictTower.coefficients`, `Towers`, `Derived`,
  `towerPullback`, `towerDirectImage`, `G`, `R`, `J`, `adj`, `jAdj`, `rId`, `gamma`.
  `finiteOrdinaryAdjunction` is their recorded termwise module adjunction.

The recorded theorems `ringedProjectionMateExact`, `localizedSystemExact`,
`openTensorNormalization`, `ringedCoefficientProjectionCocycle`,
`exists_diagramSite_realization`, `semilinearDerivedSections` and
`normalizedProperOpenCalculus` are proof dependencies, not assertions that are
executed by a statement-only file. Their signatures/docstrings were read. The
proof docstring explains their roles: exact adjunctions, open restriction and
extension, normalized comparisons, cocycle, ringed diagram realization,
semilinear compatibility and finite refinement calculus respectively. The
statement now actually uses the above canonical dependency constructions rather
than importing theorem names and supplying arbitrary replacements.

Edge cases: empty schemes and empty/whole opens are allowed; pi's two component
conditions reduce to zero or identity as appropriate. Identity proper maps and
identity coefficient maps have explicit equations. Zero objects and all integer
shifts are included. A→B is arbitrary, including non-flat and zero-ring maps;
chi is never inverted. No noetherian, boundedness, normalization, cartesian-square
or detection-of-map-equality hypothesis is introduced. Derived/site universes
are retained at their actual sizes, not equated. Constant finite comparison is
stated for every finite commutative ring without characteristic restrictions.

Searches: `msearch.py leanfinder` queried “coefficient change clopen normalized
refinement mate ordinary derived ring sheaf proetale” (8 unrelated etale or
normalization results, no exact statement); `loogle` queried
“CategoryTheory.mateEquiv, CategoryTheory.Adjunction.homEquiv” (0 results);
`grep` queried “refinement.*coefficient|clopen.*scalar” (0 matches).
`rg` over Mathlib/upstream/project and the item-id search found no exact node
statement; existing `ProperOpenCoefficientRefinement`/`RefinementCoefficientMate`
interfaces are restricted to finite etale coefficients and bounded/noetherian
settings and do not state this ringed unbounded result. Existing module
operations, cochain scalar models and strict-tower maps above were reused.

No `STATEMENT-DISPUTED` flag: the node's mathematical statement is retained.
The faulty arbitrary-category encoding was replaced, not used to correct or
weaken the source. No dependency module is needed: owning-node comparison
helpers specialize existing, usable canonical interfaces.

## Second reading by NA

The dispatcher prohibits additional agents. I performed a fresh self-review
against every paragraph of the node and the immutable-head return, rather than
claiming an independent second reader. The initial saved report was rejected
in this reading: its category parameters, arbitrary maps, repeated laws and
universe claims did not justify the node. All were replaced as detailed above.

The return's H3/H5 fault is repaired by actual inverse-image ring sheaves,
recorded module/derived operations, normalized scalar representatives, and the
h/adjunct, delta/open-unit and chi/counit constructions. The geometric fields
now enter the h map. The H3 coherence fault is repaired by distinct equations,
including genuine strict-system and finite-map comparisons. The H3 size fault
is repaired by the actual pro-etale size convention. The H4/H9 report now
separates dependency constructions used in types from theorems used only in the
natural-language proof. The H11 rereading includes these checks explicitly.

I checked the directions of ring pullback compositors, beta and delta inverse
transposes, the proper adjunction mate, each side of the main square,
coefficient associators and identity maps, successive proper compositors,
shift transformations, and the finite identity-proper comparison. Each helper
has actual data; only the named main theorem has `sorry`. The node is copied
from current main and changes only `lean` and the addition of the new
operations definition dependency to `stmt_deps`. Compilation and delivery validation are
recorded below after the final checks.

## Repair retry self-check (2026-10-18)

The required first dry run of the retained packet failed in `finiteScalar`,
`FiniteRealization.derived` and `FiniteComparison.pull_model`. The finite
comparison must use the strict-tower dependency's standard localization Hom
universe `u+2`, separately from its ordinary module Hom universe `u+1`.
The retry fixes these elaboration annotations without changing the geometric
hypotheses, the coefficient systems, the canonical maps or the theorem signature.
It also removes the overlong finite-scalar type line.

The current-main node was compared directly with the sandbox copy: the only
changed fields remain `lean` and the added operations definition dependency in
`stmt_deps` (the latest ownership repair is detailed below). A fresh source search for `ringedRefinementCoefficientSquare`,
`namespace .*RingedRefinement` and the item id in the named upstream/project
trees found no competing declaration. I reread the main node, the saved module,
the current blueprint purity-transport proof, and the actual `Operation`,
`DerivedChangeOfRingsCochainModel`, diagram `Mode`/`Site`/`topology`, strict-tower
operations and `AdjunctionEvaluation` interfaces. The sectionwise ring and
module equations, K-flat representative equations, open-unit transposes and
proper adjunction mate remain the characterizations used by the saved repair.
The main theorem is still the only postponed theorem; no definition is selected
from its existential conclusion.

An isolated helper compiled cleanly with the fixed `CommRingCat.carrier.{u+1}`
return type and transparency-respecting elaboration. The finite section uses
those settings so elaboration preserves the dependency's original universes.
The public imports now name `RingedProjectionRestriction` and
`SuccessiveDerivedQuotientNormalization` directly, since their operations and
pure-tensor normalizations occur in the statement's helper types.

The final diagnosis was confirmed with `#synth`: the full imports selected
`WeilConjectures.integralCoefficientRingSheafify.{u, ?v}` and
`WeilConjectures.scalarReductionSiteSmall.{u, ?v}`, leaving the second universe
unresolved. The fixed helper explicitly selects their existing `{u, 0}`
specializations inside definitions. The isolated constant-scalar helper passed
both wrapper compilation phases without warnings (21.0 s and 49.9 s including
slot acquisition). This changes no site, ring, category or mathematical
hypothesis. The finite derived realization also explicitly retains localization
Hom universe `u+2`; it does not equate that universe with ordinary module Homs.

`FiniteComparison.pull_model` now refers to the owning-node helper
`finitePullModel`, whose body is the same representative equation verbatim.
This lets the definition fix both actual scheme-site smallness proofs before
elaborating the equation. No smallness premise or universe equality is added
to the field. The helper is documented and listed in `lean.declarations`.

Profiling the clean packet exposed repeated localization expansion and costly
serialization (the server reported 15.5 s in `.olean` serialization). The
performance repair turns `Coefficients.rings`, `Calculus.shriek`,
`FiniteRealization.derived`, `additivePresheaf` and `finiteRing` from expanding
abbreviations into definitions of the identical constructions. The named
`Calculus.shriekShift` instance is the existing exact-functor shift instance,
with actual data, documented and recorded. The theorem and all coherence
equations are unchanged. No profiling option is present in the delivery.

Final full-module `scompile.py` validation passed both phases with no errors or
warnings: sandbox 36.7 s and final module name 58.9 s (wrapper wall times,
including slot acquisition), under the unchanged 60-second per-file limit.
The permissive unfolding option is scoped only to `siteTriangle`, `siteComp`,
`siteId` and `Laws`, where the scheme/over-category instances require it.
There is one `sorry`, the named theorem, and no overlong lines or diagnostic
commands in the module. The immutable-head return was rechecked against all
its requested replacements as explained above.

## New nodes

`def-pur-ringed-module-derived-operations` is an `existing: true` definition-node
re-export of `AlgebraicGeometry.Scheme.ProjectionRestriction.Operation` and its
existing `Mod`, `Der`, operation, shift, representative and adjunction definitions
in `Sheaf.Paper.RingedProjectionRestriction`. No Lean declaration is copied.
Its source is Stacks 03D7 and 07A6, the ordinary and derived module adjunctions.
The full datum retains the published site sizes, coefficient map, continuity,
right adjoint, additive and exact pullback structures and K-injective resolutions.
Its conclusions are definitions, with no assertion that every ringed-site map
has exact pullback. `Mod` is exactly `SheafOfModules` of the forgotten ring;
`Der` is its standard ordinary unbounded localization. The four operation
functors and both adjunctions are the existing constructions, not arbitrary
fields. The shift and representative helpers retain the same definitions.

LeanSearch found 8 ordinary module-adjunction candidates; Loogle found 5
pullback-adjunction and conjugacy candidates; the Mathlib grep for
`structure Operation|def derivedAdjunction|def moduleAdjunction` found 0.
The exact outputs are recorded in the node's `mathlib_searches`. Source grep
found no upstream `ProjectionRestriction` operation; project grep found the
existing declarations in `RingedProjectionRestriction.lean`. DAG grep found no
definition node carrying those names. The blueprint search for
`ringed module operations` found 0 nodes. The existing pro-etale operations node
is scheme-specific with identified coefficients, and the system-tensor-mate
node fixes arithmetic towers; neither owns the general ringed-site datum.
Accordingly the existing project declarations are reused through a new node,
as explicitly allowed by the maintainer return, rather than redefined.

## Returned-head ownership repair (2026-10-18)

The saved packet's required initial dry run passed (commit `235c9e7139`), but
the immutable-head `f535b5a8d4dc` return requires a substantive dependency-ownership
repair. The packet now cites `def-pur-ringed-module-derived-operations` in
`stmt_deps` in place of the extra theorem-node dependency
`lem-weil-pbc-ringed-projection-restriction`. The already present public import
`Sheaf.Paper.RingedProjectionRestriction` is exactly the new node's recorded
module. The item does not use the theorem's restriction/local-detection conclusion.
The helper definitions, all equations and the theorem signature are unchanged.
The node's original mathematical statement and its proof dependencies stay intact.
Only the new definition node and the item's permitted `lean`/`stmt_deps` fields
are changed relative to current main, besides this report and the retained module.

I reread `Operation`, its implicit site/universe binders and every re-exported
operation/adjunction signature and docstring. The new node matches its exact
fields and definitions; in particular it does not claim existence or impose
new conditions on the item's rings or schemes. Its technical proof structures
remain conclusion data in `Calculus.operation`, as in the independently checked
packet. Empty sites, zero rings, identity morphisms and arbitrary coefficient
maps are not excluded. The preserved ordinary/system and finite comparison
clauses, clopen equations, adjunction transposes and shift laws are unchanged.
No additional agent was started; this is the required author's self-check.
The initial clean compile gives no reason to split the finite section; the
same module will be checked again by the final dry run and delivery wrappers.

The repaired packet passed `deliver2.py --no-push`: commit `c432e16385`
passed the server preflight and all per-file compilation/declaration checks.
The staged set contains the retained module, the item node, the new definition
node and this report. No Lean error or unexpected warning remains.
