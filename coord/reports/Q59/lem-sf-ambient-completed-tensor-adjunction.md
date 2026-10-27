## Worker report

The delivery states the node in `Sheaf.Paper.AmbientCompletedTensorAdjunction`.
The primary declaration is
`CategoryTheory.AmbientCompletedTensor.ambientCompletedTensorAdjunction`.
The integral specialization and the implication from the recorded constructible
predicate are separate declarations of the same node. All four theorem proofs
are `sorry`; the definitions have actual data. No natural-language statement,
proof, or proof dependency was changed.

Clause-by-clause reading:

- The small site is `{C : Type u} [SmallCategory C]` and
  `J : GrothendieckTopology C`. This is the Grothendieck-topology presentation
  of the recorded site/sheaf convention, not a different module category.
  `A : Type u`, `[CommRing A]`, `[IsNoetherianRing A]`, `I : Ideal A`,
  `r : ℕ`, `a : Fin r → A`, `ha : Ideal.span (Set.range a) = I`
  give precisely the Noetherian coefficient ring and its finite generating list.
- `ConstantCompletion.completed J A I` is the specified sheaf limit B;
  `finite J A I n` is the constant quotient A/I^(n+1), and `projection` and
  `transition` are its actual limit projections and quotient transitions.
  The harmless n+1 indexing retains all positive powers.
- `ConstantCompletion.Mod`, `Cx`, `D`, `Q`, `TD` and `TQ` reuse module sheaves,
  cochain complexes, their standard derived localization, and the derived
  category of strict module towers. `moduleDerived` supplies the very same
  standard localization; it does not posit a new derived category.
- `S : CoefficientClosedStructure` and `models : CoefficientTensorModels` is a presentation of the existing derived tensor,
  normalized by `models.iso` on K-flat representatives. It exists by the
  already-landed `ringedSiteDualityMaps_exists`; it is universally quantified
  presentation data, not a restriction on P or L. The tensor bifunctor is
  `S.tensor`. No tensor-Hom adjunction is asserted by this node.
- `finiteTensor` extends each input along the actual projection, takes the
  existing `coefficientTotalTensor` over B_n and applies the recorded scalar
  restriction functor. This is exactly P_n tensor^L_{B_n} L_n on good
  representatives, including the direct-sum total differential.
- `finiteGenerator` is the existing sheafification and total summand inclusion,
  with the two scalar-extension sections. `finiteTensorStep_existsUnique`
  characterizes the actual quotient transition on every such generator;
  `finiteTensorStep` chooses from that unique characterization, not from an
  undetermined existence. `finiteTensorTower` uses those strict transitions.
  These are helpers of the node's specified tensor tower, not an independent
  new notion or a replacement of the existing sheaf tensor.
- `Good` abbreviates the conjunction of the recorded K-flat and flat-term
  predicates. `goodLocalization` uses the existing localization. The main
  inputs themselves are arbitrary objects of `D B × D B`: good complexes
  occur only in the computation clause, not as additional input hypotheses.
- The functor `T : D B × D B ⥤ TD B` is the derived strict tensor tower.
  The natural isomorphism `β : S.closed.tensor ⋙ quotientPresentation.tower ≅ T`
  is the asserted isomorphism of strict derived towers, not a family of
  unrelated component isomorphisms. For every pair of good representatives,
  `V`, `κ`, `e` identify its value with the actual finiteTensorTower.
  The equation containing `models.iso`, `quotientPresentation.comparison`
  and `TQ.map b.hom` fixes β on these representatives.
  The final quantified formula fixes `b` after evaluation at every n, degree,
  slice and pure tensor: c tensor (x tensor y) maps to
  (1 tensor x) tensor (c tensor y). Thus its quotient-unit specialization
  c=1 is the tensor of the two actual quotient augmentations. The transitions
  are retained by κ and b being isomorphisms of strict towers.
- `T ⋙ rlim B` is precisely the total derived limit defining the completed
  tensor. The natural transformation `ν` is its map from ordinary tensor;
  the next equation is exactly completionUnit followed by Rlim(β)=ν.
  It fixes the completion unit, rather than choosing an arbitrary map.
- `K : KoszulPresentation ... true r a` and the natural isomorphism `γ`
  identify that completed tensor with the Koszul completion of ordinary tensor.
  The equation `ν.app M ≫ γ.hom.app M = koszulUnit ...` preserves the units.
- `IsComplete (projection J A I 0) L` is the existing
  `IsLocallyDerivedRingedIdealComplete` predicate for the projection kernel.
  `flat_and_quotients` identifies this kernel with IB. The predicate tests
  RHom(B_U[1/t],L|_U)=0 for every U and every section of that ideal.
  `Function.Bijective (fun f ↦ ν.app M ≫ f)` is exactly the requested map
  Hom(completed tensor,L) → Hom(ordinary tensor,L). Naturality in both inputs
  is encoded by β, ν and γ being natural transformations/isomorphisms; in
  complete targets it is ordinary functoriality of postcomposition.
- `WeilConjectures.integralAmbientCompletedTensorAdjunction` uses the published
  `IntegralOnSlice.completedTensor`, its `completionUnit`, its normalized
  ordinary tensor. The already-published comparison with
  `integralOperationsTensorOnGood` identifies its quotient-tensor Roos model
  in the proof. The repeated bare Nonempty comparison clause was removed
  under return F2. The conclusion is the same bijection for all
  P,L,K in the integral ambient category with local completeness of K.
  The scheme universe t and field universe u are independent; the small
  pro-etale site's objects have universe t+1 and arrows universe t.
- `WeilConjectures.integralConstructible_locallyComplete` uses the exact
  recorded `sfIntegralConstructible` predicate, in its published universe
  convention. It implies the local condition: on every slice a global section
  locally divisible by the actual uniformizer has zero
  `integralCompletionLocalTest`. This existing test is precisely localized
  coefficient RHom against the restricted target. There is no constructibility,
  separatedness, Tor or amplitude condition on either tensor input.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; the retained Mathlib
  `GrothendieckTopology` / `Sheaf` component encodes the site used here.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules` = Mathlib `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory.standard`, `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom` publicly retains
  `CategoryTheory.derivedInternalHomOfUniverses`; this is the internal Hom
  appearing in the duality model. Its ordinary-module abbreviation is not
  misapplied to module sheaves.
- `Mathlib.Algebra.Homology.BifunctorShift` and the existing
  `coefficientTotalTensor` use `CochainComplex.mapBifunctor` and the canonical
  monoidal structure of sheaves of modules.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`; `ConstantCompletion.res` is exactly it.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `CategoryTheory.IsDerivedLimit` is the Roos-triangle predicate. For the
  functorial strict limit in this statement we use the existing
  `ConstantCompletion.StrictLimit`, `rlim`, `limitComparison` and the recorded
  strict-tower homotopy-limit theorem, rather than choose an arbitrary
  triangulated-category cone.
- `Sheaf.Paper.ConstantCompletionEquivalence`:
  `completed`, `finite`, `projection`, `transition`, `change`, `res`,
  `tensorSection`, `reductionTower`, `quotientPresentation`, `completionUnit`,
  `KoszulPresentation`, `koszulCompletion`, `koszulUnit`, `IsComplete`.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`:
  `coefficientTotalTensor`, `coefficientTensorGenerator`, `CoefficientTensorModels`.
- `Sheaf.CategoryTheory.RingedSiteDualityMaps`:
  `RingedSiteDualityModel`, `ringedSiteDualityMaps_exists`, the representative
  comparison `CoefficientTensorModels.iso`.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`:
  `IntegralOnSlice.completedTensor`, `duality`, `completionUnit`, `D`, `ring`;
  the published global quotient tensor is `integralOperationsTensorOnGood`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`.
- `Sheaf.Paper.RoosIntrinsicCompletenessEquivalence`:
  `integralCompletionScalarValue`, `integralCompletionLocalTest`,
  `roosIntrinsicCompletenessEquivalence`.

All recorded proof-dependency modules are imported, with ordinary proof-only
imports where they do not occur in the signature. In particular the main proof
plan uses K-flat resolution, total-tensor K-flatness, coefficient change,
resolving-class descent, strict Rlim, constant/completed Koszul comparison and
the reflector. The integral implication additionally uses the principal Koszul
strict replacement and the Roos/local completeness equivalence. The definition nodes used directly in the signatures are cited in stmt_deps:
`def-coef-ringed-tensor-hom-model`,
`def-sfb-constant-completion-coefficient-data`,
`def-pur-strict-quotient-completion-data`,
`def-sfb-quotient-kernel-completeness`,
`def-sf-constant-coefficient-koszul-completion-data` and
`def-sf-integral-local-completion-test`.
The constant-completion and Roos/intrinsic equivalence theorem nodes occur
only in proof_deps: the signature uses plain definitions from their modules,
not data chosen from either theorem.

Edge cases checked against the source and the signatures: the empty generating
list and I=0 (completion is the original object); I=1 and the zero ring
(completed coefficient category is zero); empty site; zero inputs; n=0 is the
first positive power; unbounded complexes; arbitrary complete targets; characteristic
two (the existing total differential carries the correct sign); independent
pro-etale site object/morphism and coefficient universes. No identification of
ordinary tensor with completed tensor is asserted. No disputed statement found.

Searches (2026-10-23):

- msearch leanfinder: "The strict quotient tower completed derived tensor
  product is Koszul completion and has the same maps into locally derived
  complete targets" — eight ordinary AdicCompletion/tensor hits; no match.
- msearch loogle: "AdicCompletion, CategoryTheory.Adjunction" — zero hits.
- msearch leansearch: "Strict quotient tower completion of the derived tensor
  of sheaves over a Noetherian ring has the same maps into locally complete
  targets" — eight ordinary adic completion / Noetherian module hits; no match.
- msearch grep: "completion.*(tensor|adjunction)|tensor.*completion" — six
  Mathlib hits in ordinary AdicCompletion/AsTensorProduct and Smooth/Flat;
  none gives this statement.
- rg of WeilConjectures for that completion/tensor expression found ordinary
  formal geometry and coherent tensor-row lemmas, not the strict ringed-site
  assertion. Searching for the item id there found no declaration.
- rg of Sheaf for completedTensor, quotientTensor, tensorCompletion and strict
  tensor/tower expressions found the existing integral operations and
  `IntegralTensorReductionTowerComparison`. Those were read and reused;
  their specialization alone does not assert this general-site result.
  `ConstantCompletion.koszul_quotient_reflector` supplies the completion part,
  but does not state the strict two-input tensor comparison or the integral
  category implication, so it is not an exact existing match for this node.
- rg of Sheaf, WeilConjectures and dag/lean_names_upstream.json found no
  declaration colliding with the newly introduced qualified names.

Validation: scompile.py is used for every compiler invocation. The sandbox
and actual library-module checks will be rerun by the required dry run and
final delivery. The maintainer performs the independent mathematical reading;
no subagent or independent second reader was started by this worker.

Dry-run repair: the first preflight rejected the direct public import of
RingedSiteDualityMaps because its module is marked by the route-pivot dropped-node
list. The general statement now uses the smaller existing CoefficientClosedStructure
and CoefficientTensorModels definition interface directly; no duality-map import is
needed there. The integral specialization continues to refer to the published
IntegralOnSlice.duality tensor through its recorded integral-operations module.
The node's new statement dependencies omit the unused duality-maps theorem node.


## Returned delivery repairs

The saved packet was inspected and its prescribed initial dry run passed on
2026-10-23 (temporary dry-run commit b38b8834ed6). The returned immutable head
8af3b04444db was identified in the maintainer's return. The saved packet's
module and its original stmt_deps still contained both findings. The current
read clone's item differs from the saved packet only in lean and stmt_deps;
its statement, proof, proof_deps and source have been preserved. Delivery tools
rebase the repaired packet onto current live sheaf-dag.

F1 (H2/H12): removed lem-weil-pbc-constant-completion-equivalence and
lem-pur-roos-intrinsic-completeness-equivalence from stmt_deps; both remain in
proof_deps and their proof plans remain in the theorem docstrings. Added the
three requested existing definition owners and the two new existing:true
owners described below. No old definition node was edited. In particular,
ConstantCompletion.completed/finite/projection/change/tensorSection/Mod/Cx/D/Q
come from def-sfb-constant-completion-coefficient-data;
transition/res/TD/TQ/rlim/reductionComplex/quotientPresentation/completionUnit
come from def-pur-strict-quotient-completion-data; IsComplete comes from
def-sfb-quotient-kernel-completeness. KoszulPresentation/koszulCompletion/koszulUnit
and integralCompletionScalarValue/integralCompletionLocalTest are owned by the
two new definition nodes. The existing upstream declarations and real bodies
were read: no data here is a .choose from either equivalence theorem.

F2 (H3/H4): removed the first, bare Nonempty isomorphism clause of
integralAmbientCompletedTensorAdjunction, which repeated the published
IntegralOnSlice.completedTensor_global_comparison. That comparison remains an
existing input to the proof, rather than a newly stated result. The integral
conclusion retains precisely the completion-unit Hom bijection with the same
local divisibility/RHom vanishing condition. The general strict-tower comparison
is still pinned on actual sectionwise pure tensors by the formula
c tensor (x tensor y) maps to (1 tensor x) tensor (c tensor y), including
quotient transitions, the quotient-unit equation and the koszulUnit equation.
No natural-language node statement correction is needed: this removes a
redundant Lean clause while using the published comparison for the same
specialization.

The advisory about the general small-site coefficient and object universe u
is retained explicitly: this is the same small-site convention used by the
published coefficient data and Koszul interface. The integral specialization
continues to have independent t and u. No new equality of universes was added.

## New nodes

`def-sf-constant-coefficient-koszul-completion-data` records the three existing
wrappers in Sheaf.Paper.ConstantCompletionEquivalence as existing:true:
CategoryTheory.ConstantCompletion.KoszulPresentation, koszulCompletion and
koszulUnit. For either constant or completed coefficient sheaf, the presentation
is the existing RingedKoszulLimitPresentation on the images of the finite list;
completion and unit are its specified projections in the standard localization.
Its source is Stacks 0A0E and the recorded strict ringed Koszul system.
The statement cites the coefficient-data, strict-quotient-data and ringed-Koszul
system nodes from which these wrappers are formed. No Noetherian or reflector
assertion is included. The empty finite list and either Boolean coefficient
choice are allowed. All three Lean declarations were read in full, including
their letI standard-localization bindings. No duplicate module is delivered.

`def-sf-integral-local-completion-test` records the two existing real definitions
in Sheaf.Paper.RoosIntrinsicCompletenessEquivalence as existing:true:
WeilConjectures.integralCompletionScalarValue and integralCompletionLocalTest.
The first is the uniformizer's actual constant-to-limit image; the second is
derived internal Hom from the localized coefficient module in degree zero to
the canonical derived slice restriction. Its source is Stacks 0999/0A0E.
Its statement cites the existing coefficient extension, completed coefficients,
integral operations, ringed section localization, derived restriction and derived
internal Hom nodes. The local section is arbitrary: no divisibility or vanishing
hypothesis is built into the definition. Both independent scheme/coefficient
universes and the small pro-etale site's distinct object/arrow sizes are kept.
No duplicate module is delivered.

Searches for both new nodes (2026-10-23): msearch leanfinder on Koszul derived
completion presentation/functor/unit and uniformizer local test returned eight
ordinary completion/perfectoid/local-cohomology hits; msearch leansearch on
derived Koszul limits for module sheaves and localization RHom returned eight
ordinary adic-completion and sheaf-limit hits; neither matches these definitions.
msearch grep for the five wrapper/helper names returned zero Mathlib hits.
The exact queries and returned top names are in each new node's mathlib_searches.
rg in WeilConjectures returned no exact wrappers; rg in Sheaf found the two
published modules reused here. rg and a declaration-owner audit of dag/nodes
found only theorem-node attachments for these five names, with no definition
owner. tools/blueprint_refs.py search 'Koszul presentation' found zero nodes.
The generic RingedKoszulLimitPresentation already has a definition owner and
is cited, not duplicated. Definition-node statements introduce their own
objects and assert no theorem conclusion.

## Second reading by Q59

Self-check of the repair by this worker, with the node, all three delivered
node files and the module open; no independent second reader was started,
following the dispatcher's instruction not to start agents. The maintainer's
independent immutable-head review supplies the independent reading for this
returned packet. F1 and F2 above identify the mismatches it found and the
concrete repairs. The main general statement and its full generator formula,
unit equations, Koszul comparison and Hom bijection were retained verbatim.
The integral signature now starts directly with forall P L K; its local test
and precomposition function are unchanged. The constructible-target implication
is unchanged. The two new nodes name exact existing definitions, not copies or
new theorems; their dependencies were checked against their bodies. All bound
variables/universes remain explicit with autoImplicit false. The four existing
sorry theorem stubs remain the only postponed proofs in the delivered module.
The general-site and integral edge cases listed above still apply, including
r=0/I=0, I=A, n=0 indexing and arbitrary unbounded inputs.


Repair validation (2026-10-23): the repaired module passed scompile.py both as
a sandbox module and under its actual library module name. The repaired
three-node packet then passed deliver2.py --no-push (de5731a51b6), including
server preflight, compilation and existing-definition attachment checks.
The final report-only wording correction was followed by another prescribed
dry run before delivery. A local self-check confirms that the main Lean
signature is unchanged verbatim, the natural-language statement, proof and
proof_deps are unchanged from current main, both theorem dependencies are
proof-only, the five requested definition nodes are cited, the new-node TeX
citations match stmt_deps, and there are no overlong Lean lines. No unrequested
source or launcher-tool edit was made.
