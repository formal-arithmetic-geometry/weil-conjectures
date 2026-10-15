## What changed

Repair: removed the duplicate private `weaklyEtale_setLimits` proof from the item.
The immersion factorization now reuses the existing
`AlgebraicGeometry.Scheme.restriction_preservesLimits` theorem from
`Sheaf.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal`; that helper is
exported so this module can use it. No duplicate theorem statement remains.

Proved `AlgebraicGeometry.Scheme.proEtale_immersion_inverseImage_preservesLimits`
with its signature and public imports unchanged. The proof retains the affine closed
extra-adjunction route, proves Zariski localization, factors the immersion into closed
and open immersions, and transfers preservation through conservative forgetful functors.
For the final coefficient isomorphism it uses the specified tensor extension functor,
reuses the existing tensor/restriction adjunction from the operations module, and
identifies it with an equivalence.

Added proved modules `Sheaf.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal`,
`Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageComparison`, and
`Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph`. The comparison
module constructs the natural abelian comparison and combines it with the scalar graph.
The scalar graph is fully proved for arbitrary generalized sections using normalized
unit presentations and their universal property.

Strengthened the existing, proved
`SheafOfModules.inverseImage_underlying_of_ring_presentation` with its adjunction-unit
normalization equation. Its hypotheses are unchanged. Retaining the unit equation of
the already constructed lifted adjunction proves the extra clause; no new assumption
or postponed proof is used. Adapted the unclaimed module
`Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying` to discard the extra
clause and retain its original public statement. Every private helper is proved.
Updated the item's DAG, the scalar-graph DAG and the strengthened comparison's DAG.

## Proved and sorry left

Closed the item's one original hole:
`AlgebraicGeometry.Scheme.proEtale_immersion_inverseImage_preservesLimits`
(node `lem-weil-pbc-proetale-immersion-limit-preservation`).

Also proved the four new public results:

- `AlgebraicGeometry.Scheme.restriction_preservesLimits`
- `AlgebraicGeometry.Scheme.proEtale_inverseImage_limits_zariski_local`
- `AlgebraicGeometry.Scheme.proEtale_moduleInverseImage_comparison`
- `AlgebraicGeometry.Scheme.proEtale_moduleInverseImage_scalarGraph`

The strengthened
`SheafOfModules.inverseImage_underlying_of_ring_presentation` and adapted
`AlgebraicGeometry.Scheme.proEtaleModelModuleInverseImage_underlying` are also proved.
There is no `sorry` in any of the six delivered Lean files. Holes closed: 1;
holes added: 0. No unfinished draft, diagnostic module or split-off obligation is
submitted. The existing affine extra-adjunction and model inverse-image dependencies
remain the specified project inputs; their independent proof status is unchanged.

All six files compile in sandbox import order under the normal per-file 60 s limit.
The scalar graph takes about 55 s, the main theorem under 31 s, the generic normalized
comparison about 23 s, and the other files less. The delivery tool supplies the
independent compile and axiom checks.

## No longer needed

The removed item-local `weaklyEtale_setLimits` helper and its repeated adjunction
construction are no longer needed; the existing restriction theorem supplies the
same result.

Removed these six proof imports from the item:

- `Sheaf.CategoryTheory.SiteMorphismComposition`:
  `lem-weil-pbc-site-morphism-composition` is replaced by Mathlib's composition of
  adjunctions, base-change composition and uniqueness of left adjoints.
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`:
  `lem-weil-pbc-site-pullback-abelian-exact` is replaced by left-adjoint preservation
  of colimits, the underlying comparison and faithful additive forgetful functors.
- `Sheaf.CategoryTheory.SitePullbackAbelianUnderlying`:
  `lem-weil-pbc-site-pullback-abelian-underlying` is replaced by a proved local helper
  with the actual pro-etale site universes.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`:
  `lem-weil-proetale-weakly-etale-localization` is replaced by the existing over-category
  map/base-change adjunction and its sheaf adjunction.
- `Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage`: no separate proof API from this
  module is used; the actual inverse-image definitions remain imported.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: the cover and local-isomorphism arguments
  use Mathlib and the existing source-library pro-etale covering API directly.

Also removed the item's direct DAG proof dependencies on
`lem-weil-pbc-right-adjoint-preserves-limits`,
`lem-weil-pbc-site-sheaf-sets-limits-sectionwise`,
`lem-weil-pbc-algebraic-sheaf-iff-underlying-sets`, and
`lem-weil-pbc-module-sheaves-limits-sectionwise`: the corresponding limit, reflection,
and module-sheaf APIs are already in Mathlib or the proved source library.
The static project import closure additionally drops these nine transitive modules:

- `Sheaf.CategoryTheory.SheafRingObjectReconstruction`
- `Sheaf.CategoryTheory.SheafRingObjectsBijective`
- `Sheaf.CategoryTheory.SheafRingObjectsInjective`
- `Sheaf.CategoryTheory.SheafRingObjectsSurjective`
- `Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects`
- `Sheaf.CategoryTheory.SheavesAlgebraicStructuresRing`
- `Sheaf.CategoryTheory.SheavesAlgebraicStructuresRingCore`
- `Sheaf.CategoryTheory.SheavesAlgebraicStructuresRingMorphism`
- `Sheaf.CategoryTheory.SiteContinuousPushforwardSheaf`

A proof-only `import all Sheaf.AlgebraicGeometry.ProEtaleOperations` reuses its
already proved private tensor/restriction adjunction and scalar equivalence. This removes
about 210 lines of duplicate private construction from the inherited attempt, including
`proEtaleScalarEquivalence`, `proEtaleRingExtensionPresheaf`, `proEtaleRingExtension`,
`proEtale_changeOfRingsMap_tmul`, `proEtaleExtensionToRestrict`,
`proEtaleExtensionFromRestrict`, `proEtaleExtensionHomEquiv`,
`proEtaleRingExtensionHomEquiv`, and
`proEtaleRingExtensionAdjunction`. The new all-limit preservation argument remains.

The definitions shared with the statement remain statement dependencies. These are
pruned dependencies of this proof; other parents may still need the same modules.
No blueprint unit statement or realized unit step was removed or bypassed.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated `restriction_preservesLimits` word for word under
the private name `weaklyEtale_setLimits`. The repair exposes and imports the existing
theorem and uses it in the immersion composition proof, as required by the import
prune check.

The planned generic abelian-underlying theorem requires a small category whose object
and morphism universes coincide. The actual pro-etale category has different object
and morphism universes. Its proof was adapted privately using the already proved
abelian/group-object equivalence at the required universes, without changing its module.

An existing source-library open-cover conservativity proof imports a different variant
of the pro-etale notation and inverse-image definitions. Importing it together with the
item's definitions produces incompatible notation. The needed local sheaf-isomorphism
argument is proved directly instead, using the compatible source-library covering API.

The planned module scalar-action argument needs more than an arbitrary underlying
abelian comparison. The existing generic theorem constructed the correct adjunction
but discarded its unit equation. Retaining that equation gives the needed normalized
comparison under the same hypotheses. Scalar compatibility then follows from the unit
presentation's `hom_ext`; it holds on arbitrary generalized sections, which cannot be
assumed to be individual images of source sections. The model/actual comparison's
naturality transports this equality back to the actual pro-etale site.

Repeatedly unfolding the model ring unit and chosen module pullback made the initial
combined proof exceed the time limit. The final proof uses these definitions locally
as irreducible terms and works through the normalized unit APIs. Explicit identity
comparison maps avoid large whole-functor definitional equality checks. No definition,
target statement or target meaning changes.

The delivery tool's shared source-index cache repeatedly restarted while its base
commit advanced, then waited on `library-builder.lock`. The interrupted preflight's
trace shows repeated `delivery_cache._load` / `load` calls. The dry run was restarted
with the tool's built-in `WEIL_DELIVERY_CACHE_DISABLE=1` mode, which runs the original
source scanners and retains every compile, axiom and source gate. No tool was edited,
no timeout was increased, and no check was skipped.

## New nodes

`lem-weil-pbc-proetale-inverse-image-limits-zariski-local` records Zariski localization
of all-limit preservation, with joint conservativity of open restrictions proved using
local invertibility of sheaf maps. Its statement allows any scheme morphism and includes
empty schemes. The corresponding new module is proved without a hole.

`lem-weil-pbc-proetale-module-inverse-image-comparison` records the natural underlying
abelian comparison together with scalar graph transport. Unit presentations normalize
the module and ring comparisons; their universal property extends the equality from
source unit sections to all target generalized sections. It is strictly the module
comparison part of the item's argument and contains no limit-preservation conclusion.
Both the scalar-graph input and comparison assembly are fully proved.

`lem-weil-pbc-proetale-restriction-preserves-limits` records the weakly etale
restriction theorem exported by the Zariski-local module. It is the adjunction-and
sectionwise-limit helper used in the immersion factorization and has its own proof
docstring and declaration record.

`lem-weil-pbc-proetale-module-inverse-image-scalar-graph` records the proved
scalar-action compatibility on arbitrary test sheaves. It uses the strengthened generic
module comparison, canonical forgetful comparison, normalized ring presentation and
unit-presentation uniqueness. It has no limit or exactness assertion. Its edge cases
include the zero ring and empty schemes; no nonzero or nonempty hypothesis is used.

All four nodes are in `sec-proper-base-change`, inherit unit `sk-thm-properbasechange`, and
refer through the item to blueprint ancestor `lem-weil-pbc-reconstruction-uniform-tower`.
Blueprint searches found no duplicate. LeanFinder, Loogle and Mathlib grep searches
were recorded; LeanSearch was attempted and reported its internal-server-error outage.
Change records:
`coord/changes/proetale-immersion-proof-scope.md` records the main module's new
private proof scopes. `coord/changes/D2-normalized-module-inverse-image-comparison.md`
records the strengthened proved comparison, its one proof adaptation and every
transitive user. Only the generic comparison statement strengthens; the item and all
existing downstream public signatures remain unchanged.

## Earlier second reading (a previous round; superseded)

1. **Signatures and accidental changes — pass.** Compared every delivered module with the repository version. The item's target declaration and all existing public declarations retain their original signatures. The only interface change is the declared strengthening of `SheafOfModules.inverseImage_underlying_of_ring_presentation`, recorded in `coord/changes/D2-normalized-module-inverse-image-comparison.md`; its unclaimed downstream adapter preserves the original public statement. The four added declarations are new nodes with matching Lean statements.

2. **Proof and trust checks — pass.** Compiled all six delivered Lean files in sandbox import order with `lcompile.py --all`. No delivered file contains `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or `debug.skipKernelTC`; no definition contains postponed data. The proof uses only the existing open declarations listed in the DAG and proved project/Mathlib APIs. The delivery preflight will perform the declaration-level axiom check.

3. **New statements — pass.** Checked each new node against its Lean declaration, its docstring, and the source route. The Zariski-local theorem has no extra separation, nonemptiness, or immersion hypothesis. The scalar-graph and comparison statements quantify over arbitrary generalized sections and retain the same ring/module comparisons for all test sheaves. Searches recorded in each node found no existing Mathlib or upstream declaration duplicating these results.

4. **Pruning and route — pass.** The proof follows the unit route through affine closed inverse-image adjunction, Zariski localization, immersion factorization, abelian comparison, module comparison, and scalar extension. Removed proof-only imports and stale DAG dependencies listed under `## No longer needed`; the unit's statement and realized route remain intact. The new modules are imported privately by the item where they are proof inputs.

5. **DAG agreement — pass.** Updated the item's proof and proof dependencies to match the actual Lean route. Added the four new nodes with source, blueprint ancestry, proof steps, searches, and exact Lean declarations. Updated the normalized-comparison node and change record to describe the retained unit equation and the adapted underlying module theorem.

Changed during this second reading: no proof or statement changes were needed after compilation; the report was expanded with this review record, and the final import visibility was rechecked as proof-only imports.

## Forced adaptations

`Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying` was adapted because the
strengthened `SheafOfModules.inverseImage_underlying_of_ring_presentation` now returns
an existential pair `(e, unit_equation)` instead of `Nonempty e`. The original final
expression no longer elaborated; the forced change destructures the pair and returns
`⟨e⟩`, preserving the adapter's original public signature exactly.

`Sheaf.CategoryTheory.ModuleInverseImageAdjunction` is delivered with the strengthened
source declaration itself. Its private helper
`inverseImage_underlying_of_actions` was changed in lockstep so that the public theorem
can retain the unit equation. The proof-only elaboration options were removed after the
proof compiled without them; no public import, variable, definition, or existing public
signature other than the declared comparison theorem changed.

## Second reading by D2

1. **Signatures and accidental changes — pass.** I diffed all delivered modules against
   `/home/ubuntu/weil-conjectures-sheaf/lean`. The target theorem and the existing
   adapter retain their original signatures. The only intentional public statement
   strengthening is `SheafOfModules.inverseImage_underlying_of_ring_presentation`,
   recorded in `coord/changes/D2-normalized-module-inverse-image-comparison.md`; the
   private helper's matching strengthening is recorded there as well. The four new
   public declarations have matching DAG `lean.statement` fields.

2. **Proof and trust checks — pass.** `lcompile.py --all` compiled all six delivered
   Lean files in sandbox import order with no diagnostics. A source scan found no
   `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or
   `debug.skipKernelTC`, and no definition contains postponed data. The delivery probe
   is the remaining declaration-level axiom check.

3. **New statements — pass.** The Zariski-local result has exactly the arbitrary scheme
   morphism and affine-open hypotheses in its node, with no separation or nonemptiness
   assumption. The scalar-graph and comparison results quantify over arbitrary
   generalized sections and preserve the ring/module comparison data. Searches recorded
   in the node files found no duplicate Mathlib or upstream result.

4. **Pruning and route — pass.** The main proof uses the affine closed adjunction,
   Zariski localization, immersion factorization, abelian comparison, normalized module
   comparison, scalar graph, and tensor/restriction equivalence recorded in its node.
   Removed imports and proof dependencies listed under `## No longer needed` are absent
   from the final proof. The unit's realized route remains represented by the item and
   its four strictly intermediate nodes.

5. **DAG agreement — pass.** The item and all four new nodes have declarations,
   statements, proof steps, proof dependencies, source origins, blueprint ancestry and
   unit fields matching the delivered Lean. The normalized-comparison node and change
   record describe both the retained unit equation and the forced adapter.

Changed during this second reading: corrected the change-record user table to the
checker-visible form, recorded the private helper statement strengthening, and added
this exact second-reading section plus the forced-adaptation evidence. No Lean proof or
mathematical statement required repair.
