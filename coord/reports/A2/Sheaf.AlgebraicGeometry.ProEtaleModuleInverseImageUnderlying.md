## What changed

Proved `AlgebraicGeometry.Scheme.proEtaleModelModuleInverseImage_underlying` with its
original signature, universes and visibility unchanged. Updated its docstring and
DAG proof to describe the implemented construction. No existing definition or
other module was changed, and no forced adaptations are needed.

Added six fully proved supporting modules:

- `Sheaf.CategoryTheory.SheafPullbackForgetComparison`: commute a forgetful functor
  with constructed sheaf pullback by the canonical Kan-extension and sheafification
  comparisons, and prove their compatibility with the actual adjunction units.
- `Sheaf.CategoryTheory.SheafPullbackUnitPresentation`: a specified-unit presentation,
  equality testing on unit sections, product presentations and transport of operations.
- `Sheaf.CategoryTheory.ModuleInverseImageAction`: module actions on the actual
  abelian inverse-image carrier, with semilinear restrictions and unit.
- `Sheaf.CategoryTheory.ModuleInverseImageActionOfPresentations`: construct the scalar
  action and prove all six module laws by equality testing on unit sections. Addition
  is the actual abelian inverse-image addition throughout.
- `Sheaf.CategoryTheory.ModuleInverseImageAdjunction`: prove the converse-linearity
  argument and restrict the abelian adjunction to module maps; compare the resulting
  left adjoint with Mathlib's module pullback.
- `Sheaf.AlgebraicGeometry.ProEtaleModelRingPresentation`: transport the ring adjunction
  through the strict AsSmall equivalences and identify its unit with precisely
  `proEtaleModelRingUnit`, then construct its set inverse-image presentation.

The item's two new imports are proof-only. Each new module uses public imports for
its statement vocabulary and ordinary imports for additional proof machinery.
The private transported ring adjunction is irreducible with a proved unit API;
this avoids repeatedly unfolding `restrictFullyFaithful` during unit comparison.
No heartbeat or time limit was increased. Recompiled all seven repaired modules
with `lcompile.py --all`: all compile without warnings within the single-file limit.

The source argument is [Stacks 03D2](https://stacks.math.columbia.edu/tag/03D2)
and [03D3](https://stacks.math.columbia.edu/tag/03D3). The underlying-algebraic
comparison follows [00YV](https://stacks.math.columbia.edu/tag/00YV);
pro-etale functoriality for arbitrary scheme morphisms is the opening paragraph of
[09A5](https://stacks.math.columbia.edu/tag/09A5). The Lean proof explicitly supplies
the converse-linearity step that 03D3 leaves to the reader.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.proEtaleModelModuleInverseImage_underlying`
(node `lem-weil-pbc-proetale-module-inverse-image-underlying`).

Holes closed: 1. Holes added: 0. No `sorry` remains in any delivered Lean file.
All supporting lemmas and constructions are proved, rather than split off as
unproved obligations. Explicit `#print axioms` checks for the target and all new
public proof results report only `propext`, `Classical.choice` and `Quot.sound`. Data selected by choice in the action construction comes
from its fully proved construction theorem; no unproved existence theorem is used
for choosing data. Lifting a morphism through the faithful forgetful functors also
has a uniquely determined image.

The new public results are
`CategoryTheory.sheafPullbackForgetIso_unit`,
`CategoryTheory.SheafPullbackUnitPresentation.hom_ext`,
`CategoryTheory.SheafPullbackUnitPresentation.map_unit`,
`SheafOfModules.inverseImageAction_of_presentations`,
`SheafOfModules.inverseImage_underlying_of_ring_presentation`, and
`AlgebraicGeometry.Scheme.proEtaleModelRingPresentation`, together with the
explicit comparison, action and presentation definitions recorded below.

Edge cases: the construction uses no nonempty-site, nonzero-ring or flat-scheme
hypothesis. The unit testing criterion also works for the terminal sheaf and
empty sections. The six action laws use only ring-hom laws and the actual additive
unit; therefore the zero ring and zero module require no separate hypothesis.
Finite-limit preservation concerns the base-change functor of sites and holds for
arbitrary scheme morphisms, including morphisms involving the empty scheme.
The proper-base-change unit's three realized proof steps are unchanged: this item
is a helper below that unit, not one of its realized statement or step nodes.

## No longer needed

Removed these five proof imports from the item:

- `Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects`.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`.
- `Sheaf.CategoryTheory.RingedSiteModules`.
- `Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects`.
- `Sheaf.CategoryTheory.SitePullbackAbelianUnderlying`.

Removed the corresponding old direct proof dependencies:
`lem-weil-pbc-adjunction-lifts-group-ring-objects`,
`lem-weil-pbc-ringed-topoi-module-adjunction`,
`def-weil-sheaf-of-modules-category`,
`lem-weil-pbc-sheaf-algebraic-structures-objects`, and
`lem-weil-pbc-site-pullback-abelian-underlying`.
Also removed `lem-weil-pbc-conjugate-iso-unit-equation`: the proof uses Mathlib's
`Adjunction.unit_leftAdjointUniq_hom_app` directly.
The definition of the module category remains part of the theorem's statement
vocabulary, rather than a proof obligation. These are removals from this proof
route; they do not assert that no other target or transitive import needs those
modules. In particular, `ProEtaleInverseImage` still has its own imports.

The second reader also removed three redundant direct import lines from the new
supporting modules: `Mathlib.CategoryTheory.Sites.PreservesSheafification` and
`Mathlib.CategoryTheory.Functor.KanExtension.Preserves` from
`SheafPullbackForgetComparison`, and
`Mathlib.Algebra.Category.Ring.FilteredColimits` from
`ProEtaleModelRingPresentation`. Their APIs remain supplied by the public imports
already required in those modules. No whole-library pruning count is claimed.

The implemented proof does not need to construct internal abelian-group or ring
objects and then identify their lifts. Instead it uses the actual constructed
abelian inverse image, the actual transported ring, and canonical comparisons
that preserve the specified units. No auxiliary modules are withdrawn. Removed the duplicate private declaration
`SheafOfModules.adjunctionOfLinearLifts` (its full statement and proof). The proof
now uses `AlgebraicGeometry.adjunctionOfLinearLifts` from the existing
`Sheaf.AlgebraicGeometry.EtaleInverseImageModuleAdjunction` module. This new
proof dependency can retain transitive imports that this item no longer imports directly.

## Where the brief, the DAG or earlier work was wrong

The original statement is true unchanged. The original broad module-adjunction
existence lemma does not directly normalize its existential ring morphism to the
specified `proEtaleModelRingUnit`; the implemented route keeps that morphism fixed
and proves the action and adjunction explicitly. The previous internal-object
route was unnecessary, rather than mathematically false.

LeanSearch returned an Internal Server Error. Its logged search is recorded as
unavailable, with no claim that absence of search results establishes absence of
a Mathlib theorem. Loogle, LeanFinder and source searches found the canonical
comparison APIs used in the proof, but no existing varying-ring comparison with
the required unit normalization. The returned delivery correctly identified that the private generic helper
`AlgebraicGeometry.adjunctionOfLinearLifts` had been copied verbatim. Its statement
has only generic category and functor binders, so it applies here unchanged.
The repair removes the copied declaration and imports its existing module using
`import all Sheaf.AlgebraicGeometry.EtaleInverseImageModuleAdjunction`; Lean
makes that private helper accessible to this proof without changing its original
visibility or exposing the import to downstream modules. The call now names
`AlgebraicGeometry.adjunctionOfLinearLifts` explicitly. The action-adjunction
node records this dependency. No existing library module needs adaptation.
The previous second reading missed this duplication and is superseded; the next
reader must review the repaired delivery.

## New nodes

`def-weil-pbc-module-inverse-image-action`: explicit module structures on the
actual abelian inverse-image section groups, with semilinear restrictions and
specified-unit linearity; its associated module has the same abelian carrier.

`def-weil-pbc-sheaf-pullback-unit-presentation`: a set inverse-image presentation
retaining the chosen adjunction unit, so scalar multiplication can be transported
without replacing the specified coefficient morphism.

`lem-weil-pbc-sheaf-pullback-unit-presentation`: the proved presentation API:
equality testing on unit sections, product presentations, and compatibility of
transported maps with their source maps on unit sections.

`lem-weil-pbc-sheaf-pullback-forget-comparison`: the proved canonical comparison
commuting forgetting with sheaf pullback, including the exact unit equation.

`lem-weil-pbc-module-inverse-image-action-of-presentations`: the proved construction
of the action, its six module laws, restriction semilinearity and unit linearity.

`lem-weil-pbc-module-inverse-image-action-adjunction`: the proved general module
comparison from a ring unit presentation, via the linearity criterion and
uniqueness of left adjoints.

`lem-weil-pbc-proetale-model-ring-presentation`: the proved comparison identifying
the original transported ring unit with the set inverse-image unit on model sites.

All seven nodes have Lean attachments, source references, detailed proofs where
applicable, and the logged searches. No change record is needed: no existing
statement or definition changes.

## Second reading by A2

1. Compared every delivered module with the repository. Only the item existed;
   the other six modules are new. The existing theorem signature is byte for byte
   identical, including universes and visibility; its original public import remains.
   No existing definition changes. The only changed fields of its existing DAG node
   are `proof`, `proof_deps`, and `proof_origin`. Verdict: passes.

2. Read the complete seven-module argument and the existing generic
   `AlgebraicGeometry.adjunctionOfLinearLifts` proof. The actual abelian carrier and
   additive operations are fixed; the transported scalar action satisfies all six
   module laws, semilinear restriction, and the specified unit equation. Linearity
   of an adjunct implies linearity by equality testing on pairs of unit sections.
   Both module adjunctions have exactly the same restricted pushforward. Compiled
   all seven files using `lcompile.py --all`, without warnings. The scratch audit
   prints axioms for the target, every new public proof result and construction;
   only `propext`, `Classical.choice`, and `Quot.sound` occur. No delivered file
   contains a hole, forbidden declaration, or hollow definition. Choice of action
   data uses the fully proved construction theorem, and the reused helper chooses
   morphisms uniquely determined by their faithful images. Verdict: passes.

3. No statement is split off with `sorry`. Checked the new proved statements and
   definitions against their sectionwise equations and Stacks Tags 03D2, 03D3,
   00YV, and the opening paragraph of 09A5. Empty section sets require no chosen
   elements in the testing criterion. The zero module and zero ring satisfy the
   same six identities, and no nonempty or flatness hypothesis was introduced.
   Repeated LeanFinder, Loogle, and source searches with different terms, including
   `lanCompIsoOfPreserves`, and read the existing module-adjunction and underlying
   abelian-comparison APIs. The latter do not supply the prescribed unit equation.
   The already existing generic adjunction helper is reused through the proof-only
   `import all`, rather than duplicated. Verdict: passes.

4. Checked the proof from the original target downward. It uses Mathlib's canonical
   Kan-extension, sheafification, product, and left-adjoint-uniqueness comparisons.
   The five removed original proof imports and all six removed original direct
   proof-dependency nodes are recorded under `No longer needed`. Kept the original
   statement import and the proof-only status of the two new target imports.
   Removed the three redundant supporting import lines listed above. Tested removal
   of `Grp.FilteredColimits` from the action module and restored it: its instances
   are required to elaborate the public abelian inverse-image signatures, so it is
   a legitimate public import. Read `dag/units/sk-thm-properbasechange.json`:
   this helper realizes none of its statement or step nodes, and the three realized
   steps are untouched. Verdict: passes after import pruning.

5. Checked all eight delivered node files. Each Lean attachment matches the source;
   every `proof_deps` is exactly the union of step `uses`, and the prose follows the
   implemented proof, including the existing generic adjunction helper. All seven
   new nodes have source, searches, creation, blueprint, chapter/unit, and Lean
   records; constructions contain actual data and proved properties. The original
   node's statement and statement dependencies are unchanged. Verdict: passes.

Second reading changes: removed three redundant supporting imports, documented
those removals, refreshed the compile wording, and appended this independent review.
Proof bodies and statements required no repair. Holes closed: the original
`AlgebraicGeometry.Scheme.proEtaleModelModuleInverseImage_underlying`; holes added:
none. This is a proof of 1 of 1 original obligations, with 0 split off.
