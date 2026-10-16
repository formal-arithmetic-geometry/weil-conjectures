## What changed

Proved `AlgebraicGeometry.Scheme.proEtaleModuleInverseImage_canonicalUnitComparison`
without changing its statement. All helper declarations are private and proved.

The canonical module adjunction comes from an explicit Hom equivalence: transport
through the strict AsSmall models, apply the model module adjunction, and transport
back. Its unit agrees sectionwise with the model unit. The existing normalized
module comparison and the unit-compatible uniqueness comparison of abelian left
adjoints give the underlying isomorphism. Their unit equations identify the mate
in the theorem with that isomorphism's inverse.

Repair of the returned duplicate: removed the private theorem
`AlgebraicGeometry.Scheme.modelAbelianAdjunction_unit` entirely. The proof now
maps the adjunction uniqueness equation through the original-site equivalence
and rewrites its right side directly with the existing general Mathlib theorem
`CategoryTheory.Adjunction.map_restrictFullyFaithful_unit_app`. The version in
`Sheaf.AlgebraicGeometry.ProEtaleModuleSpecializationUnit` is private and cannot
be used through an ordinary import. No copy or renamed replacement of that
specialized statement remains. The specialization module is unchanged.

The local Hom equivalence and unit formula were compiled incrementally. Naturality
is checked on elements, and cancellation is factored through a generic adjunction
lemma to avoid expensive unfolding. No library definition or public interface changed.
The DAG node now records this proof and its actual dependencies. The change
record `coord/changes/G3-proetale-canonical-unit-proof-commands.md` documents the
local command changes conservatively flagged by the interface detector.

## Proved and sorry left

Closed the only original hole:
`AlgebraicGeometry.Scheme.proEtaleModuleInverseImage_canonicalUnitComparison`
(node `new-lem-weil-pbc-proetale-module-canonical-unit`).

No `sorry` remains in the delivered module. No holes or split-off statements were added.

## No longer needed

The proof does not use `proEtaleModelModuleInverseImage_underlying`, node
`lem-weil-pbc-proetale-module-inverse-image-underlying`, or its module
`Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying`; its direct proof
import is removed. The stronger normalized comparison is used directly from
`Sheaf.CategoryTheory.ModuleInverseImageAdjunction` instead. The model-ring
presentation and module-action-adjunction dependencies remain necessary.

## Where the brief, the DAG or earlier work was wrong

The previous delivery unnecessarily repeated the private specialization-unit
helper. Applying the already available general Mathlib identity directly removes
that duplicate. The previous second reading concerned the returned version and
has been removed; the repaired version is checked in the second-reading section below.

The original proof plan referred to the bare underlying comparison, which discards
the unit equation needed here. The already proved normalized comparison in
`inverseImage_underlying_of_ring_presentation` supplies that equation directly;
no new theorem is needed.

LeanFinder, Loogle, and Mathlib/library grep searches found generic adjunction and
pullback facts but no exact pro-etale canonical-unit theorem. The proof uses the
existing normalized module comparison and Mathlib adjunction APIs. The statement
and the unit route are unchanged; no immersion, nonempty-site, or nonzero-ring
assumption is introduced, so the empty-scheme and zero-ring cases are included.


## Second reading by G3

1. **Interfaces: pass.** Compared the delivered module with the repository by diff
   and extracted the existing theorem signature: it is byte for byte identical.
   Its visibility and sole public import are unchanged. All added declarations are
   private. Only this module is delivered; no forced adaptation or statement change
   occurs. The command-only change record accurately describes the local universe,
   namespace, variable and elaboration settings.
2. **Proof and constructions: pass.** Compiled the delivered module through
   `lcompile.py` without errors or warnings. The explicit sectionwise Hom maps are
   inverse by the strict AsSmall identities and natural by the model adjunction.
   The resulting unit has the asserted section formula. The normalized comparison
   and adjunction uniqueness equations give `hunit`; injectivity of `homEquiv`
   identifies the mate with the comparison inverse. There are no remaining holes,
   forbidden declarations or hollow definitions. The transported equivalence and
   adjunction data are constructed explicitly, not chosen from mere existence.
   A fresh scratch copy with `#print axioms` reports exactly `propext`,
   `Classical.choice` and `Quot.sound` for the public theorem, with no `sorryAx`.
3. **Split statements and shorter routes: pass.** No statement is split off and
   no hole is added. Inspected the existing normalized module comparison and the
   neighboring pro-etale comparison/specialization proofs. The unnormalized
   underlying isomorphism does not give the required unit equation. Independent
   grep, Loogle and LeanFinder searches with adjunct/invertibility terminology
   found generic adjunction identities, which the proof already uses, and no
   shorter applicable pro-etale theorem. In particular the removed specialized
   `modelAbelianAdjunction_unit` theorem is not reintroduced: the existing general
   Mathlib restriction-unit identity is applied directly. No nonempty-site,
   nonzero-ring or immersion assumption occurs; the argument also covers identity
   maps, zero modules and empty schemes.
4. **Route and pruning: pass.** Read `dag/units/sk-thm-properbasechange.json` and
   its `realized` statement/steps. This comparison lies below those unit steps;
   none is bypassed. Both remaining proof imports are used explicitly, and the
   public inverse-image import is required by the statement. The old proof
   dependency omitted from the new proof is exactly
   `lem-weil-pbc-proetale-module-inverse-image-underlying`, with its direct import
   removed and reported under No longer needed. This is a direct-import pruning
   claim, not a claim that no other target imports that module.
5. **DAG agreement: pass.** The only changed node fields are `proof`,
   `proof_deps` and `proof_origin`. Their four steps match the constructed Hom
   equivalence, normalized comparison, mapped restriction-unit equation and final
   mate cancellation. The dependency union is exactly the three recorded ids;
   inspected each corresponding declaration. The statement, source, unit,
   blueprint and existing Lean record are unchanged. There are no new nodes.

Second reading changed only this report: added the independent point-by-point
review and clarified the obsolete pending-review sentence. The Lean proof and
DAG repair were already correct and are retained.
