## What changed

Proved `AlgebraicGeometry.Scheme.punctured_dvr_normalization_stalkMap_injective`
in `Sheaf.AlgebraicGeometry.Morphisms.PuncturedDvrNormalizationStalkMapInjective`.
All existing signatures, universes, visibility and public imports are unchanged.
Replaced the proof import of `NormalizationStalkBaseChange` with the Mathlib proof
imports `Mathlib.AlgebraicGeometry.SpreadingOut` and `Mathlib.RingTheory.RingHom.Injective`.
Updated the existing node's proof, proof_deps and proof_origin to the direct argument.

The argument represents a kernel germ on an affine neighbourhood whose germ map is
injective. Its section ring is a domain. A zero germ on the normalization vanishes
on an open neighbourhood meeting the dense image of `toNormalization`. The flat
local stalk map of the original etale/open-immersion composite is faithfully flat
and injective, so the section has zero germ on the original source's image in X.
Localization of the domain section ring makes that base germ map injective, forcing
the section and the original germ to vanish. No normalization/stalk base change is
needed. The unit statement and its route are unchanged; this is a shorter proof of
an auxiliary node below the unit level.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.punctured_dvr_normalization_stalkMap_injective`
(node `lem-sbc-punctured-dvr-normalization-stalk-torsion-free-injective`).
Holes closed: 1. Holes added: 0. No sorry remains in any delivered Lean module.
This is a complete proof, not a decomposition.

The final proof compiles without warnings in about six seconds through lcompile.py.
The explicit axiom check reports exactly `propext`, `Classical.choice`, `Quot.sound`.
There are no source nonemptiness assumptions: the normalization point and density
supply the source point used in the argument. Empty source/open cases are therefore
handled without adding hypotheses.

## No longer needed

Removed proof import:
`Sheaf.AlgebraicGeometry.Morphisms.NormalizationStalkBaseChange`.
The sole planned proof dependency,
`lem-sbc-normalization-stalk-base-change`, and its declaration
`AlgebraicGeometry.Scheme.Hom.isIso_normalizationPullback_stalk`, are unnecessary
for this theorem. The corresponding module is pruned from this module's proof
closure; other users can still need it. No other project proof-dependency module
is imported or required, and there are no new nodes.

## Where the brief, the DAG or earlier work was wrong

The DAG's single base-change step omitted the actual injectivity argument: its
comparison theorem alone does not state injectivity. The shorter argument above
uses only proved Mathlib declarations and avoids this step entirely. The domain
stalk hypothesis and local Noetherianity suffice here; the DVR hypothesis and
boundary hypothesis are not mathematically required, but every original binder
was preserved. The boundary assumption dismisses the impossible positive case of
a membership case split to keep the unchanged named binder explicitly used.

Searches run: LeanFinder for normalization stalk injectivity (germ-injective and
affine-stalk ingredients, no exact theorem); Loogle `RingHom.injective` (simple
ring lemma only); msearch grep and local rg for stalk-map injectivity, normalization
and germ-injective neighbourhoods. `DenseEtaleStalkMapInjective` suggested the germ
argument but requires domain stalks everywhere; it was read, not imported or copied
as a dependency. Mathlib's locally Noetherian IsGermInjective instance supplies the
needed neighbourhood using the domain assumption at only the specified point.

## Second reading by D3

1. Compared the delivered Lean module and node with the repository using `diff`.
   The existing theorem signature is byte for byte unchanged, as are its universes,
   visibility, docstring and public imports. Only its proof and private proof imports
   change. No definition or statement is changed and no change record is required.
   Verdict: pass.
2. Independently compiled the module through lcompile.py without errors or warnings.
   Compiled a scratch copy with `#print axioms` for the theorem: exactly `propext`,
   `Classical.choice` and `Quot.sound`. The delivered file has no `sorry`, axiom,
   unsafe declaration, opaque declaration, external implementation or new definition.
   The witnesses used in the proof come from proved Mathlib theorems, not postponed
   existence assertions. Verdict: pass.
3. There are no new or split-off statements, modules or nodes. Checked the domain
   descent along the injective germ map, the nonempty open supplied by x, and the
   faithfully flat local stalk map. Density supplies a source point without a source
   nonemptiness assumption; an empty source cannot supply the normalization point
   used here. The auxiliary DVR and boundary hypotheses remain unchanged.
   Verdict: pass; zero holes added.
4. Read the proof from its kernel reduction downward and searched the existing Lean
   library for stalk-map injectivity and germ-injective neighbourhoods. Read
   DenseEtaleStalkMapInjective: its public theorem assumes domain stalks everywhere,
   whereas this item assumes one domain stalk, so it is not a direct replacement.
   The new proof imports are private and supply the germ-injective neighbourhood
   and kernel reduction. The removed NormalizationStalkBaseChange import and its
   sole old proof dependency are fully listed under No longer needed. Read
   dag/units/sk-prop-input-spreading.json: its realized fields are empty and neither
   this auxiliary node nor the removed dependency realizes a specified unit step.
   No unit statement, route or record is changed. Verdict: pass.
5. Compared the node diff: only proof, proof_deps and proof_origin change. Its three
   steps accurately describe the affine germ representation, density/naturality
   transport, and faithful-flatness/localization injectivity in the Lean proof.
   The empty project proof_deps agrees with the Mathlib-only proof. No new-node
   metadata or statement-change record is needed. Verdict: pass.

Changes made by the second reader: appended this independent review only; no Lean
proof or DAG repair was necessary. Independently verified one hole closed and zero
holes added. Existing public imports were preserved to retain the public interface.
