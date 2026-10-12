## What changed

Replaced the only sorry in `Sheaf.AlgebraicGeometry.FindGloballyGenerated` with a complete
Lean combination of the reciprocal-cover construction, the two-section line-bundle
construction, and the existing invertible generating-sections fibre criterion. The two
construction steps are new modules and nodes, with unchanged parent statement. This is
Stacks 09NB's route: the finite local-ring denominator argument, the open covering,
the reciprocal transition functions, and the pair of sections. It bypasses no unit step.

The main proof explicitly constructs the family indexed by `ULift (Fin 2)`, verifies
pointwise nonvanishing from the open cover, obtains its epimorphism by the existing fibre
criterion, and constructs `GeneratingSections L`. It uses existential elimination only:
no definition chooses a line bundle, functions, or sections from a sorry theorem.

All three delivered modules compile together without warnings with lcompile.py.
Searches used LeanFinder, Loogle, grep and LeanSearch; LeanSearch returned HTTP 500 and
is recorded as unavailable. No direct theorem was found. The Cech and fibre interfaces
were read in full. The Stacks source is absent from literature in this clone, so the
proof of Tag 09NB and its Tag 09N5 reference were read on the official Stacks website.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.Modules.exists_globallyGenerated_invertible_nonvanishing_eq`
(node `lem-sc-find-globally-generated`). No sorry remains in the item's module.

Added two construction holes, so this is a decomposition, not a sorry-free proof:

- `AlgebraicGeometry.exists_affine_complement_reciprocal_cover`
  (`lem-sc-affine-complement-reciprocal-cover`), in
  `Sheaf.AlgebraicGeometry.AffineComplementReciprocalCover`.
- `AlgebraicGeometry.Scheme.Modules.exists_line_bundle_sections_of_reciprocal_cover`
  (`lem-sc-reciprocal-cover-line-bundle`), in
  `Sheaf.AlgebraicGeometry.ReciprocalCoverLineBundle`.

Each new theorem has its whole proof `:= by sorry`, a complete proof in words,
a source, and a matching node. The existing
`invertible_generating_sections_fibre_criterion` is used unchanged and remains an
existing downstream hole, not a hole added by this delivery.

Edge cases: empty complement permits V empty and f = 1; an empty chart has unique
sections; the line-bundle construction works for arbitrary schemes satisfying its
explicit cover and reciprocal-function hypotheses. On projective one-space with
U the standard affine chart, f = t and g = 1/t give the standard two sections of O(1).
The line-bundle lemma does not assume global generation: that is proved in the parent.

## No longer needed

Removed the item's direct proof imports:
`Sheaf.AlgebraicGeometry.FunctionField`,
`Sheaf.AlgebraicGeometry.GlueComponentTransitionCocycle`,
`Sheaf.AlgebraicGeometry.SeparatedAffineFunctionFieldSurjective`, and
`Sheaf.RingTheory.JacobsonDenominatorFunctionField`.

The last three construction dependencies are retained in the relevant new modules,
not pruned from the proof closure. The first module's component-product definition
`Scheme.functionFieldOfComponents` is not used by this integral-scheme argument;
the existing Mathlib generic stalk supplies its function field. It may still be
reached indirectly through existing imports. No entire dependency module or existing
construction node is claimed to be pruned from the targets' closure.

The parent's former proof dependencies now occur in the new reciprocal-cover and
gluing nodes where they are needed; its immediate proof dependencies are exactly
the two new nodes and `lem-weil-pbc-invertible-generating-sections-fibre`.
Public statement imports are unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The DAG's five-step argument is correct,
but the existing Cech theorem supplies frames, not the compatible global sections
or their nonvanishing-locus calculation. The existing denominator theorem supplies
stalk elements, not their common regular representative on an open neighbourhood.
Those are the two interfaces split off here. No existing dependency states either
interface, and neither is a renaming or repackaging of the target conclusion.

The fibre criterion is used as a generic tool for the final generation check;
it preserves the unit route and replaces only the final elementary argument's Lean glue.

## New nodes

`lem-sc-affine-complement-reciprocal-cover` records steps 1--3 of Stacks 09NB:
local stalk dimensions, the separated tensor map and 09N5, then representative gluing
and the basic-open calculation. It concludes only regular functions on a covering,
without any module or generating sections.

`lem-sc-reciprocal-cover-line-bundle` records the two-chart specialization of steps
4--5: reciprocal transitions glue a line bundle, the two local section pairs glue,
and frames compute their nonvanishing. Its hypotheses contain no curve geometry,
and its conclusion contains no global-generation assertion.

No statement or definition was changed and no change record is needed.

## Second reading by U1

1. I compared the delivered item module with the repository version. The target
   declaration has the same signature byte for byte; only its proof and proof-only
   imports changed. The two added modules contain the newly split construction
   statements recorded by their nodes.

2. I compiled all three delivered modules with `lcompile.py --all`; they compile
   without errors or warnings. The item has no `sorry`; the only remaining sorries
   are the two named construction theorems, each with a matching node and complete
   proof documentation. No forbidden declaration or hollow definition was added.

3. I checked both split-off statements against the reciprocal-cover and Cech
   constructions in Stacks 09NB. They are true, strictly weaker than the parent
   conclusion, and include the edge cases of an empty complement or chart. Neither
   duplicates an existing Mathlib or library declaration.

4. The parent proof uses the shortest available route through the two construction
   interfaces and the existing fibre criterion. The removed imports are proof-only
   and are listed above; the construction modules retain the dependencies they use.

5. The parent node proof and proof dependencies match the Lean proof, and the two
   new nodes match their declarations and documented sources. The unit route remains
   realized through the reciprocal-cover, gluing, and fibre-generation steps.

I changed only this report: added this second-reading record. No Lean statements,
definitions, or proofs required repair.
