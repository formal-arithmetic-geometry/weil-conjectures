## What changed

Replaced the single sorry in `GaloisCover.exists_finiteEtale_extension_noetherian` by
Noetherian induction on strict enlargement of opens, followed by composition with the
whole-base open isomorphism and pullback-square pasting. Its signature and docstring
are unchanged. Added two proof-only imports and two intermediate statement modules.
Updated the parent node to match this proof. No definitions or existing statements changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.GaloisCover.exists_finiteEtale_extension_noetherian`
(node `lem-sbc-noetherian-finite-etale-extension`) by a complete Lean reduction.
There are no sorries left in the assigned module.

Added two holes, each the entire proof of its own public theorem:

- `AlgebraicGeometry.Scheme.GaloisCover.exists_generic_open_finiteEtale_model`,
  node `lem-sbc-generic-open-finite-etale-model`.
- `AlgebraicGeometry.Scheme.GaloisCover.exists_larger_open_finiteEtale_model`,
  node `lem-sbc-enlarge-open-finite-etale-model`.

This is a decomposition (one upper hole closed, two strictly smaller holes added),
not a sorry-free proof of the mathematical extension theorem. The first step does not
require normality, a section, connected fibres, or invertible group order. The second
starts with an actual model over a proper generic open and supplies a strictly larger
one. Their combination uses the Noetherian topology essentially.

## No longer needed

None: the original module had no proof-dependency imports or nodes. The unit's trait,
purity, depth-two and completion argument remains in the enlargement theorem's proof.
No module is claimed pruned. The new generic-open module omits the geometrically
connected import because its statement does not require connectedness.

## Where the brief, the DAG or earlier work was wrong

The original node has three non-elementary steps with empty `uses` and `proof_deps`;
there are no stated trait/depth-two inputs in its plan to import. The prior sandbox
attempt was an unchanged copy, with searches but no proof. The delivery now supplies
the missing intermediate interfaces rather than applying the parent theorem under a
new name. Existing `UnderlyingFiniteEtaleExtension` depends on this item, so importing
it as a shortcut would be circular.

Read Stacks 0EYJ, 0BQM, 0BQ5 and 0EY3. Corrected the initial draft's source citation:
0BQM is generic full faithfulness, not finite-presentation limit descent; the seed
instead cites 01ZM, 01ZO and 07RP. Searches with LeanFinder returned ring-level étale
locus and descent lemmas, Loogle found no GaloisCover theorem, and local grep found
no initial-open or strict-enlargement result. LeanSearch returned Internal Server Error.
Reviewed the existing function-field limit and finite-presentation descent interfaces;
they can support the seed's future proof, but do not directly supply its conclusion.

Edge cases: an integral base is nonempty; the seed includes the generic point and
therefore never chooses the empty open. For a field base the seed open is necessarily
all of S and the induction takes its isomorphism branch. The enlargement assumption
U != top excludes that case. The trivial group, empty family (in the seed), and
nonconnected total space of a torsor cause no change to these conclusions. In the
main theorem the section prevents empty fibres. A smooth geometrically connected
fibre is geometrically integral, which is what the enlargement argument uses.
No data is defined by choosing an arbitrary witness from an unproved existence theorem:
the proof eliminates existential models inside a proposition only.

## New nodes

`lem-sbc-generic-open-finite-etale-model` is the initial spreading subargument, in
`lean/Sheaf/AlgebraicGeometry/Morphisms/GenericOpenFiniteEtaleModel.lean`. It supplies a
model only over some generic open, and therefore cannot replace the parent conclusion.

`lem-sbc-enlarge-open-finite-etale-model` is the local extension and spreading subargument,
in `lean/Sheaf/AlgebraicGeometry/Morphisms/EnlargeOpenFiniteEtaleModel.lean`. Its proof
keeps the trait and higher-dimensional depth-two cases and the disconnected-cover
reduction. It supplies one strict enlargement, while the parent proves that the
process reaches the whole base by Noetherian induction. Both inherit the parent's
chapter and unit. No change records are needed.


## Second reading by M2

1. **Unchanged interface: pass.** Read and diffed the original module against the
   delivery. The complete existing theorem signature is byte-identical, including
   normal stalks, qcqs smooth geometrically connected family, section, invertible
   group order, generic pullback, and rational lift. Its docstring is unchanged.
   Only its proof and two plain proof imports changed. There are no definitions or
   change records. The new modules declare exactly the signatures recorded in their
   new nodes; they are absent from the repository.
2. **Lean proof: pass as a decomposition.** Compiled all three modules in import
   order through lcompile.py (2.3--2.7 seconds each, no warnings or errors). Read the
   reverse-order induction: the hypothesis for V is available precisely because
   U < V; at top, the open inclusion is an isomorphism and vertical pullback pasting
   gives the original square. The assigned module has no sorry. The only two sorries
   delivered are the whole proofs of the two named new theorems listed above. A scratch
   copy with #print axioms for all three declarations reports only propext,
   Classical.choice, Quot.sound, and sorryAx (subsets of these for the split lemmas).
   No axiom/unsafe/opaque/extern/implemented_by or hollow definition occurs. Existential
   models are eliminated within a Prop proof, never used to define arbitrary data.
3. **Split statements: pass.** Read Stacks 0EYJ and 0BQM, and the seed's 01ZM, 01ZO,
   07RP. The seed uses only finite-presentation limit descent and eventual finiteness
   and etaleness over a generic neighbourhood, so its lack of normality, section and
   order assumptions is valid. The enlargement is the local claim of 0EYJ plus its
   spreading, with the action recovered by normal generic full faithfulness; connected
   smooth fibres are geometrically integral. A finite etale model cannot have extra
   components invisible generically: each component has open image in the integral
   family and therefore meets the generic fibre. Its image is clopen and contains the
   generic point, giving surjectivity. The disconnected torsor case follows componentwise
   with stabilizers and the split section fibre. Tested a field base (seed is top,
   enlargement hypothesis impossible), a trait (the only generic proper open is the
   generic point), trivial G, empty C in the seed, and disconnected torsors. In the
   formal computation, relative dimension zero needs no 0EY9: V = V0 already;
   positive dimension uses its stated d >= 1 hypothesis. Neither lemma simply renames
   the parent: one supplies a seed, the other one strict enlargement, and the Lean
   parent supplies the Noetherian termination argument. Independent LeanFinder search
   for descent from the function field to a dense open returned etale-locus and
   composition facts, Loogle search for Etale and IsFinite returned ring-level splitting
   results, and grep for finite-etale descent/spreading and punctured covers found no
   replacement. Read the nearby NoetherianSpreadingData, GenericFibreHomExtension,
   GenericFibreActionExtension and UnderlyingFiniteEtaleExtension; none closes either
   new hole in a few minutes. The latter imports the assigned module and cannot be
   used as a shortcut. The new holes remain explicitly open.
4. **Route and pruning: pass.** Read dag/units/sk-prop-input-spreading.json. Its realized
   lists are currently empty; this delivery changes none of them. The trait, section,
   depth-two completion, and local spreading route of its Noetherian steps is retained
   in the enlargement lemma, with maximality expressed as well-founded induction.
   The old parent proof_deps is empty, so the report's No longer needed list is complete.
   Both new plain imports are directly used. Public imports provide the signature's
   notions; the seed correctly omits geometric connectedness. No pruning is claimed.
5. **Nodes: pass.** The parent changes exactly proof, proof_deps and proof_origin.
   Its dependency list is exactly the two lemmas applied by the Lean proof, and its
   top-isomorphism/pasting step matches the code. Both new nodes have the same chapter
   and unit, source, search records, creation and blueprint ancestry, and verbatim Lean
   signatures. Their currently sorry proofs use no Lean dependency declarations.

Second reading changed only this report, adding the independent checks and the
relative-dimension-zero clarification. No Lean repair was needed. This closes one
upper hole and adds two lower holes: net holes closed minus added is -1, a decomposition,
with zero modules pruned, not a completed axiom-free extension theorem.
