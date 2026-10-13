## What changed

Replaced the sorry in `Module.mem_span_ideal_kernel_localized_baseChange` with a
compiling proof from two new intermediate statements. Its signature, visibility,
universes, definitions and public imports are unchanged. Added proof-only imports
of `Sheaf.RingTheory.BaseChangeIdealKernelGenerators` and
`Sheaf.RingTheory.LocalizationIdealKernelGenerators`.

The first statement concerns ordinary base change and quotient flatness, with no
localization or auxiliary S-algebra. The second concerns localization of the
ordinary multiplication kernel, with no quotient-flatness or original-kernel
hypothesis. Both prescribe their maps uniquely by pure-tensor formulas.

The parent proof uses tensor induction to identify the composite of those maps
with the given theta. An explicit span induction then transfers ordinary kernel
generators, using the scalar-tower identity to convert R'-scalars to S'-scalars.
Finally `Submodule.span_le` transfers localization kernel generators. All three
modules compile cleanly with lcompile.py. The delivery dry run prints OK; nothing
was pushed. The independent second reader still writes its own review.

## Proved and sorry left

Closed the original hole in
`Module.mem_span_ideal_kernel_localized_baseChange`
(node `lem-weil-pbc-localized-base-change-ideal-kernel-span`).

Added two holes, each the entire proof of a named public theorem:

- `Module.exists_baseChange_ideal_kernel_generators`, node
  `lem-weil-pbc-base-change-ideal-kernel-generators`.
- `Module.exists_localization_ideal_kernel_generators`, node
  `lem-weil-pbc-localization-ideal-kernel-generators`.

This is a decomposition, not a sorry-free proof: one upper hole closed and two
strictly simpler lower holes added (net holes closed minus added: -1).
There are no holes inside definitions or inside the combining proof.

The source calculations were read in Stacks Tags 00MO, 00MM and 00MN, including
00MO's second and third proof paragraphs. These do not use the local, Noetherian,
finite-module or vanishing hypotheses needed for the final flatness conclusion.
The new statements were checked at I = 0, I = R, M = 0, identity base change,
and localization containing zero; the relevant kernels then vanish or the
localization map is the identity. The linear map in the localization statement
is uniquely fixed by nested pure-tensor induction, so no arbitrary data is
chosen from a mere existence statement.

## No longer needed

No import was removed from the original module. No global pruning is claimed.
The parent no longer uses these original proof dependencies directly:

- `lem-weil-pbc-module-tensor-cancel-base-change`
- `lem-weil-pbc-tensor-over-quotient-ring`
- `lem-weil-pbc-localization-module-exact`
- `lem-weil-pbc-localization-tensor-over-base`
- `lem-weil-pbc-tor-one-surjective-flat-middle`
- `lem-weil-pbc-tor-one-surjective-change-rings`
- `lem-weil-pbc-tor-ideal-kernel-naturality`
- `def-weil-pbc-tor-modules`

They remain in the proof plans below the two new statements. In particular the Tor modules are
still needed for ordinary kernel generation, and localization/tensor-cancellation
lemmas remain needed for localization. The parent DAG now records just the two
new nodes as proof dependencies, matching the Lean proof. No blueprint unit
statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The parent node already notes a genuine interface gap:
`CategoryTheory.torOne_surjective_flat_middle` only asserts existence of an epi;
it gives no canonical-map characterization or generator formula. Its signature
also puts the rings and module in one universe, whereas the assigned theorem
has independent universes. These cannot be silently treated as canonical
surjectivity in the parent proof. The new ordinary-base-change statement isolates
that kernel-generation calculation for the next worker. The source's construction
of the canonical map, rather than an unspecified existential epi, must be used.
No existing statement or definition was changed.

Searches were run through msearch.py and recorded in searches.jsonl. LeanFinder
found flat tensor-kernel and tensor right-exactness lemmas; Loogle found
`TensorProduct.AlgebraTensorModule.ker_mapOfCompatibleSMul` and
`IsLocalizedModule.map_exact`. Mathlib source reads also found
`Submodule.localized'_eq_span`. None directly supplies either complete new
interface. Both LeanSearch requests returned Internal Server Error, recorded
as unavailable. Library searches found no duplicate of the new statements;
blueprint searches for kernel/localization and kernel/base found no matching
blueprint statement. Local copies of the literature text are absent on this
machine; the named Stacks pages were read online.

## New nodes

`lem-weil-pbc-base-change-ideal-kernel-generators` is stated in
`lean/Sheaf/RingTheory/BaseChangeIdealKernelGenerators.lean`. It isolates the
ordinary base-change part of Tag 00MO, third proof paragraph, using 00MM, 00MN,
and the ideal-kernel connecting map of 00M6. Its pure-tensor formula determines
theta; its remaining content is generation of the ordinary base-change kernel.

`lem-weil-pbc-localization-ideal-kernel-generators` is stated in
`lean/Sheaf/RingTheory/LocalizationIdealKernelGenerators.lean`. It isolates
localization exactness and tensor compatibility in Tag 00MO, second proof
paragraph, expanded by 00CS and 00DK. It does not assume ordinary kernel
surjectivity or quotient flatness and does not depend on the first new node.

There are no change records or forced adaptations.


## Second reading by J1

1. **Unchanged interfaces: pass.** Read the diff of the parent module against
   the repository. The complete existing theorem signature, universes, instance
   binders, docstring, visibility and four public imports are byte for byte
   unchanged. Only two plain proof imports and the body replace the original
   sorry. The two additional modules are new; there are no definitions, changed
   targets or forced adaptations. The existing node changes only `proof`,
   `proof_deps` and `proof_origin`.

2. **Kernel-checked combining proof: pass, with two reported open lemmas.**
   Recompiled all three modules in import order with lcompile.py after the import
   repairs, without errors or warnings. The parent has zero sorry tokens; each
   new theorem has exactly the entire named proof `by sorry`. No forbidden
   declaration or hollow definition occurs. A scratch copy of the parent with
   `#print axioms` for all three declarations compiled: the parent and ordinary
   base-change theorem use only propext, Classical.choice, Quot.sound and
   sorryAx; the localization theorem uses propext, Quot.sound and sorryAx.
   Tensor induction proves the composite formula for every k, not merely pure
   generators. R'-linearity of alpha and algebraMap_smul justify the scalar step
   of span induction. The final span_le uses precisely the localization kernel
   generators. This remains a decomposition: one closed hole and two added holes,
   net -1, not an axiom-free proof of the item.

3. **Split statements: pass.** Read both signatures, docstrings and new nodes
   against Stacks Tags [00MO](https://stacks.math.columbia.edu/tag/00MO),
   [00MM](https://stacks.math.columbia.edu/tag/00MM),
   [00MN](https://stacks.math.columbia.edu/tag/00MN) and
   [00M6](https://stacks.math.columbia.edu/tag/00M6). The first statement assumes
   only quotient flatness, makes ordinary base change with N = R' tensor M,
   and concludes R'-span generation. The second assumes compatible algebra
   maps and localization, has no quotient-flatness hypothesis, and concludes
   S'-span generation from the ordinary kernel. These are distinct strict
   parts of the parent's argument, not renamed versions of it. Pure-tensor
   formulas uniquely prescribe the additive theta and the linear alpha by one
   and two tensor inductions, respectively. No arbitrary data are chosen by a
   definition. Checked I = 0 and I = R (zero multiplication kernels), M = 0,
   zero target ring and localization containing zero (zero target module).
   Identity base change retains the original, possibly nonzero kernel and
   gives its own span. For a nonzero-kernel check, R = Z, I = (2), M = Z/2 and
   R' = Z/4 satisfy quotient flatness; the target kernel is Z/2 and the
   prescribed generator maps onto it. The localization check S = Z[t],
   M = (Z/2)[t], R' = Z and S' = Z[t,t^-1] gives the expected fractions of
   original kernel elements. These edge checks are mathematical checks, not
   additional claimed Lean proofs.

   Independently searched with msearch.py using different phrases:
   LeanFinder `ideal tensor multiplication kernel change of scalars quotient
   flat module`, Loogle `Submodule, LinearMap.ker, IsLocalization`, and grep
   `ker.*(tensor|localiz)|[Ll]ocaliz.*ker`. Read the resulting
   `LinearMap.localized'_ker_eq_ker_localizedMap` and
   `LinearMap.ker_localizedMap_eq_localized'_ker`, together with
   `Submodule.localized'_eq_span`, in Mathlib's LocalizedModule/Submodule.lean.
   They support the localization step but still require constructing the
   specified localization maps, the A-action and tensor identifications;
   none states the complete new interface. Flat kernel tensor lemmas require
   a flat tensor factor, which quotient flatness here does not imply.
   Searched the repository and upstream ring/algebra modules for kernel
   generation and scalar/base-change variants; found no duplicate. Both new
   nodes already record the three prescribed search kinds, including the
   first worker's unavailable LeanSearch requests. Closing either remaining
   hole requires substantial construction beyond a short review repair.

4. **Route and pruning: pass after import repairs.** The parent follows the
   two source calculations and combines them explicitly. Read
   dag/units/sk-thm-p1.json, including every realized statement and step;
   neither the parent nor any of its eight former direct dependencies is a
   realized node. Their mathematical steps persist below the two new nodes.
   The local blueprint _section.md text is unavailable on this machine; the
   complete unit statement and steps are recorded in the JSON that was read.
   Enumerated all eight former direct proof dependencies under No longer
   needed. They are not globally pruned. Both new imports in the parent are
   plain imports and only support its proof.

5. **Lean/DAG agreement: pass.** Matched all hypotheses and conclusions of
   both new signatures with their node statements, including the orientation
   of tensor symmetry, coefficient rings of the two spans, pure-tensor
   formulas and independent universes. The parent proof now uses exactly the
   two new nodes; its recorded tensor and span induction describes its Lean
   body. The new nodes have complete sourced proof plans with proof_deps
   equal to the union of their steps' uses, three search kinds, created and
   blueprint ancestry records, the parent's chapter and unit, and Lean
   declaration records. Their proof dependencies remain plans for the two
   explicitly open proofs, not claims of Lean applications already made.

Changes made by this reader: removed Localization.Defs and RingTheory.TensorProduct.Basic
from the new ordinary-base-change module and replaced RingHom.Flat with the narrower
Flat.Basic; its remaining TensorProduct.Quotient import supplies ideal quotient
and tensor structures used in the statement. Removed RingHom.Flat and
TensorProduct.Quotient from the new localization module, replacing their incidental
ideal-map support with the direct public import Mathlib.RingTheory.Ideal.Maps.
A compile with only TensorProduct.Basic and Localization.Defs reached a heartbeat
limit during ideal-map instance synthesis; the direct Ideal.Maps import resolves
it and compiles in about two seconds. The parent proof and all signatures were
left unchanged. Expanded the pruning report and added this independent reading.
