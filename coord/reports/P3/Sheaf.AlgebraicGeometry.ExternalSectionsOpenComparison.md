## What changed

Proved `AlgebraicGeometry.Scheme.Modules.externalSectionsComponent_openComparison`
with its original signature and visibility. The proof constructs the canonical open
base-change map, establishes its image and projection equations, constructs both
k-linear section isomorphisms, and proves the square by tensor extensionality.

Added `Sheaf.AlgebraicGeometry.ExternalOpenCoefficientNormalized`, containing the
coefficient-sheaf comparison `exists_externalOpenCoefficient_normalized` as one named
remaining theorem. Its prose proof explicitly constructs the
coefficient isomorphism from the existing restriction adjunction,
`module_pullback_tensor`, and normalized composition comparisons; the section
equation composes and cancels their unit equations.
The assigned module imports this comparison only for its proof. Neither existing
public imports nor existing declarations' signatures were changed.

The source read was [Stacks 0BED](https://stacks.math.columbia.edu/tag/0BED), especially
its degree-zero cup construction and omitted canonical-map verification, together
with [0096](https://stacks.math.columbia.edu/tag/0096),
[0097](https://stacks.math.columbia.edu/tag/0097), and
[01CD](https://stacks.math.columbia.edu/tag/01CD). The isomorphisms used here are
structural comparisons of module sheaves, so no quasi-coherence or finiteness
hypotheses from the Kunneth isomorphism are used. Empty opens are retained: all
restriction and adjunction comparisons remain isomorphisms, and the image and
section calculations do not assume points or nonzero sections. Zero coefficients
and zero sections also satisfy all unit and bilinearity equations.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.externalSectionsComponent_openComparison`
(node `lem-sc-external-sections-open-comparison`).

Split off one smaller hole:
`AlgebraicGeometry.Scheme.Modules.exists_externalOpenCoefficient_normalized`
(node `lem-sc-external-open-coefficient-normalized`), in its own new module, with
proof exactly `by sorry` and a complete construction and normalization argument
in its docstring. There are no holes in the assigned module. Its two private helpers
`scalarMap_openImage` and `scalarRestrictIso` are proved. This is a decomposition:
one original hole closed, one smaller coefficient-comparison hole added, net zero
holes. Existing mathematical dependencies are retained in that remaining node.
No unproved existence theorem is used to define data: the assigned proof eliminates
the coefficient lemma inside a theorem proof, and constructs the scalar section
isomorphisms directly.

## No longer needed

The original direct proof dependencies
`def-weil-pbc-composite-adjunction`,
`lem-weil-pbc-conjugate-iso-unit-equation`, and
`lem-weil-pbc-module-pullback-tensor` are no longer direct dependencies of the
assigned node: they are moved to
`lem-sc-external-open-coefficient-normalized`. They are not pruned from the
argument or the targets' import closure. None of the mathematical dependencies
in the original plan is pruned: its
restriction, tensor and composition/unit comparisons are used in the remaining
coefficient lemma. The assigned node now cites that lemma for those steps.
No pre-existing import was removed, and no pre-existing node or module is claimed
unreachable from the targets. There are no unused proof imports in the delivered
modules.

## Where the brief, the DAG or earlier work was wrong

The original assigned module imported only its statement dependency, despite its
DAG listing several proof dependencies. The final reduction isolates the coefficient-level assembly of those comparisons
in the new remaining theorem; there is no mathematical statement correction.

LeanSearch was unavailable (Internal Server Error). LeanFinder returned restriction
unit/section comparisons; Loogle returned `restrictAppIso` and its scalar/restriction
laws. Grep found the existing normalized composition comparison in
`EtaleTensorSections` and the tensor-section comparison in `ModulePullbackTensor`;
no assembled coefficient comparison was found. Their signatures were read,
including the pure-section normalization in `module_pullback_tensor`.

I also attempted the coefficient proof: the explicit isomorphism construction and
several unit-equation helpers compiled, but combining the factor equations led to
kernel/elaboration timeouts from reductions through tensor localization and
pullback scheme objects. The final delivery retains the compiling reduction and
leaves the coefficient step as the single named remaining theorem. The scratchpad
contains the attempt for the next worker; it is not part of the delivery.

## New nodes

`lem-sc-external-open-coefficient-normalized` records the remaining coefficient-sheaf
isomorphism and its section equation. It is strictly a structural part of the
original argument: its conclusion is an isomorphism of coefficient sheaves and
an equation on pure section products; it supplies neither source tensor-module
isomorphism nor the final equality of linear maps. The assigned proof constructs
those and combines the result by tensor extensionality. Its source, proof steps,
searches and exact Lean signature are recorded in
`dag/nodes/sec-abelian-varieties/lem-sc-external-open-coefficient-normalized.json`.
The existing node's proof dependencies and proof origin were updated accordingly.
The unit route is retained; no unit statement or realized step was bypassed.
No change record is required: existing interfaces and mathematical statements are
unchanged.

## Second reading by P3

1. Compared both delivered modules with the repository. The only existing
   module changed is `ExternalSectionsOpenComparison`; its theorem signature
   was checked byte for byte by extracting the text before `:=`. Its docstring,
   visibility, variables, and public import are unchanged. The added imports are
   proof-only. The new coefficient module introduces no changes to existing
   definitions or statements. No change record is needed. Verdict: pass.
2. Inspected both entire files for forbidden declarations and hollow definitions.
   The sole delivered `sorry` is exactly the named coefficient theorem reported
   above. The private scalar isomorphism constructs its data from the proved
   restriction section isomorphism. The existential coefficient witness is
   eliminated inside a theorem proof, never used to define data. Both delivered modules compiled locally with no errors or warnings. The
   scratch-copy `#print axioms` probe for the assigned theorem and the remaining
   coefficient theorem printed only `propext`, `Classical.choice`, `Quot.sound`,
   and `sorryAx`, as expected from the named remaining hole. Verdict: pass.
3. Read the new theorem, its complete prose construction, and its node. The
   projection equations allow precisely the composition comparisons claimed;
   the inverse open-restriction comparison cancels the second-factor unit. For
   the empty open both source schemes of the open restriction are empty and the
   same adjunction isomorphisms apply. For zero coefficients or zero sections,
   the linear maps and tensor-section equations give zero on both sides. The
   statement is a coefficient-sheaf comparison; it supplies neither scalar
   source section isomorphism nor the final square of linear maps. Thus it is
   a real intermediate reduction, not a renaming of the assigned statement.
   Fresh LeanFinder search for “open immersion base change external product
   module sheaf normalized tensor sections” found presheaf tensor operations;
   Loogle found `Adjunction.unit_leftAdjointUniq_hom_app`. Searched upstream and
   Sheaf with restriction/composition/unit terminology and read
   `ModulePullbackTensor` and `EtaleTensorSections`; no assembled comparison
   duplicates the new theorem. The remaining normalization assembly is not a
   few-minute proof, as the prior scratch attempts also demonstrate. Verdict: pass.
4. Read the top-level proof downward: canonical base-change map, image and
   projection identities, scalar restriction isomorphisms, then tensor
   extensionality. Both added imports support this proof; the new module's one
   public import supplies its signature. No shorter existing assembled theorem
   was found. Checked `sk-prop-av-cube.json`: its realized fields are unchanged,
   and no unit step is bypassed. Corrected “No longer needed” to explicitly list
   the three old direct dependencies transferred to the coefficient node;
   there are no pruned modules or closure dependencies. Verdict: pass.
5. Compared the old node and its delivered version: only `proof`, `proof_deps`,
   and `proof_origin` change. The uses union equals `proof_deps`. The new node
   records the exact Lean statement, source, construction, searches, status,
   creation data, chapter, unit and blueprint ancestry. Its unit-normalization
   route matches the docstring. Verdict: pass.

Second reading changes: clarified the transferred direct dependencies and added
this review. No mathematical or Lean proof changes were necessary. This remains
one hole closed and one split off, net zero, a decomposition rather than a
complete proof.

Source spot-check: [Stacks 01CD](https://stacks.math.columbia.edu/tag/01CD)
confirms the functorial tensor-pullback isomorphism for all ringed-space modules;
[Stacks 0BED](https://stacks.math.columbia.edu/tag/0BED) describes the canonical
cup construction. This delivery uses that structural compatibility, without
claiming the full Kunneth isomorphism without its extra hypotheses.
