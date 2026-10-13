## What changed

Repaired the duplicate-statement return by removing
`exists_etaleIdealKernelPresentationCore` and its node. The assigned theorem now combines
`exists_etaleIdealKernelIsoPair` (tensor identifications and inclusion compatibility) with
`exists_etaleNestedIdealKernel` (the kernel calculation wholly within additive sheaves).
These are genuinely separate parts of the affine-and-gluing argument, not a renamed copy
of the assigned theorem. Both modules are proof-only imports of the assigned module.
Its existing signature, visibility, and public imports are unchanged.

The combining proof cancels the monomorphic kernel inclusion to identify the tensor
inclusion with the nested-kernel inclusion precomposed by the tensor isomorphism for J.
It proves the required zero composite and transports the limiting fork using Mathlib's
`IsKernel.isoKernel`. All three delivered modules compile with `lcompile.py`.
Unchanged dependency copies were removed from the sandbox delivery.
The independent second reading below reviews this repaired reduction. It also closes
the nested additive kernel theorem by a shorter categorical argument.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.exists_etaleIdealKernelPresentation`.
This is a decomposition, not a complete geometric proof: one hole is added.
The second reader also proves the new declaration
`AlgebraicGeometry.Scheme.exists_etaleNestedIdealKernel` without `sorryAx`.
Net holes closed minus holes added in this delivery: 1 - 1 = 0.

- `AlgebraicGeometry.Scheme.exists_etaleIdealKernelIsoPair`, node
  `lem-sc-etale-ideal-kernel-iso`, is left `:= by sorry`.
The proved nested-kernel declaration has node `lem-sc-etale-nested-ideal-kernel`;
it is no longer a hole.

No other holes are added; none remain in the assigned module. No definition has a hole.
The two statements were checked on I=J, J=0 and empty objects: the compatible maps
respect identity and zero ideals, and the nested kernel fork has the expected vertex.

## No longer needed

Removed the rejected new node `lem-sc-etale-ideal-kernel-presentation-core` and declaration
`exists_etaleIdealKernelPresentationCore`. They were never part of the landed library.
The module path `Sheaf.AlgebraicGeometry.Curve.EtaleIdealKernelIso` is reused for a genuinely
smaller tensor-identification statement, so that module remains needed.
No existing dependency modules are pruned from the target closure. The assigned module's
public imports remain unchanged because its statement uses their declarations.
The nested-kernel module publicly imports only `EtaleAdditiveStructureSheaf`; its
closed-subscheme inclusion proof privately imports `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`.
The assigned node no longer directly uses these old proof-dependency nodes:
`def-sbc-ideal-sheaf-powers`, `def-pc-module-pullback`,
`def-sc-etale-additive-structure-restriction`, and
`lem-sc-etale-tensor-sections-right-exact`. Its proof dependencies are the two new nodes.
Those old ingredients remain needed through the statements and tensor-comparison plan;
none of their modules is pruned from the import closure.

## Where the brief, the DAG or earlier work was wrong

The returned core theorem was exactly the assigned theorem with another name. The previous
wrapper and its second-reading claim of a strict reduction were wrong. Importing the
existing presentation theorem to prove its own statement would create a circular proof.
The repaired delivery instead splits its actual argument into tensor comparison and the
nested additive kernel calculation, with a nontrivial complete Lean proof combining them.
No True conjunct or other repackaging artifact remains. The unit route is kept: both
geometric steps follow the original affine identification and gluing argument.

## New nodes

`lem-sc-etale-ideal-kernel-iso` in
`lean/Sheaf/AlgebraicGeometry/Curve/EtaleIdealKernelIso.lean` states only the tensor ideal
isomorphisms and their compatibility with inclusion. It does not assert the limiting fork.

`lem-sc-etale-nested-ideal-kernel` in
`lean/Sheaf/AlgebraicGeometry/Curve/EtaleNestedIdealKernel.lean` states the nested-kernel
calculation in additive sheaves. It mentions no tensor-sections functor or tensor
isomorphism. Each has its source, complete proof in words, searches, and matching node.

## Second reading by E4

1. Compared the existing module with the repository using `diff -u`: only two plain
   proof imports and the theorem body change. The existing signature, docstring,
   visibility, definitions, and public imports are byte-for-byte unchanged. The other
   two delivered modules are new. No target statement or data definition changes.
2. Compiled all three modules in dependency order using `lcompile.py --all`. The
   assigned theorem has no direct hole; its axiom closure still includes `sorryAx`
   from the tensor-identification theorem. The nested-kernel theorem is now fully
   proved using only standard axioms. Explicit `#print axioms` scratch copies confirm the nested theorem uses only
   `propext`, `Classical.choice`, and `Quot.sound`; the tensor comparison uses
   `sorryAx`, and the assigned theorem uses those standard axioms plus `sorryAx`.
   The only direct remaining hole is `exists_etaleIdealKernelIsoPair`. No forbidden declaration or hollow definition.
3. Read both split statements and their proof docstrings. The tensor comparison
   supplies compatible identifications but no limiting fork; the nested-kernel
   theorem contains no tensor construction. Neither restates the assigned item.
   Checked I=J, J=0, I=top, and the empty scheme: the inclusion and kernel directions
   agree with the quotient maps. Independently searched with leanfinder (nested
   kernels of composites), loogle (`kernel.lift, IsLimit`, unresolved identifier),
   msearch grep and direct rg in both library roots and Mathlib. Generic kernel
   lemmas do not provide the remaining tensor-sheaf comparison. Existing affine
   ideal/tensor lemmas supply ingredients but not the global compatible isomorphisms.
4. Replaced the nested theorem's affine-and-gluing hole with a proof from the
   closed-subscheme inclusion and kernel universal properties. Its imports are
   limited to the additive structure sheaf for the statement and a plain Mathlib
   subscheme import for the proof. The assigned module uses both new imports, and
   its public imports supply its signature. All four old direct proof dependencies
   are accounted for above. Read `dag/units/sk-prop-h2.json`: its realized arrays
   are unchanged; the reduction retains the ideal/tensor step supporting Brauer
   vanishing and bypasses no unit. The referenced literature files are absent on
   this machine; the source argument is preserved in the repository node's proof.
5. Compared the DAG records with all three Lean signatures, checked the new-node
   fields and that proof_deps is the union of the steps' uses. The assigned node
   records exactly the two sublemmas and categorical transport used by its proof.
   Updated the nested node and docstring to the actual categorical proof; its
   signature and statement remain unchanged.

Second reading changed: closed `exists_etaleNestedIdealKernel`, added its proof-only
Mathlib import, updated its proof docstring and DAG proof/origin, corrected hole
accounting and the full list of old direct proof dependencies, and replaced the
superseded second-reading claim with this review. The tensor comparison remains
one named, documented hole; the original one-hole item is reduced to one smaller hole.
