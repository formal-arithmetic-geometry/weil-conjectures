## What changed

Proved `SheafOfModules.normalized_ringIso_derived_transport` with its existing statement
and all existing data/specification definitions unchanged. The construction chooses the
native symmetric localization tensor, identifies it with the published K-flat bifunctor
by representative rigidity, and transports the monoidal structure onto that actual
bifunctor. Thus `tensor_eq` is an equality of functors, including maps.

Added proved supporting modules for prescribed tensor transport, normalized braided
localization, reflection of monoidality on tensor models, ordinary and cochain
restriction coherence, exact derived comparisons, their cocycle, and their monoidality.
The named `cochainMonoidal` definition caches exactly the existing canonical termwise
strong structure and prevents repeated expansion of its tensor-instance arguments.
No source-library module, target statement, or existing public definition was changed.

The ordinary data use the proved normalized ring-isomorphism transport. All new
existential choices are supplied by proved construction theorems; no data are selected
from an unproved arbitrary existence assertion. Identity/composition maps fix every
section. The source-library exact-derived compositor cocycle supplies associativity.
Monoidality descends from the actual canonical factorization equations using K-flat
models, with no boundedness or constructibility assumptions.

## Proved and sorry left

Closed the original hole in `SheafOfModules.normalized_ringIso_derived_transport`:
1 of 1 original sorries proved; 0 holes added; 0 split off; 0 sorries remain in the
item or any new module. Every declaration in the new modules is proved or is an
explicit construction. The combined remote compilation passed all twelve modules;
the final annotated packet is recompiled by the delivery tool and its axiom audit.

The new proved interfaces include `ringIso_published_tensor`,
`ringIso_normalized_derived_braided`, `derivedId_fac`, `derivedComp_fac`,
`ordinaryId_monoidal`, `ordinaryComp_monoidal`,
`mapCochainComplexCompIso_monoidal`, `chainId_monoidal`, `chainComp_monoidal`,
`derived_left_unit`, `derived_right_unit`, `derived_assoc`,
`derivedId_monoidal`, and `derivedComp_monoidal`.

## No longer needed

The proof does not invoke `lem-sf-ringed-derived-closed-symmetric-monoidal`:
it constructs the symmetric structure on the prescribed bifunctor from native
localization and tensor-model rigidity. Its old public import is preserved for
consumer compatibility, so its import closure is not claimed as globally pruned.
Removed its obsolete tool-use entry from the node. No module is withdrawn.

The main proof no longer directly invokes
`lem-weil-pbc-exact-functor-derived-factorization` or
`lem-weil-pbc-localization-universal-property`: the already proved Mathlib/source
exact-derived functor and comparison APIs supply these operations. Their mathematical
role is retained in the new comparison and descent nodes. The published tensor
construction continues to use `lem-weil-pbc-site-derived-tensor-descent` through
`lem-sf-cochain-tensor-model-rigidity`, so that dependency is not pruned globally.

Removed unused draft imports of the old braided-square module from the new normalized
square module and of the braided-derived helper from the monoidality helper. The
normalized square keeps the monoidal-factorization proof from the existing square
construction in its conclusion; the old module remains unchanged for all consumers.
No `lean/WeilConjectures` declaration, import, attribute, or proof was removed.

## Where the brief, the DAG or earlier work was wrong

The original mathematical plan is valid. Its literal-equality tensor clause requires
an explicit transport of constraints and tensor maps onto the published bifunctor;
a mere tensor isomorphism would not establish it. The original braided-localization
square exposes a normalization equation but discards its internal proof that the
canonical factorization is monoidal, so a proved general variant retains that proof.

Repeatedly elaborating `mapCochainComplexMonoidal` for scalar restriction expanded
large total-tensor structures. The named `cochainMonoidal` construction and general
factorization-pasting lemmas keep those structures behind their interfaces. This fixes
the expansion without increasing the compile timeout or changing any mathematics.
The ordinary and derived identity cases, arbitrary composite isomorphisms, all
integer degrees, and reassociation equality transports were checked explicitly.

## New nodes

`lem-pur-u2-prescribed-tensor`: proved supporting construction/coherence interface; its module, source, complete argument, dependencies, and three recorded search kinds are in the node.

`lem-pur-u2-normalized-braided-localization`: proved supporting construction/coherence interface; its module, source, complete argument, dependencies, and three recorded search kinds are in the node.

`lem-pur-u2-monoidal-descent`: proved supporting construction/coherence interface; its module, source, complete argument, dependencies, and three recorded search kinds are in the node.

`lem-pur-u2-published-derived-tensor`: proved supporting construction/coherence interface; its module, source, complete argument, dependencies, and three recorded search kinds are in the node.

`lem-pur-u2-normalized-braided-derived`: proved supporting construction/coherence interface; its module, source, complete argument, dependencies, and three recorded search kinds are in the node.

`lem-pur-u2-restriction-comparisons`: proved supporting construction/coherence interface; its module, source, complete argument, dependencies, and three recorded search kinds are in the node.

`lem-pur-u2-ordinary-restriction-coherence`: proved supporting construction/coherence interface; its module, source, complete argument, dependencies, and three recorded search kinds are in the node.

`lem-pur-u2-monoidal-complex-comparison`: proved supporting construction/coherence interface; its module, source, complete argument, dependencies, and three recorded search kinds are in the node.

`lem-pur-u2-chain-restriction-coherence`: proved supporting construction/coherence interface; its module, source, complete argument, dependencies, and three recorded search kinds are in the node.

`lem-pur-u2-derived-restriction-cocycle`: proved supporting construction/coherence interface; its module, source, complete argument, dependencies, and three recorded search kinds are in the node.

`lem-pur-u2-derived-restriction-monoidal`: proved supporting construction/coherence interface; its module, source, complete argument, dependencies, and three recorded search kinds are in the node.

No change record is required: all original signatures and definition bodies are unchanged; the original theorem proof and its route are the only edits to existing Lean code.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
