## What changed

Proved `DerivedCategory.homology_vanishes_of_localization_span` in
`Sheaf.RingTheory.HomologyVanishingLocalizationSpan`, without changing its signature.
Added proof-only imports of `Mathlib.RingTheory.Flat.Localization`,
`WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso`,
and `Mathlib.Algebra.Homology.ShortComplex.ModuleCat`.

Localization is flat, so tensoring preserves exact pairs. A private, proved
`DerivedCategory.tensorEquiv` transports this to extension of scalars at the
statement's module universes. Exact-functor homology comparison then reduces the
hypothesis to zero localized homology modules. Mathlib's elementwise localization
zero criterion proves global vanishing. The node now records these steps.
The local instance priority for `CommRing.toRing` prevents localization's separate
ring instances from being mixed; it expires at the end of the namespace and adds
no exported instance. The transparency option is scoped to this theorem.

Validation: the module compiles cleanly with lcompile.py. A scratch example after
the namespace applies the theorem to the original verbatim signature (including
all universes), checking compatibility after the local instance expires.
`#print axioms DerivedCategory.homology_vanishes_of_localization_span` reports
only `propext`, `Classical.choice`, and `Quot.sound`.
The existing caller `Sheaf.RingTheory.RingPseudoCoherentLocalizationGlue` also
compiles unchanged in a scratch overlay against the proved module.
The proof uses no positive-size assumption on r, no boundedness condition on M,
and no nonzero-ring assumption; the empty-family case is included by Mathlib's
span criterion.

## Proved and sorry left

Closed the sole hole: `DerivedCategory.homology_vanishes_of_localization_span`
(node `lem-pc-homology-vanishing-localization-span`).
No sorries remain in the item; no new holes or nodes were added.
The private tensor equivalence is fully proved.

## No longer needed

No original imports were removed: all four public imports support the existing
statement. The second reader removed the redundant added proof imports
`Mathlib.RingTheory.Localization.BaseChange` and
`Mathlib.RingTheory.LocalProperties.Submodule`; both are supplied transitively by
`Mathlib.RingTheory.Flat.Localization`. These removals prune no library module. The exploratory proof-only import
`Mathlib.Algebra.Category.ModuleCat.Descent` was replaced by the smaller
`Mathlib.RingTheory.Flat.Localization` import.

The original planned dependency `lem-weil-pbc-localization-module-exact`
(`Mathlib.Algebra.Module.LocalizedModule.Exact`, `LocalizedModule.map_exact`) is
not used by this proof. Its direct use is replaced by the existing Mathlib leaves
`lem-weil-pbc-localization-flat` and `lem-weil-pbc-flat-tensor-exact`.
The unit record has no realized step attached to this auxiliary node, so no
unit-level statement or route was bypassed. No Sheaf statement module is needed.
No claim is made that the removed dependency is unreachable from other targets.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found in the statement or the DAG's argument.
Two existing conveniences have smaller universe scope than the item:
`ModuleCat.preservesFiniteLimits_extendScalars_of_flat` and
`ModuleCat.tensorEquivExtendScalars` use module universe equal to ring universe.
The proof supplies the needed transport locally, with no interface change.
The complex homology comparison is in the existing source-library module
`WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso`, rather than the
Mathlib homology functor module alone.

The preflight classifies the added local `attribute` and namespace `open` commands
as a possible interface change. Their scope and unchanged theorem signature are
documented in `coord/changes/homology-vanishing-local-proof-commands.md`.
No other module is adapted.


## Second reading by E2

1. **Interface: pass.** Read the complete diff against the repository module.
   The sole existing declaration's signature and docstring are byte-for-byte
   unchanged. All additions are proof imports, namespace-local commands, a fully
   constructed private tensor equivalence, and the theorem proof. The existing
   change record explains the local instance priority and scoped transparency
   option; no target or public definition changes. The original signature also
   type-checks as an application outside the local instance scope.
2. **Proof: pass.** Compiled the module locally with lcompile.py, and checked the
   complete tensor-lift construction, its inverse laws, exactness transport, both
   homology comparison directions, and the localized zero criterion. There is no
   sorry, axiom, unsafe, opaque, implemented_by, extern, or hollow definition.
   Independent scratch #print axioms checks of the theorem and private helper
   use only propext, Classical.choice, and Quot.sound. The unchanged direct caller
   was checked against the delivered module in a scratch overlay.
3. **Split statements and reuse: pass.** No statements or holes were split off.
   Searched the library and Mathlib for scalar-extension exactness and tensor
   comparison under different names, including RingTensorCohomology.flatHomologyMap,
   ModuleCat.preservesFiniteLimits_extendScalars_of_flat, and
   ModuleCat.tensorEquivExtendScalars. These existing conveniences fix the module
   universe to the ring universe; they do not replace the general-universe helper.
   The helper gives explicit tensor lifts and chooses no unproved existence witness.
   Empty cover (forcing the zero ring), zero module, and localization at zero all
   satisfy the argument without an extra nonzero or boundedness assumption.
4. **Route and pruning: pass after import cleanup.** The argument uses existing
   proved flatness, tensor exactness, homology comparison and span-zero results.
   Removed the redundant added imports Localization.BaseChange and
   LocalProperties.Submodule, which Flat.Localization supplies transitively.
   ShortComplex.ModuleCat is necessary: removing it makes the exactness
   characterization unknown. The report lists the sole old dependency no longer
   used, lem-weil-pbc-localization-module-exact. Read the unit record
   dag/units/sk-thm-picard-duality.json: this auxiliary node realizes no unit step;
   no unit route is bypassed and no library module becomes unreachable here.
5. **DAG: pass.** Compared the node diff: only proof, proof_deps and proof_origin
   change. The uses union is precisely localization-flat, flat-tensor-exact and
   localized-span-eq-zero; read all three existing Mathlib leaf records and their
   declarations. The elementary steps accurately describe the constructed tensor
   equivalence and the existing canonical comparison isomorphisms. No new node
   is needed and the Lean statement recorded in the node is unchanged.

Second reading changed only two redundant proof imports and this report. It
closed no additional hole and added none: the delivery proves 1 of 1 original
holes, with 0 split off. The change record is
coord/changes/homology-vanishing-local-proof-commands.md.
