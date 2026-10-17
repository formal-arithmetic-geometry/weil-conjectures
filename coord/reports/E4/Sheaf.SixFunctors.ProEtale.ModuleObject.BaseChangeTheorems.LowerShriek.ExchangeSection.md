## What changed

The existing section theorem is proved by inverting its original exchange component. A proof-only
`import all Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono`
reuses the proved private `boundedCartesianCounit` helper and the already available
`openUnitIsIso` helper. Fully faithfulness passes the latter unit isomorphism through the derived
and bounded-constructible restrictions. After rewriting the given exchange formula, every
component factor is invertible. The inverse satisfies the required section equation.

The first worker's new `ExchangeIso.lean` and new node
`stage3-sfb-open-base-change-component-iso` were removed before delivery. They have never landed.
No existing signature, definition body, visibility, docstring, or public import changes.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChange_app_section`.
Added zero holes; zero split-off statements remain. This closes the item's one hole, rather than
merely decomposing it. Its existing imported dependencies still contain open statements:
`#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
There is no `sorry` in the delivered module and no new definition or witness chosen from an
unproved existence theorem.

## No longer needed

Removed the direct proof-only import
`WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale`. Its geometric result is still used
transitively by the proved support helper in `ExchangeMono`; no library module is pruned from the
import closure. The old immediate proof dependency
`lem-weil-pbc-coefficient-site-weakly-etale-base-change` is replaced by
`stage3-sfb-open-base-change-component-mono` (specifically its proved support/counit helper) and
`lem-weil-pbc-condensed-open-closed-recollement` (its proved module unit helper).

The provisional `ExchangeIso` import, module, and node are absent from the final delivery.
A separate explicit recollement import was tested and removed as redundant: `import all` of
`ExchangeMono` already makes the needed helper available. No other imports were removed.

## Where the brief, the DAG or earlier work was wrong

The first worker shifted the whole geometric problem into a stronger component-isomorphism
sorry. That was not a strictly simpler part of the argument and was not acceptable progress.
Moreover, the current library already proves the required support/counit and unit facts inside
`ExchangeMono`; these suffice without a new exchange-compatibility theorem. The original section
statement is unchanged. Its node now describes the actual proof instead of retaining the
first worker's unused geometric proof step and inconsistent proof-dependency union.

## Second reading by E4

1. Compared the delivered module with the repository using `diff -u`. The existing theorem's
   signature and all context binders are byte for byte unchanged. The only Lean changes are one
   proof-only import replacement and the theorem proof. No existing data, target, public import,
   visibility, or other module is changed. No change record is needed.
2. Compiled the repaired module through `lcompile.py`. A scratch copy with `#print axioms` also
   compiles and reports only `propext`, `Classical.choice`, `Quot.sound`, and inherited `sorryAx`.
   No delivered `sorry`, axiom, unsafe/opaque declaration, foreign implementation, or hollow
   definition remains. The proof constructs the section from the inverse of a proved isomorphism.
3. Rejected and removed the new stronger isomorphism hole, its module, and its node. There are no
   new statements or split-off statements to validate. Independent source searches found the
   existing `boundedCartesianCounit` and `openUnitIsIso` proofs; a fresh Loogle search confirmed
   `CategoryTheory.IsIso.inv_hom_id`. Identity squares, empty opens, and zero objects require no
   extra assumption: the same unit/support-counit proof applies to them.
4. Read the complete `ExchangeMono` support proof, the recollement unit proof, ordinary abelian
   extension-by-zero base change, and the unit record and source. Reusing these proved helpers
   closes the hole along the original unit--square--counit route. Imports are minimal by a
   scratch compile after removing the separate recollement import. The unit record's existing
   `realized.statement` and `realized.steps` entries are empty and are left unchanged; no unit
   statement or step is bypassed. The previous immediate dependency and removed import are
   fully accounted for above; no whole library module is pruned.
5. Updated only `proof`, `proof_deps`, and `proof_origin` of the existing section node. The
   dependency set is exactly the union of its proof steps' `uses`. It records reuse of the
   private helper in the component-mono module, rather than pretending to derive a section
   from the monicity conclusion alone. There are no new nodes in the final delivery.

Second-reading changes: removed the unsupported stronger split; wrote the actual proof from
existing unit and support/counit isomorphisms; minimized the import; repaired the node's route;
and replaced the inaccurate decomposition report with the final hole counts and checks.
