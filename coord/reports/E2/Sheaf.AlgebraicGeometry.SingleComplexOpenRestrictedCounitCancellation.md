## What changed

Repaired Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictedCounitCancellation.
The public theorem singleComplexOpen_restricted_counit_cancellation has exactly the
original signature and imports. Its proof uses
open_pinned_counit_homotopy_restriction, categorical isomorphism cancellation,
naturality of mapDerivedCategoryFactorsh, and functoriality. Two fully proved
private categorical lemmas perform cancellation and remove the mapped identity;
congruence and transitivity combine these steps without a broad concrete rewrite.

Local reducibility controls keep derived and homotopy functor constructions abstract
while exposing only category aliases for implicit unification. Profiling traced
slow definitional comparisons through mapHomotopyCategory to componentwise sheaf
restriction. The repaired complete proof first compiled in 45.8 seconds; clean
compilation with artifacts took 51.0 seconds, and the original direct importer
compiled against the repaired artifact in 28.5 seconds. Both checks emitted no warnings.

Change record:
coord/changes/single-complex-open-restricted-counit-local-reducibility.md.
The existing node's proof and proof_origin now describe the implemented calculation;
proof_deps remains lem-pc-open-pinned-counit-homotopy-restriction.

## Proved and sorry left

Closed the sole original hole:
AlgebraicGeometry.singleComplexOpen_restricted_counit_cancellation
(lem-pc-k3-open-restricted-counit-cancellation).
Both private helpers remove_mapped_identity and cancel_restriction_counit are proved.
No sorry remains in the item, no new sorry is added, and no statement is split off.
The existing imported compatibility theorem remains the intended proof dependency;
its upstream proof closure is not claimed closed by this delivery.

## No longer needed

None. All existing public imports are required by the preserved statement;
OpenPinnedCounitHomotopyRestriction supplies the compatibility theorem actually used.
The proof follows the node's route and prunes no node or module. No extra proof
imports or new modules are added.

## Where the brief, the DAG or earlier work was wrong

The returned sandbox contained a proof but no report or node updates. Its broad
concrete simplification unfolded homotopy restriction data and could not meet the
60-second file limit. Local definition reducibility and an explicitly instantiated
categorical identity calculation repair this without changing the public interface.

The second return message names the item as its own importer. Source inspection
and tools/downstream.py show the real sole direct importer is
Sheaf.AlgebraicGeometry.SingleComplexOpenPullbackCounitHomotopyFactorization.
The original importer is compiled against the repaired sandbox artifact. All original
public imports, signature binders, universes, and visibility are preserved, so no
forced importer adaptation is necessary or included. No definition data or target
meaning is changed.

## Second reading by E2

1. Compared the entire delivered module with the repository using diff and separately
   compared the public theorem signature byte for byte: identical. Universes,
   instance binders, the unused F₀/a lets, conclusion, visibility, docstring and
   public imports are preserved. Only proof code, private proved helpers, local
   reducibility attributes and elaboration options are added. The change record
   explains the timeout repair; no definition or statement is changed.
2. Read both helpers and the complete proof. The cancellation helper derives
   k.inv ≫ s ≫ e ≫ b = d ≫ t.inv from hc by inverse identities, then uses hn
   to replace v ≫ z by b ≫ q. The identity helper is map_id and comp_id.
   The public proof instantiates these with the actual compatibility equation
   and naturality at the homotopy counit, removes the final mapped identity,
   and combines Qh images by map_comp. The delivered file compiled locally
   without errors or warnings in 44.4 seconds. No sorry, axiom, unsafe, opaque,
   implemented_by or extern occurs in it; no definition is added.
3. No split-off statement, new node, or added hole exists. The two private
   helpers are proved categorical calculations, not renamed open statements.
   Their equations require only isomorphisms and naturality, and apply to
   identity isomorphisms, zero objects and empty opens without extra assumptions.
4. Read OpenPinnedCounitHomotopyRestriction and the constructed
   singleComplexRestrictedCoefficient. The dependency gives exactly hc for
   P = F_h(I), with the additive family selected in the original statement;
   naturality gives exactly hn. Searched local restriction/counit declarations
   and Mathlib's Iso cancellation lemmas: the short generic helper packages
   those inverse identities without unfolding concrete sheaf constructions.
   Each public import supplies names in the preserved statement; the compatibility
   import is proof-only already. The sole old proof dependency is still used,
   so “No longer needed: None” is complete. Read the unit record
   sk-thm-picard-semicon: its realized lists are empty, and neither the unit route
   nor its records change. No route is bypassed.
5. Diffed the node: only proof and proof_origin change, accurately describing
   cancellation, naturality and the mapped-identity calculation. proof_deps stays
   exactly lem-pc-open-pinned-counit-homotopy-restriction, matching the theorem used.
   No new-node field requirements apply.

Second reading changed no Lean code or node: the repair is correct as written.
Added this independent review and verification evidence to the report.

A scratch copy with explicit `#print axioms` compiled in 42.4 seconds:
`singleComplexOpen_restricted_counit_cancellation` uses exactly `propext`,
`Classical.choice`, `Quot.sound`; `remove_mapped_identity` uses no axioms;
`cancel_restriction_counit` uses only `Quot.sound`. In particular, this theorem's
entire proof closure contains no `sorryAx` in the currently compiled library.
