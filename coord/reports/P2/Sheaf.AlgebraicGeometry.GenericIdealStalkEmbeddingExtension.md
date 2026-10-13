## What changed

Proved `AlgebraicGeometry.Scheme.Modules.generic_ideal_stalk_embedding_extension`
in the assigned module, preserving its statement and its public imports.
Added the proof-only import of `Sheaf.AlgebraicGeometry.LocalClosedIdealMapExtension`
and the existing stalk-extension, qcqs pushforward, affine finite-type, coherence
criterion, and quasi-coherent-unit modules.

The proof first establishes coherence of the closed structure pushforward by cyclic
affine sections. It extends the prescribed stalk map on an open using the existing
`exists_open_hom_of_coherent_stalk_map`, then uses the new local denominator-clearing
theorem. Naturality of the restriction-stalk isomorphisms proves the exact prescribed
stalk equation. The rest is fully proved: the pushed ideal inclusion is injective
on stalks by Mathlib, and a map into a pushed integral ideal with zero generic stalk
is zero by injectivity of restriction of regular functions. Applied to the kernel
inclusion, this proves that the extended map is mono.

Updated the existing node's proof, proof_deps, and proof_origin to this route.
Added one new module and its node for the local denominator-clearing step.
No definitions or existing signatures changed; no forced adaptations.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.generic_ideal_stalk_embedding_extension`
(node `new-generic-ideal-stalk-embedding-extension`): 1 of 1 original sorries closed.
The item's module contains no remaining sorry. Its four private helpers are proved:
`pushforward_ideal_map_eq_zero_of_generic_stalk`,
`mono_of_pushforward_ideal_generic_injective`,
`coherent_closed_pushforward_unit`, and `stalk_map_apply_eq_restrict`.

Added one sorry:
`AlgebraicGeometry.Scheme.Modules.local_closed_ideal_map_extension`,
node `lem-pc-local-closed-ideal-map-extension`, in the new module
`Sheaf.AlgebraicGeometry.LocalClosedIdealMapExtension`.
It extends an arbitrary already-local map and asserts agreement on the given open;
it does not assume injectivity and does not assert a monomorphism. It is strictly
the denominator-clearing part of the argument, not a renamed generic embedding
statement. Its proof is exactly `:= by sorry`, with source and full proof in words.
Edge cases checked in words: zero local map, U = X, and exponent n = 0. The generic
point hypothesis excludes an empty U because an integral scheme is nonempty.

This is a decomposition (one hole closed, one hole added), not a claim that the
whole import closure is sorry-free. The existing imported
`AlgebraicGeometry.exists_open_hom_of_coherent_stalk_map` is now proved in the
repository with its existing node; it is neither changed nor re-stated. The remaining
new hole is the local ideal extension, and the target still reports `sorryAx`.
Both delivered modules compile with the launcher script; the delivery dry run
provides the final compile, axiom, signature, import-cycle, and preflight checks.

## No longer needed

No original public import was removed: they are needed by the unchanged signature.
The following original planned proof dependencies are no longer used by either
this proof or the new local extension node:

- `lem-weil-pbc-finite-pushforward-coherent` /
  `Sheaf.AlgebraicGeometry.FinitePushforwardCoherent`: replaced by the proved
  cyclic-affine closed-structure special case and the existing qcqs and finite-type
  criteria. No general finite direct image theorem is needed here.
- `lem-weil-pbc-coherent-kernel-cokernel-locnoeth` /
  `Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian`: the kernel
  argument uses no coherence of the kernel.
- `lem-weil-pbc-closed-immersion-coherent-equivalence` /
  `Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence`: no descent of the
  kernel is needed.

The development-only import `Sheaf.Algebra.Homology.ModuleStalkExact` was removed:
Mathlib's `TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective` supplies
all stalk injectivity needed. The redundant development import
`Mathlib.CategoryTheory.Abelian.Basic` was also removed.

`CoherentHomsOverOpen`, `ReducedInducedClosedSubscheme`,
`ClosedImmersionPushforwardIdealPowers`, and `IntegralIdealGenericStalk` remain
planned dependencies of the new local extension node; they are not claimed pruned.
These are route-local pruning claims, not claims that the named modules become
unreachable from every target.

## Where the brief, the DAG or earlier work was wrong

The original module did not import its planned proof-dependency modules. Moreover,
`tools/import_direction.py may` refuses importing
`Sheaf.AlgebraicGeometry.FinitePushforwardCoherent` and
`Sheaf.AlgebraicGeometry.CoherentHomsOverOpen`: both already reach the assigned
module, so each proposed import closes a library cycle. It also refuses importing
`WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion` for the same reason.
The proof therefore uses permitted existing lower interfaces for coherence and
isolates the local denominator-clearing argument in its own module. No existing
module or tool was altered to evade the cycle check. The DAG's proof-dependency
paths for those nodes do not reach this item; these cycles arise in Lean imports.
A subsequent proof of the local extension should address that import mismatch.

The planned coherent-kernel descent is unnecessary: the direct integral
restriction-injectivity argument works for any map into i_*J, even without
quasi-coherence of its source. No mathematical statement was disputed.

`tools/blueprint_refs.py ancestor` returns None for the assigned created node
because its created.item is a module name. The recorded blueprint links identify
`lem-pc-coherent-hi` through `lem-pc-r2-rank-one-generic-ideal-inclusion`; the new
node records that actual chain. Blueprint searches for generic ideal, 01YB, and
01YE found no duplicate local extension statement; the ideal-powers search found
only a flat-pullback statement, which is not this lemma. The unit's realized
statement and step lists are empty, and its route was not changed.

The local literature checkout is absent on this machine. Sources were read online
from the Stacks pages for Tags 01Y4, 01YB, and 01YE. LeanSearch returned HTTP 500;
that search is recorded as unavailable, alongside successful LeanFinder, Loogle,
and source-grep searches. No unavailable search is claimed to have found no match.

## New nodes

`lem-pc-local-closed-ideal-map-extension` records precisely the local ideal-power
extension step from Tags 01YB and 01YE. It has one public theorem in
`lean/Sheaf/AlgebraicGeometry/LocalClosedIdealMapExtension.lean`, and inherits
chapter `sec-picard-framework` and unit `sk-thm-picard-coherence`. Its proof describes
the complement ideal, ideal-power extension, affine quotient identification, and
nonzero generic stalk. Its Mathlib search records are copied from the actual
launcher search log. No change records are required.

## Second reading by P2

1. **Interfaces: PASS.** Diffed both delivered modules against the repository (the
   local extension module is new). The complete existing target signature is
   byte-for-byte identical, including every hypothesis and the prescribed stalk
   equality. Its existing docstring and public imports are unchanged. There are
   no definitions, interface changes, change records, or forced adaptations.
2. **Proof and axioms: PASS as a decomposition.** Compiled both modules in import
   order with `lcompile.py --all`, without errors or warnings. In scratch copies,
   printed axioms of the target, the new theorem, and all four private helpers.
   Each helper uses only `propext`, `Classical.choice`, and `Quot.sound`; the target
   and local extension additionally use `sorryAx`. The sole delivered sorry is
   the entire proof of the public named `local_closed_ideal_map_extension`.
   There are no forbidden declarations, hidden holes, or data constructions from
   arbitrary unproved existence witnesses. Read the sectionwise generic-vanishing
   proof, kernel cancellation, affine cyclic coherence, and both directions of
   restriction-stalk naturality; all prove their stated claims.
3. **New statement: PASS.** Independently read Stacks Tags
   [01YB](https://stacks.math.columbia.edu/tag/01YB),
   [01YE](https://stacks.math.columbia.edu/tag/01YE), and
   [01QY](https://stacks.math.columbia.edu/tag/01QY).
   Apply 01YB with coherent source `i_*O_W` and quasi-coherent target `G`.
   The complement ideal's power times `i_*O_W` is the pushed image ideal on W;
   the affine quotient calculation glues and respects its inclusion. Its stalk
   is the unit ideal at eta, hence the constructed ideal is nonzero. The displayed
   equality follows on all of U. Checked the zero map, U = X, exponent zero,
   disjoint opens away from W, and nonreduced ambient X: none invalidates this
   argument. A field closed point also reduces to extending a local cyclic map.
   This theorem isolates extension only, whereas the target separately proves
   compatibility with a prescribed stalk map and monomorphy. It is a strict
   intermediate step, not a restatement. Independent LeanFinder search for
   extension from powers of a complement ideal, Loogle search for coherence,
   and source searches found localization lemmas and the existing general
   `coherent_homs_over_open`, but no duplicate local closed-pushforward theorem.
   Read `exists_generic_ideal_extension`: it requires a generically invertible
   finite free map on an integral ambient scheme, so does not apply here.
4. **Route and pruning: PASS.** The argument starts with the target and proves
   coherence and monomorphy without new holes. The only remaining geometric step
   is the sourced local extension. General coherent-Hom and finite-pushforward
   modules cannot be imported on this route because of the reported cycles;
   moving their whole arguments into the target is not a short replacement.
   All six new proof imports support declarations used in the proof, and none
   is public. The public imports support the signatures. Compared every original
   proof dependency: three are discarded, three remain in the local extension
   plan, and stalk extension remains directly used. `## No longer needed` gives
   exactly those distinctions. The unit has `realized = {statement: [], steps:
   [[]]}`; no chapter or unit record is changed or bypassed.
5. **Nodes: PASS.** The existing node changes only `proof`, `proof_deps`, and
   `proof_origin`. Its dependency list is precisely the union of the uses in
   its new proof. The new node has its source, full argument, dependency union,
   searches, creation provenance, blueprint ancestry, chapter/unit, and matching
   verbatim Lean signature. The local extension's planned dependencies are
   recorded as future proof obligations, not claimed to be Lean imports used
   by a completed proof.

Second-reading changes: corrected the stale report saying the existing
stalk-extension theorem itself remains unproved; added this independent review
and its search evidence to the new node. The Lean proofs and signatures needed
no repair. One original hole closed and one new hole added: net zero, decomposition.
