## What changed

Replaced the sorry in `Algebra.exists_flat_finiteType_approximation_point` by a complete
Lean reduction following the localized-system argument of Stacks Tags
[02JO](https://stacks.math.columbia.edu/tag/02JO) and
[00R6](https://stacks.math.columbia.edu/tag/00R6). Its signature is unchanged.

Constructed the localized ring and additive-group diagrams explicitly in
`Sheaf.RingTheory.LocalizedApproximationColimits`. `primeModuleMap` sends x/s to
f(x)/f(s), with proved well-definedness and additivity. `primeRingDiagram` and
`primeModuleDiagram` have proved identity and composition laws. The fraction map's
semilinearity and the localized stage square's commutativity are proved. These
constructions contain no sorry and select no arbitrary existence witness.

Split the two remaining arguments into separate modules: canonical localized
colimits with their scalar/flatness comparison, and localized transition tensor
base changes. The main proof establishes Noetherianness, local homomorphisms,
finiteness of localized modules, applies `RingTheory.exists_flat_stage`, and proves
the scalar tower needed by `Module.flat_iff_of_isLocalization` to restrict flatness
back to the original stage base.

The localized modules and their additive-group colimit live in universe `max u v`;
the ring diagrams remain in `u`. No universe or binder of the original declaration
was changed. The two base-change-to-limit clauses of hmodel are not needed.

The diagram definitions are reducible so their concrete localized object instances
are available. The main theorem locally enables
`backward.isDefEq.respectTransparency false` to identify the inferred Ore-localization
scalar structures with the module projections used in the eventual-flatness API.

## Proved and sorry left

Closed one original hole: `Algebra.exists_flat_finiteType_approximation_point`
(node `lem-pc-finite-type-approximation-flat-point`). There is no sorry in the item's
module. This is a decomposition, not a completed proof without sorry dependencies.

Added exactly two holes, both named public theorems in separate new modules:

- `Algebra.localized_approximation_colimits`, node
  `lem-pc-localized-approximation-colimits`, in
  `Sheaf.RingTheory.LocalizedApproximationColimits`.
- `Algebra.localized_approximation_baseChange`, node
  `lem-pc-localized-approximation-base-change`, in
  `Sheaf.RingTheory.LocalizedApproximationBaseChange`.

The first has no finiteness, tensor-base-change, or flatness hypothesis and asserts
no flat stage; it compares colimits and actions. The second assumes only transition
tensor isomorphisms and asserts their localization identities, with no colimit,
finiteness, flatness, or directedness hypothesis. They are strictly distinct parts
of the original argument. Each has exactly `:= by sorry`, a source and complete
proof in its docstring, and a matching node. Existing holes in imported modules
are unchanged. The declaration-level count is one closed and two added (net -1).

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.FilteredColimitLocalizationAtPrime` from the item's module;
it is still needed by the colimit comparison and is imported by the new colimit
module. Its node is consequently retained through the new child, not pruned.

The original module's other proof imports, `Sheaf.RingTheory.ColimitEventuallyFlat`
and `Sheaf.RingTheory.FlatModuleAtPrime`, are used directly. Its public statement
imports remain. Localization-tensor-product, localization-tensor-over-base, and the
module-colimit criterion are now dependencies of the two split statements rather
than direct dependencies of the parent. They are not globally unnecessary.
No original node or library module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG's localized-system route is mathematically sound, but the existing named
interfaces did not already supply the coupled canonical semilinear module-colimit
comparison or the localized transition tensor formulas. Those are the two split
steps; applying only the ring-colimit theorem does not establish either.

The local source mirror lacks `literature/stacks-project/algebra.tex` and the
blueprint unit's `_section.md`. Read the unit record's complete statement and steps
and read the Stacks sources online at Tags 02JO, 00QX, 00R6, and 037D. No unit or
chapter route is changed; this delivery keeps localization and eventual flatness.
The ancestor helper prints `None` for this module-created node; the new nodes use
its existing `blueprint.from.node = lem-pc-rf-perfect-base-change` and extend its
existing `via` chain, without changing the parent blueprint fields.

Searches: LeanFinder and Loogle found localization and flatness ingredients but no
exact shorter theorem for a supplied approximation. The similar
`exists_flat_integer_approximation_stage_at_prime` requires ULift diagrams in a
single enlarged universe, so it does not directly accept this supplied diagram.
LeanSearch returned Internal Server Error on both new statements. Mathlib/source
searches and whole-blueprint searches for 02JO and 00QX found no duplicate of either
new coupled statement. Relevant Mathlib tensor-localization APIs and fixed-ring
module-colimit APIs are recorded in their nodes.

Checked the new statements on identity transitions (tensor comparison becomes the
usual identity/cancellation equivalence), zero stage modules (all localized modules
remain zero), and zero limit rings (there is no prime q to supply). The base-change
statement is vacuous for an empty index preorder; the colimit statement preserves
the required nonempty directed indexing. Neither needs injective ring maps, domains,
nonzero modules, or finite-type hypotheses. The colimit map and module action are
determined by their equations on coprojections: filtered joint surjectivity and
passage to a common stage determine all products r • x. No definition chooses data
from a mere existence theorem, and both diagrams are independently constructed.

## New nodes

`lem-pc-localized-approximation-colimits`: localized colimit and scalar compatibility
for arbitrary supplied semilinear diagrams. It realizes step 3 of the original node,
including the canonical-colimit transport needed in its final step. Its source is
02JO's first paragraph and 037D's first proof paragraph. It uses the existing ring
localization-colimit statement and filtered element/equality criteria.

`lem-pc-localized-approximation-base-change`: the ring-localization and module-linear
base-change identities for the concrete localized transition maps. It realizes step
4 of the original node and the local-system hypotheses of 00QX (5) and (6). Its
proof follows tensor-localization compatibility and tensor cancellation. No existing
module, definition, or statement was adapted; there is no change record.

## Second reading by D3

1. Compared `FiniteTypeApproximationFlatPoint.lean` with the repository version. The target
   theorem signature is byte-for-byte unchanged; only its proof and proof-only imports differ.
   Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`. There are no forbidden
   declarations and no `sorry` in the item module; the only remaining `sorry`s are the two
   named split theorems, each with a source docstring and matching DAG node. Verdict: pass.
3. Checked the two split statements against their hypotheses and edge cases (identity and
   zero transitions, zero modules, and empty preorder where applicable). They are distinct,
   strictly smaller reductions and do not restate the parent target. Verdict: pass.
4. Checked the proofs and imports against the DAG. The parent proof uses both split nodes,
   preserves the localization and eventual-flatness route, and the unit route is unchanged;
   the removed direct localization import remains transitively used by the colimit node.
   Verdict: pass.
5. Searched the library and Mathlib-facing modules for duplicate declarations and checked the
   node `proof`, `proof_deps`, and `proof_origin` records against the Lean code. No duplicate
   or hollow definition was found. Verdict: pass.

Changed only the proof of the parent theorem, added the two explicitly documented split
Theorems and their nodes, pruned the parent proof-only localization import, and added this
second-reading record. No statement or definition was changed.
