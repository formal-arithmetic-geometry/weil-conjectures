## What changed

Completed `AlgebraicGeometry.etale_lfp_and_finiteType_over_field` in
`lean/Sheaf/AlgebraicGeometry/EtaleLfpAndFiniteType.lean`. The proof uses only the
Mathlib instances: étale implies locally of finite presentation, and the
composition instances for quasi-compact and locally finite type morphisms. The
corresponding DAG node updates its proof route and removes the obsolete project
proof dependency.

## Proved and sorry left

Closed the sole declaration hole, `AlgebraicGeometry.etale_lfp_and_finiteType_over_field`.
No sorries remain and no holes were added.

## No longer needed

Removed the redundant direct public import
`Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: it remains publicly available
through `Etale` → `Smooth` → `FinitePresentation` → `QuasiSeparated`.
The project node `def-weil-pbc-scheme-conventions` is the entire old `proof_deps`
and is no longer a proof dependency. It is a conventions node, with no Lean module
to prune. No project modules are pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan treated the finite-type argument as depending on the project scheme
conventions node. The Lean statement already exposes exactly the needed quasi-compact and
locally finite type hypotheses, so Mathlib's typeclass composition instances close the
conclusion directly.

## Second reading by F4

1. Compared the sole delivered Lean module with the shared repository by `diff`
   and checked the theorem signature byte for byte by script: identical. It still
   quantifies over arbitrary `U`, `X`, an étale `f : U ⟶ X`, every field `K`, and
   every structure morphism `g : X ⟶ Spec K`. Its first conclusion is local finite
   presentation of `f`; its second assumes precisely quasi-compactness of `f` and
   quasi-compactness plus local finite type of `g`, and concludes both properties
   of `f ≫ g`. These are exactly the node's two clauses, using finite type =
   quasi-compact plus locally finite type. No declaration, definition, hypothesis,
   conclusion, universe, or visibility was changed. The public import removal is
   declared in `coord/changes/etale-lfp-redundant-import.md`.
2. Compiled the delivered proof through `lcompile.py` successfully, without
   warnings. A scratch copy with `#print axioms` reports exactly `propext`,
   `Classical.choice`, and `Quot.sound`. Inspected the entire file: no holes,
   forbidden constructs, new definitions, or witness choices. Both conjuncts are
   ordinary instance-based proofs, with the three explicit hypotheses installed
   locally for the composition instances.
3. No statements were split off or added, so there are no new holes, docstring
   proofs, nodes, or small-case obligations for lower lemmas. Also checked the
   original statement on identity morphisms and empty sources: the same étale and
   composition facts apply, without any hidden nonemptiness or dimension
   assumptions. Searched `lean/Sheaf` and `lean/WeilConjectures`; the only project
   declaration with this name is the item itself.
4. The proof already takes the direct Mathlib route; verified the composition
   declarations by Loogle and Mathlib grep, and the étale-to-smooth and
   smooth-to-local-finite-presentation instances by Mathlib grep. No project
   theorem is needed. Tested removing the separate `QuasiCompact` import in a
   scratch copy, which compiled, and removed that redundant direct import.
   `## No longer needed` now lists it and the sole obsolete old dependency.
   Read `dag/units/sk-prop-sf-kunneth-ordinary.json` and its blueprint section:
   both `realized.statement` and `realized.steps` are empty and the section names
   the Künneth/projection-formula nodes, not this conventions leaf. This local
   simplification preserves the unit's route.
5. Compared the DAG files as JSON: only `proof`, `proof_deps`, and `proof_origin`
   change. Empty `proof_deps` agrees with a proof using only Mathlib. Corrected the
   fictitious `etale_to_locallyOfFinitePresentation` source label to the actual
   two-instance route through `Smooth`, with file/line references, and explicitly
   included the local-finite-presentation-to-local-finite-type step needed for
   `f`. There are no new nodes to validate; all statement and unit fields agree
   with the shared version.

Second-reading changes: removed one redundant public Mathlib import, corrected
DAG proof-source details, restored readable Unicode in the node JSON, and updated
this report and the import change record. The first worker's Lean proof is kept.

Change record: `coord/changes/etale-lfp-redundant-import.md`.
