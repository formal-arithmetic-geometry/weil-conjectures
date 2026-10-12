## What changed

Proved `AlgebraicGeometry.Scheme.Modules.affine_module_correspondence` from the
existing scalar-restriction and qcqs-pushforward declarations and two new, strictly
smaller tensor lemmas. The original statement, universes, and public imports are unchanged.
A proved private categorical helper lifts the functors and component isomorphisms to the
full quasi-coherent subcategories, applies `CategoryTheory.Equivalence.mk`, and supplies
the two inclusion comparisons by reflexivity. The main proof explicitly chooses all
construction witnesses, applies the invertibility lemma, and combines the results.

The source read was Stacks Morphisms, Lemma 01SB, label
`lemma-affine-equivalence-modules`, including its elucidation and omitted algebra calculation
(local read-only copy `/home/ubuntu/c1-stacks-review/morphisms.tex`, lines 1895–1970).
The item's unit is `sk-thm-p1`; this auxiliary node is not itself a realized unit step.
Its construction, affine calculation, and final equivalence route are retained.

Searches used LeanFinder, Loogle, Mathlib grep, and repository rg. LeanSearch returned
HTTP 500 and is recorded as unavailable. No existing affine module equivalence was found.
Mathlib's `Algebra.IsPushout.cancelBaseChange` is useful algebraic infrastructure but
supplies neither the sheaf-level tensor functors nor the comparisons on canonical units.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Modules.affine_module_correspondence`
(node `lem-weil-pbc-affine-module-correspondence`). No sorry remains in the item's module.
The private helper `equivalence_on_full_subcategories` is proved without sorry.

Added holes, each the entire proof of one public theorem in its own new module:

- `AlgebraicGeometry.Scheme.Modules.affine_module_tensor_construction`
  (`lem-weil-pbc-affine-module-tensor-construction`,
  `Sheaf.AlgebraicGeometry.AffineModuleTensorConstruction`): construct the tensor algebra,
  functors, and maps with their formulas; no invertibility or equivalence is asserted.
- `AlgebraicGeometry.Scheme.Modules.affine_module_tensor_comparison_isIso`
  (`lem-weil-pbc-affine-module-tensor-comparison-isIso`,
  `Sheaf.AlgebraicGeometry.AffineModuleTensorComparisonIsIso`): for given construction data,
  prove the two canonical comparisons invertible; no construction or equivalence is asserted.

This is a decomposition: one original hole closed, two smaller holes added (net −1),
not a proof free of remaining dependencies. Each new theorem has a complete prose proof.

Edge cases checked mathematically: empty schemes give trivial module categories and the
same constructions; the zero module gives zero tensors and the unique comparison; for an
identity morphism both changes of rings reduce to the identity. No nonzero-ring, finite
presentation, quasi-compactness of the base, or nonempty-cover assumption was introduced.
In the comparison lemma the hypotheses pin κ on units, γ on every tensor-unit section,
and α/β by their adjunction equations; these exclude arbitrary comparison automorphisms.

## No longer needed

Removed direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.AffinePushforwardBaseChange`: the stronger base-change theorem
  and node `lem-weil-pbc-affine-pushforward-base-change` are unnecessary for this argument.
  The proved `pqf-lem-pushforward-qcoh` suffices, exactly as in the source's first paragraph.
- `Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`,
  `Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraChangeOfRings`,
  `Sheaf.AlgebraicGeometry.QuasiCoherentIsoOnAffineCover`, and
  `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`: the corresponding planned
  dependencies belong to the new smaller nodes; they are not claimed mathematically
  unnecessary for those nodes.
- `Sheaf.AlgebraicGeometry.TensorPullback` and
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`: already available through the
  retained statement imports, so redundant as direct proof imports.

The two new modules use public imports only for their signatures and plain imports for
the proof dependencies recorded in their nodes, as required by the stage contract. Their redundant direct
public TensorProduct imports were removed in second reading because TensorPullbackAdjunction
already exports them. No public import of the existing item was removed.

The complete list of old item proof-dependency IDs removed is:
`def-pc-module-pullback`, `def-pur-sheaf-tensor-product`,
`lem-weil-pbc-affine-pushforward-base-change`,
`lem-weil-pbc-module-pullback-affine-sections`,
`lem-weil-pbc-module-pullback-quasi-coherent`,
`lem-weil-pbc-quasi-coherent-algebra-change-of-rings`, and
`lem-weil-pbc-quasi-coherent-iso-on-affine-cover`. Except for the stronger base-change
assertion, these remain statement dependencies or dependencies of the smaller tensor nodes;
the pruning claim is removal from the upper proof, not from the entire import closure.
No claim is made that a module is globally unreachable from every other target branch.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found in the original statement or source. The DAG's construction
and affine identification steps were not available as Lean declarations of their own:
the existing affine-section lemma supplies underlying structure-sheaf linear sections,
not the pulled-back algebra action, functorial comparison κ, or the balanced α/β calculation.
These are now the two separately stated tasks rather than hidden glue in the upper proof.
The full affine base-change theorem was stronger than required for the pushforward clause.

The combined proof-DAG audit found one pre-existing reachable cycle:
`lem-weil-pbc-sheaf-algebraic-structures-objects` →
`lem-weil-pbc-sheaf-algebraic-structures-abelian-component` →
`lem-weil-pbc-sheaf-algebraic-structures-objects`, below scalar restriction through
cokernel/image and site/sheafification nodes. Neither new tensor node belongs to it.
These nodes are outside this item; reported for maintainer repair rather than altered.
The Lean import-pruning check passed with no findings.

## New nodes

`lem-weil-pbc-affine-module-tensor-construction` records the construction part of 01SB
(original step 3) in `lean/Sheaf/AlgebraicGeometry/AffineModuleTensorConstruction.lean`.
It leaves invertibility to a different task and never asserts an equivalence.

`lem-weil-pbc-affine-module-tensor-comparison-isIso` records the affine inverse calculation
(original steps 4–7) in `lean/Sheaf/AlgebraicGeometry/AffineModuleTensorComparisonIsIso.lean`.
It assumes the explicit construction formulas and proves only invertibility on quasi-coherent
objects. Blueprint searches for 01SB and tensor/module facts found no duplicate blueprint
node. Both new nodes inherit the item's chapter, unit, and nearest blueprint ancestor.
There are no changed statements or definitions, and no change records are needed.

## Second reading by D2

1. PASS. Diffed the existing module against the read-only repository. The existing
   theorem signature is byte-for-byte identical, including universes and every
   construction/comparison conjunct. Its local notations and all four public imports
   are unchanged. There are no changed definitions or statements and no change records.
2. PASS as a decomposition. Compiled all three files through lcompile.py, without errors
   or warnings. Exactly two sorries occur, the complete proofs of the two named tensor
   theorems listed above; none occurs in a definition. No prohibited declarations,
   attributes, or kernel-check bypasses occur. Scratch-copy #print axioms reports only
   propext, Classical.choice, Quot.sound, and sorryAx for the main theorem and tensor
   lemmas. The private categorical helper has only the three standard axioms.
   Existential witnesses are eliminated only inside a proof of a proposition: this
   delivery creates no data definition by choosing from a mere existence theorem.
3. PASS. Independently checked the tensor pushout and balanced inverse calculation
   against the local Stacks 01SB source. For a C-module N the maps are
   c tensor (b tensor n) -> cb n and n -> 1 tensor (1 tensor n); balancing with
   b tensor 1 and 1 tensor b proves the two inverse identities and C-linearity.
   The gamma formula fixes the quotient map, which is epimorphic because epsilon has
   the section b; hence its factorization fixes alpha. The kappa unit formula and the
   adjunction fix beta on affine sections. Zero rings, zero modules, identity maps,
   and empty schemes cause no exception. Construction asserts no invertibility;
   comparison assumes that construction and asserts only invertibility. Neither
   restates the full item. Both have source/prose proofs and nodes. Independent
   LeanFinder queries about pushout scalar extension and multiplication tensor
   cancellation, Loogle searches, and repository/Mathlib rg found algebraic tools
   (notably cancelBaseChange) but no theorem closing either whole sheaf-level task.
   Loogle does not index the project's changeOfRings name. Neither hole can be closed
   in a few minutes using the available declarations without further tensor glue.
4. PASS after repairs. The upper proof first uses the existing scalar-restriction and
   qcqs-pushforward results, then the tensor construction/invertibility nodes, and
   finally proves the full-subcategory assembly. All seven removed old proof-dependency
   IDs are now explicitly listed. Dependencies still needed by the new tasks have
   plain proof imports in those modules; they are not claimed globally pruned.
   Checked sk-thm-p1.realized: none of the replaced auxiliary nodes realizes a unit
   statement or step. The construction, affine calculation, and equivalence route stays.
5. PASS after repairs. The old node changes only proof, proof_deps, and proof_origin;
   its uses match the actual upper proof. Each new node has source, complete proof steps,
   proof_deps equal to the union of uses, search records, split status, creation record,
   blueprint ancestry, chapter/unit, and its Lean record. The new Lean statement fields
   now store the exact multiline signatures, rather than whitespace-normalized copies.

Second reading changed documentation, imports, and node metadata only: corrected the
main docstring's stale base-change citation; completed the pruning list; removed two
redundant direct public TensorProduct imports from the new modules; supplied their
planned dependencies as plain imports; and recorded verbatim new signatures. The Lean
proofs and all mathematical statements are unchanged. One upper hole is closed and two
lower holes remain, net -1 before any whole-closure pruning; no extra hole was closed
in second reading.
