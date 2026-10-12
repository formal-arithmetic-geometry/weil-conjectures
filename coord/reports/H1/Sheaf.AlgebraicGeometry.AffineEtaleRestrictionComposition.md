## What changed

The original target signature and definitions are unchanged. Its proof now obtains gamma from a proved fully faithful cancellation construction and applies a properly scoped mate/coherence obligation to obtain d and the remaining identities. The first worker's two auxiliary declarations were removed. Two new modules are imported privately by the target module. The gamma module imports only the full affine site and affine-morphism API needed by its signature. Existing target imports supply its signature.

## Proved and sorry left

`AlgebraicGeometry.Scheme.affineEtale_restriction_composition_gamma` is proved without sorry. `AlgebraicGeometry.Scheme.affineEtale_inverseImage_restriction_composition` has a complete reduction proof, but transitively depends on the remaining named obligation `AlgebraicGeometry.Scheme.affineEtale_restriction_composition_mates` (node `lem-weil-pbc-affine-etale-restriction-composition-mates`). That is the delivery's only sorry. One original theorem body is closed; this is not axiom-free completion of the target.

## No longer needed

No existing import or module is pruned from the target closure. The original direct proof dependencies `def-pc-fibre-product`, `def-weil-pbc-composite-adjunction`, and `lem-weil-pbc-conjugate-iso-unit-equation` now occur in the gamma and mates nodes, respectively, rather than directly in the assembly node. They remain needed by the argument and are not pruned.

## Where the brief, the DAG or earlier work was wrong

The first worker's units lemma quantified over arbitrary gamma and d, without a gamma compatibility hypothesis and without choosing d as the adjunction mate. Its identities cannot hold for arbitrary comparison isomorphisms. Both auxiliaries also lacked matching node metadata. I removed that split and proved the first step using Mathlib fullyFaithfulCancelRight. The repaired remaining obligation assumes the gamma equation and constructs d existentially. It comprises strictly the remaining two steps, not a restatement of the original theorem.

## Second reading by H1

1. Compared the final target module against the repository with diff and the declaration parser: the existing target signature is byte for byte unchanged. No definition changes. Verdict: pass.
2. Compiled all three modules in import order with lcompile.py. Gamma has only standard axioms; the target and mates obligation additionally have sorryAx because the mate proof remains open. No forbidden declarations or hollow definitions. Verdict: pass as a partial reduction.
3. Reviewed both new statements and searched using msearch.py (LeanFinder, Loogle, grep; LeanSearch unavailable). Mathlib supplies cancellation and mate tools, but no exact affine restriction square was found. Gamma requires no arbitrary sheaf data. Mates requires the gamma equation and constructs d, fixing the first worker's false universal claim. Identity morphisms and empty affine objects impose no new assumptions: the argument uses natural transformations and adjunction transposition. The mates docstring gives the full proof and its node. Verdict: pass.
4. The proved gamma step realizes the original first step; the remaining obligation retains the mate and coherence steps. The unit sk-thm-iff realized record is unchanged. Existing imports occur in signature APIs, and no old dependency leaves the closure. Verdict: pass.
5. Updated the original node's proof, proof_deps and proof_origin to match the actual assembly, and added nodes with exact Lean signatures for gamma and mates. Verdict: pass.

Changed the invalid split, proved gamma, and retained one correctly scoped named obligation in its own module. No existing statement was weakened.

## New nodes

`lem-weil-pbc-affine-etale-restriction-composition-gamma` records the proved lift in `Sheaf.AlgebraicGeometry.AffineEtaleRestrictionCompositionGamma`.

`lem-weil-pbc-affine-etale-restriction-composition-mates` records the remaining mate construction and coherence in `Sheaf.AlgebraicGeometry.AffineEtaleRestrictionCompositionMates`.

No change record is needed: existing statements, definitions and public imports are unchanged; new helpers are imported only by the proof.
