## What changed

Proved `CategoryTheory.compactTests_rightAdjoint_preservesCoproducts` in
`Sheaf.CategoryTheory.CompactTestsRightAdjointCoproducts`, with its original signature
and visibility unchanged. Added proof-only imports of
`Mathlib.CategoryTheory.Adjunction.Additive` and
`Mathlib.CategoryTheory.Adjunction.Limits`.

Three proved private helpers implement the existing node's route:
`coproduct_small_support` injects the nonzero support into the endomorphisms
of an arbitrary colimit cofan; `preservesCoproducts_of_small` shrinks this support,
restricts the colimit cofan, applies small-index preservation, and reinserts the
zero summands; `compactTests_small` proves the direct-sum/adjunction comparison
square and uses the detecting hypothesis. The final theorem obtains additivity
from preserved finite biproducts and combines these helpers.

No definitions, public statements, DAG dependencies, or unit routes change.
The empty family and entirely zero families are covered by the same constructions:
the support can be empty, and all maps from the omitted objects are uniquely zero.
No arbitrary data are chosen from an unproved existence statement.

## Proved and sorry left

Closed the single original hole in
`CategoryTheory.compactTests_rightAdjoint_preservesCoproducts`
(node `lem-sc-compact-tests-right-adjoint-coproducts`). All three private helpers
are completely proved. No holes added or remaining, and no new statement modules.
Single-file compilation passes without warnings. The delivery dry run also checks
all introduced constants' axioms against the permitted three standard axioms.

## No longer needed

No original imports, nodes, or modules are pruned: the existing proof plan needs
only the compact-object definition, and the proof follows it.
During development, redundant proof imports of
`Mathlib.CategoryTheory.Preadditive.AdditiveFunctor` and
`Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts` were removed; their APIs
are already available through the two retained proof imports. These development
imports were never present in the original module.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The stated plan is sufficient and is
now fully formalized, including the nontrivial indexing-universe step. In Lean's
composition notation the support idempotent is `p i ≫ t.inj i` (an endomorphism
of the coproduct), and precomposition with `t.inj i` followed by `p i` distinguishes
it from the idempotent for any other index.

The cited literature and blueprint `_section.md` files are absent from this local
read-only clone. The delivered proof uses the complete proof supplied in the
existing DAG node and declaration docstring; it adds no sourced intermediate holes.
The unit record has empty `realized` lists, so no prescribed realized unit step
is bypassed. Library and Mathlib searches found no direct replacement theorem.

## Second reading by X2

1. Compared the delivered module with the repository version. The public theorem
   signature and visibility are byte-for-byte unchanged; differences are limited to
   the proof, private helpers, proof-only imports, and module documentation. Verdict:
   pass.
2. Compiled the module with `lcompile.py`; it is warning-free and contains no
   `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. A scratch
   `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
   The support injection, small-index reduction, compact Hom comparison, and
   adjunction additivity arguments cover empty and zero families. Verdict: pass.
3. Checked the private helpers against the existing node and searched the library
   and Mathlib search records for an existing theorem. No split-off statements or
   new nodes were introduced, and the existing theorem remains exactly as strong
   as the node statement. Verdict: pass.
4. The proof follows the node route: compactness proves the universe-`u` case,
   then the nonzero support injection and zero-summand deletion extend it to every
   indexing universe. No shorter applicable library theorem was found, and no
   imports or proof dependencies can be pruned. Verdict: pass.
5. The DAG node's `proof`, `proof_deps`, and `proof_origin` remain consistent with
   the implementation; its unit record has no realized steps to bypass. Verdict:
   pass.

Changed only the proof and its private supporting lemmas; no statements, definitions,
nodes, or unit records required repair.
