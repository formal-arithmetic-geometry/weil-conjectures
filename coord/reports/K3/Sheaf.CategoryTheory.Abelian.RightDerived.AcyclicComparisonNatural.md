## What changed

Proved `CategoryTheory.acyclicComparison_naturality` in
`Sheaf.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural` without changing its
signature or visibility. A proved private helper transports homotopy uniqueness from
ℤ-indexed complexes to ℕ-indexed complexes by extension by zero and `Homotopy.ofExtend`.
The main proof constructs the three comparison lifts, checks equality after augmentation,
applies homotopy invariance of homology, and uses Mathlib's inverse comparison naturality.
Added the proof-only import `Mathlib.Algebra.Homology.Embedding.ExtendHomotopy`.
Updated the existing node's proof route and proof dependencies to match the Lean argument.

## Proved and sorry left

Closed the sole hole: `CategoryTheory.acyclicComparison_naturality`
(node `lem-sc-acyclic-comparison-natural`). The private helper
`CategoryTheory.homotopy_of_comp_quasiIso_nat` is also completely proved.
No sorry remains in the item; no holes or new statements with sorry were added.
This is a proof, not a decomposition. The existing comparison constructions and homotopy
uniqueness theorem are used with their original signatures.

## No longer needed

Removed the unused direct proof import
`WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`.
It remains available transitively through the required public Acyclic import, so this does
not claim removal of that module from the targets' closure.

Pruned proof dependency `lem-weil-pbc-lift-along-injective-quasi-iso`, whose general model
category lifting theorem is unnecessary: the already implemented
`InjectiveResolution.descOfQuasiIso` constructs both acyclic comparison lifts directly.
Its associated Mathlib model-category module is not imported by this proof.
All other planned proof dependencies remain used; no unit-level route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan invokes general lifting along a degreewise monic quasi-isomorphism for
the two acyclic comparison lifts. The existing definition of the displayed isomorphism
already uses concrete `descOfQuasiIso` lifts, so no general lifting theorem is required.
The homotopy-uniqueness declaration is ℤ-indexed whereas the item is ℕ-indexed; the proved
private extension/restriction helper supplies this glue without changing either interface.
The unit `sk-thm-picard-duality` has no realized step identifying this generic lemma as a
fixed subroute; its statement and proof steps are unchanged.

## Second reading by K3

1. **Unchanged interface — PASS.** Compared the sole delivered Lean module with the
   repository using `diff -u`. The existing public theorem's signature, section variables,
   visibility, and public import are byte-for-byte unchanged. There are no changed
   definitions, change records, additional delivered modules, or target changes.
2. **Proof and axioms — PASS.** Compiled the delivered file with `lcompile.py` without
   errors or warnings. A scratch copy with `#print axioms` for both
   `CategoryTheory.acyclicComparison_naturality` and the private
   `CategoryTheory.homotopy_of_comp_quasiIso_nat` reports only `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. No `sorry`, prohibited
   declaration, or new definition appears in the delivery. The existing
   `descOfQuasiIso` is a degreewise injective-factorization construction, not an
   arbitrary witness chosen from an unproved existence statement.
3. **Split statements and alternatives — PASS.** No statements with `sorry` were split
   off. The proved private helper extends by zero, applies the existing bounded-below
   injective homotopy-uniqueness theorem, and restricts via `Homotopy.ofExtend`; it is
   a strict intermediate result, not a renamed naturality assertion. Checked the
   identity quasi-isomorphism, zero target, and degree-zero boundary: extension adds
   zero objects only in negative degrees and introduces no extra hypothesis.
   Independent LeanFinder, Loogle, and grep searches, including upstream and Sheaf,
   found no direct arbitrary-acyclic-resolution naturality replacement. Mathlib's
   `descHomotopy` requires an injective source resolution, whereas this source need
   only be F-acyclic. Mathlib inverse-comparison naturality is already used.
4. **Shortest route, imports, and unit — PASS.** The proof uses the concrete lifts
   already defining the comparison isomorphism, then homotopy invariance and inverse
   naturality. Both new/helper imports are proof-only. The public Acyclic import is
   required by the statement. The removed direct LongExactSequence import is redundant
   through Acyclic. Compared old and new `proof_deps`: the only removed node is
   `lem-weil-pbc-lift-along-injective-quasi-iso`, explicitly listed above. The unit
   `sk-thm-picard-duality` has empty `realized` statement/step arrays; this generic
   lemma does not replace a realized unit route. No closure pruning of the transitively
   imported LongExactSequence module is claimed.
5. **DAG agrees — PASS.** Compared the node JSON with the repository: only `proof`,
   `proof_deps`, and `proof_origin` change. Read each dependency's Lean record and the
   actual comparison, lift, homotopy, and Mathlib naturality declarations. The four
   revised steps match the proof, including the ℕ-to-ℤ extension/restriction helper;
   `proof_deps` is exactly the union of step uses. There are no new nodes.

Second-reader change: corrected the theorem's stale natural-language proof sketch to
cite the concrete `InjectiveResolution.descOfQuasiIso` construction instead of the
pruned general lifting lemma, and to mention extension/restriction of the homotopy.
The executable proof, all signatures, and the dependency route needed no repair.
Closed holes: `CategoryTheory.acyclicComparison_naturality` (one).
Added holes: none (zero).
