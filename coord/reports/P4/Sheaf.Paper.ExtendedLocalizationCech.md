## What changed

Completed the seven remaining proofs in `Sheaf.Paper.ExtendedLocalizationCech`, using only
Mathlib and proved private helpers in the same module. All existing public statements,
definitions, docstrings, and imports are unchanged.

The scalar endomorphisms act sectionwise by multiplication. This gives commutativity of
scalar powers and the subset-product formula. For `differential_sq`, expand the differential
on each coproduct summand and pair ordered insertions `(j,k)` and `(k,j)` using
`Finset.sum_involution`. Their target subset and scalar coefficient agree; the filtered
cardinalities give opposite integer signs. Repeated insertions vanish. This includes empty
index families and all integer degrees without extra assumptions.

The transition identity follows on each insertion from the subset-product formula.
Coefficient comparison follows from preservation of multiplication and powers by the ring
map. Naturality for arbitrary natural-number arrows is assembled with
`NatTrans.ofSequence`. The cokernel relation proves ideal annihilation. Negative
cardinality rules out incoming degree-zero summands, and the empty-subset product proves
augmentation compatibility.

The proof follows the existing docstrings and Stacks More on Algebra, Tag 0913
(`lemma-extended-alternating-Cech-is-colimit-koszul`), and Algebraization, Tag 099H
(`lemma-map-identifies-koszul-and-cech-complexes`). No new obligations are introduced.

## Proved and sorry left

Closed seven holes, all under node `def-weil-pbc-extended-localization-cech`:

- `SheafOfModules.LocalizationCech.differential_sq`
- `SheafOfModules.LocalizationCech.transition_comm`
- `SheafOfModules.LocalizationCech.comparison_comm`
- `SheafOfModules.LocalizationCech.comparisonCocone_naturality`
- `SheafOfModules.LocalizationCech.idealRow_comparison_zero`
- `SheafOfModules.LocalizationCech.augmentation_incoming`
- `SheafOfModules.LocalizationCech.augmentation_naturality`

No `sorry` remains in the module. Holes added: zero. Split-offs: zero.
The copied shared version already contained proofs of `insert_degree`,
`mapSection_naturality`, and `unitMap_existsUnique`; those are preserved and are not
counted as this delivery's progress.

The entire module compiles through `lcompile.py` with no errors or warnings. Explicit
`#print axioms` checks cover the seven completed theorems and the constructed complex,
comparison, quotient comparison, and augmentation. Every audited declaration uses only
`propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

None. No imports, nodes, or modules are pruned. The node has no external proof dependencies
and no numbered proof steps to bypass. Searches found no existing complete arbitrary-site
construction or matching square-zero theorem; the exterior-algebra Koszul differential in
the source library uses a different model, requiring a longer comparison argument.
Mathlib's coproduct extensionality, finite-sum involution, and sequential natural
transformation constructor suffice for the direct route.

## Where the brief, the DAG or earlier work was wrong

The initial read and the sandbox copy straddled a shared-library update: the initial file
had ten holes, while the copied version already had three of them proved. This delivery
closes the remaining seven. No mathematical defect or statement repair was needed.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
