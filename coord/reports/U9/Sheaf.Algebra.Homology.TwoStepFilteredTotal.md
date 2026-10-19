## What changed

Proved both compatibility theorems in
`lean/Sheaf/Algebra/Homology/TwoStepFilteredTotal.lean`, preserving all signatures,
definitions, visibility and existing docstrings. Added the proof-only import
`WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns` for its proved
`HomologicalComplex.HomologySequence.quasiIso_τ₂`.

`twoStepTotal_homotopy` applies `DerivedCategory.Q_map_eq_of_homotopy` to the
ordinary total homotopy already supplied by the filtered homotopy relation.
`twoStepTotal_inverts` selects the representative supplied by the definition of
filtered quasi-isomorphism. Quotient lifting computes its image to the ordinary
derived image of its total map. The subcomplex inclusions are monomorphisms, so
their canonical cokernel sequences are short exact. The representative and its
canonical cokernel map give a morphism between those sequences. Applying the
existing five-lemma theorem to its two graded quasi-isomorphisms proves that the
total map is a quasi-isomorphism; ordinary derived localization inverts it.

This is exactly the argument already written in the declaration docstrings; the
node has no numbered proof steps or proof dependencies to change. The unit route
is preserved. No definition or statement repair and no consumer adaptations.

Checked the filtered derived category definition in local Stacks `trace.tex`,
section “Filtered derived category” (Tag 03TB), the full signatures of the used
Lean declarations, and the unit record `sk-p-trace`. The argument imposes no
bounds on cochain degrees and applies to zero complexes, zero subcomplexes,
identity subcomplex inclusions, and the zero ring as well.

LeanFinder search for the short-exact-sequence quasi-isomorphism criterion found
the Mathlib third-component theorem but not the middle-component theorem;
Loogle confirmed the latter is not a Mathlib identifier. Local source search
found the already proved migrated middle-component theorem in BicomplexColumns.
The import-direction check permits this import. All compiles used lcompile.py.
The final proof compiled cleanly in 2.0 seconds; an additional compile with
#print axioms confirmed that both theorems and `twoStepTotal` use only propext,
Classical.choice and Quot.sound.

## Proved and sorry left

Closed 2 of 2 original holes, both attached to
`def-trf-two-step-filtered-total`:

- `CochainComplex.twoStepTotal_homotopy`.
- `CochainComplex.twoStepTotal_inverts`.

No sorry remains in the item. No holes added or split off. The total functor now
has no sorry dependency, as verified by #print axioms.

## No longer needed

None. No imports removed, no declared proof dependencies bypassed, no nodes or
modules pruned. The existing public import supplies the statements and remains
necessary; the added proof-only import supplies the proved five-lemma tool.
The proof does not rely on the unproved graded compatibility theorems of
TwoStepFilteredModuleDerived.

## Where the brief, the DAG or earlier work was wrong

No mathematical or process correction was needed. The interrupted turn had left
only dispatch metadata in the sandbox, with no pending compile or delivery; the
item was resumed in that same sandbox with the original budget metadata intact.

## Second reading by U9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
