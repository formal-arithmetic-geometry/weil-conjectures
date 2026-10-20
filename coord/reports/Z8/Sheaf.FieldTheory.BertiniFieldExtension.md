## What changed

Proved `FieldTheory.bertini_field_extension` with its existing signature and definitions.
All supporting lemmas are private and proved in the same module. The proof follows
Stacks Tag 0G4D's separable-element and collision argument. To supply infinitely many
substitutions even over finite fields, it uses the invariant
`T = c_j*x_l - c_l*x_j` and automorphisms `x_i ↦ x_i + c_i*T^m`.
The inverse uses subtraction, since each substitution fixes T. Independence ensures
`j ≠ l`, `c_j ≠ 0`, and transcendence of T, so its powers are distinct.
The node's proof and proof origin record this uniform variant.

## Proved and sorry left

Closed one original hole: `FieldTheory.bertini_field_extension`
(node `lem-zl-bertini-field-extension`). Added zero holes; split off zero statements.
No `sorry` remains in this delivery. The existing imported dependency theorems remain
as stated and supply the geometric-irreducibility and finite-separable-closure steps.

## No longer needed

No original dependency node or module is pruned: all six are used. The finite-field
rational-function base-change/descent paragraph is replaced by the invariant-shear
argument; only the ascent half of the existing transcendental-extension theorem is
needed. No new DAG dependency is introduced. Added proof imports are Mathlib primitive-element
and pigeonhole finiteness, algebraic-independence scalar-extension lemmas, intermediate-field
finite-generation lemmas, and tactics; each supplies a used declaration or tactic.
Replaced the newly added broad `Mathlib.Tactic` import with only the seven tactic
modules actually used. No original import was removed.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The attribute commands on the new private shear
constructions require the change record `coord/changes/bertini-private-shears.md`;
they preserve every existing public signature and definition. The original docstring records the source's constant
translations and finite-field reduction. The updated DAG and proved private lemmas
record the uniform invariant-shear variant used by the actual proof. The unit record
has no realized node at this level, and its mathematical route is preserved.

Validation: the complete module compiles through `lcompile.py`; delivery preflight
checks the declarations and their axioms against the imported dependency proofs.

## Second reading by Z8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
