## What changed

Proved `Module.exists_projective_lift_of_nilpotent_ideal` in
`Sheaf.RingTheory.NilpotentProjectiveModuleLift` without changing its signature or visibility.
Two proved private helpers construct reduction of endomorphisms and prove its kernel nilpotent.
The proof chooses the free A-module on the underlying set of Pbar, splits its reduction onto
Pbar by projectivity, lifts the resulting projector, and uses the image as the lifted module.
The final quotient map is proved surjective with kernel exactly I times that image, and its
canonical A/I-linearity is checked explicitly. No other Lean module is changed.

The only ring-theoretic input beyond the module API is Mathlib's existing noncommutative
idempotent-lifting theorem, already available through the original proof-only import
`Mathlib.RingTheory.Idempotents`. No imports were added. A new Mathlib leaf records that exact
input, and the original node's proof and dependencies now describe the compiled route.

## Proved and sorry left

Closed: `Module.exists_projective_lift_of_nilpotent_ideal`
(node `lem-weil-pbc-nilpotent-projective-module-lift`), the only original hole.
Added holes: none. Remaining holes in the delivery: none. Split-offs: zero.
Both private helpers are completely proved. The existing Mathlib lifting theorem is proved;
the proof does not depend on any Sheaf theorem with sorry.

Validation: the complete file compiles through lcompile.py, with the original universe-polymorphic
statement and arbitrary projective quotient modules. The proof uses no finite-generation or
nontriviality assumption. Zero ring, I = bottom, zero Pbar, and differing ring/module universes
are covered by the same construction; no nonzero vector or nonempty basis is chosen.

## No longer needed

The original dependency `lem-weil-pbc-lift-idempotents-locally-nilpotent` is not needed by this
proof. Its commutative uniqueness statement is replaced by the existing noncommutative existence
theorem, recorded as a Mathlib leaf. In particular the planned universal ring
Z[t]/((t^2-t)^N), its nilpotent principal ideal, and the polynomial evaluation construction
(steps 4 and 5 of the original plan) need no new Lean modules or proofs.
The original three public imports and proof-only Idempotents import are all retained and used.
No existing Lean module is withdrawn; no unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The planned commutative-polynomial detour was unnecessary:
Mathlib already proves idempotent lifting for homomorphisms of noncommutative rings.
The existing commutative leaf gives uniqueness, which is neither required nor valid for
endomorphism rings. The new leaf states only the existence result actually used.
The old declaration docstring is preserved as the original proof plan; the DAG and this report
record the shorter implemented route.

## New nodes

`lem-weil-pbc-noncommutative-idempotent-lift-nil-kernel` is a Mathlib leaf attached to
`exists_isIdempotentElem_eq_of_ker_isNilpotent` in `Mathlib.RingTheory.Idempotents`, lines 249-253.
Its statement permits noncommutative source and target rings and asks only for existence.
The three recorded searches were run through msearch.py. Searches of the DAG and imported
blueprint found no exact existing node. No new Lean statement or module is introduced,
and no change record is needed because all existing signatures and definitions are unchanged.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
