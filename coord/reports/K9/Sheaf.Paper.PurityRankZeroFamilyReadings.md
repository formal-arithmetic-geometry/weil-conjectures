## What changed

Replaced the hole in `rank_zero_family_readings` by an explicit comparison: the inverse
of the canonical section base comparison for the rank-zero Rees family over the line.
Private lemmas normalize etale section objects by the coefficient unit, prove that
base comparison and prescribed restriction preserve that normalization, and cancel the
normal collapse. Base-square pasting then gives both endpoint readings.

Only the assigned Lean module and its own DAG node change. Public imports and the theorem
statement are preserved. No shared definitions, source-library declarations, or unit routes
change. Proof imports supply the existing base-comparison laws, finite-etale counit
normalization, and derived pullback unit-composition coherence.

Validation: the final module compiles through `lcompile.py` in 30.2 seconds with no
warnings. Its public theorem signature is byte-for-byte unchanged. The file contains
zero `sorry`s; no shared module or direct importer needs adaptation.

## Proved and sorry left

Closed: `WeilConjectures.PurityFiniteSetting.SectionRestriction.rank_zero_family_readings`
(node `lem-pur-rank-zero-family-readings`), the item's one original hole.
Added: none. Remaining in the item: none. No split-off statements.
All private helpers have complete proofs. The proof uses existing stated dependencies;
no claim is made here that their entire transitive import closure is hole-free.

## No longer needed

No original imports are removed and no modules or declarations are withdrawn.
The direct proof dependency `pur9-def-upper-shriek-composition` is replaced by the
already proved finite-etale normalization equations and section base-comparison laws.
Its module remains part of the original public data imports; this is no claim that the
module can be withdrawn elsewhere. The proof does not use delta, its normalization,
or the theorem `section_constant_trivialization`; its original module remains publicly
imported for the definition `lineCounit` used by the statement.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The planned counit-pasting argument can be completed using
existing declarations. The ordinary-etale unit normalization makes explicit why the
zero reading uses exactly the published restriction along the normal collapse.
The argument assumes neither reducedness nor nonemptiness of the base.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
