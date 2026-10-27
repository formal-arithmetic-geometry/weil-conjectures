## What changed

Copied `Sheaf.Paper.ExceptionalFiniteRealization` into the sandbox. The original
`integralExceptionalEtaleDerivedRight_existsUnique` hole is now a real categorical
assembly from two named lower interfaces: existence of a normalized comparison and
uniqueness of any comparison satisfying the universal right-derived-unit square.
The lower interfaces are documented split-off theorems in the same module, and the
item node records the revised proof route.

## Proved and sorry left

The original theorem `WeilConjectures.integralExceptionalEtaleDerivedRight_existsUnique`
is proved by combining the existence and uniqueness interfaces.

Two strictly smaller split-off holes remain:

- `WeilConjectures.integralExceptionalEtaleDerivedRight_exists`, node
  `lem-pur-adic-etale-derived-right-existence`;
- `WeilConjectures.integralExceptionalEtaleDerivedRight_unique`, node
  `lem-pur-adic-etale-derived-right-uniqueness`.

No definitions contain `sorry`.

## No longer needed

No imports were removed. The three original proof dependencies remain available to
the parent construction; the split interfaces have no additional imports.

## Where the brief, the DAG or earlier work was wrong

The original proof plan bundled construction of the normalized derived comparison and
its uniqueness into one unproved declaration. The Lean target can be reduced cleanly
by naming these two independent obligations; the parent now performs the genuine
existence-plus-uniqueness assembly.

## New nodes

- `lem-pur-adic-etale-derived-right-existence`: existence of the comparison satisfying
the full universal right-derived-unit square.
- `lem-pur-adic-etale-derived-right-uniqueness`: uniqueness of a comparison satisfying
that square.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
