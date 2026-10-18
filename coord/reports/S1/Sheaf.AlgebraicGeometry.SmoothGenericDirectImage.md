## What changed

Proved the target theorem from two strictly smaller intermediate interfaces: bounded/lisse cohomology and the pairing-transpose ordinary exchange. Added a generic relative-dual boundedness interface. The three intermediate proofs remain sorry because the full six-functor constructions are not available within this item; each is named and documented in its module and DAG node. All files compile together.

## Proved and sorry left

The target declaration is proved by combining `smooth_generic_directImage_cohomology` and `isIso_smooth_lisse_ordinary_exchange`. Three strictly smaller obligations remain as named declarations:

- `isBoundedConstructible_smooth_lisse_relativeDual` (`lem-asd-smooth-lisse-relative-dual-bounded`)
- `isIso_smooth_lisse_ordinary_exchange` (`lem-asd-smooth-lisse-ordinary-exchange`)
- `smooth_generic_directImage_cohomology` (`lem-asd-smooth-generic-direct-image-cohomology`)

## No longer needed

No planned proof dependency was removed from the original module imports; the proof route uses the smooth tensor, compact-support boundedness, finite lisse dual, and derived base-change interfaces through the intermediate declarations. No source modules are pruned.

## Where the brief, the DAG or earlier work was wrong

The original eight-step proof cannot be elaborated directly within the single-file timeout because its internal-adjunction pairing and finite clopen recombination expand into a very large dependent expression. The decomposition records the two independent mathematical obligations rather than moving the target statement under another name. The split interfaces compile and the target combines them by a direct proof.

## New nodes

`lem-asd-smooth-lisse-relative-dual-bounded`, `lem-asd-smooth-lisse-ordinary-exchange`, and `lem-asd-smooth-generic-direct-image-cohomology` are new strictly smaller obligations, each with a corresponding module and DAG node.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
