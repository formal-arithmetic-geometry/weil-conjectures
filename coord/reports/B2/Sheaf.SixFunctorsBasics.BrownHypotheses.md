## What changed

Generalized the existing finite-support proof to individual compactness. Proved
`CategoryTheory.exists_uniform_hom_single_shift_bound_of_compact`: any compact
object of the constructible localizing closure has a bound on maps into shifted
heart objects, uniform over all eligible heart targets. The source need not be
constructible or bounded, and no Brown bundle, coefficient admissibility, base
field or field cohomological bound is assumed. Proved its contrapositive
`CategoryTheory.not_isCompactObject_of_unbounded_ext`, which identifies a
noncompact source directly. The old Brown-specific results now follow from these
proofs and the existing Brown criterion, with identical public signatures.

Replaced the proper-direct-image coproduct proof import by its two narrower inputs
and a proved private local countable-exactness instance. Kept the large Brown bundle
folded after its API. The initial unchanged file exceeded the per-file limit at
68.9 seconds; the profiled refactor compiled in 49.2 seconds. The final compile
removed profiling and passed without warnings in **29.5 seconds**. Delivery checks
the declarations and axioms and compiles the unchanged direct importers.

## Proved and sorry left

Original item holes closed: **0 of 1**. Holes added: **0**. Split-off holes: **0**.
The only remaining hole is `CategoryTheory.brownHypotheses`, still the original
unrestricted assertion and still marked STATEMENT-DISPUTED. Its signature, docstring,
unit statement and unit route are preserved. No false unrestricted compactness or
Ext-vanishing premise is introduced. This packet does not claim that theorem is
proved or decomposed.

The two new public theorems and the three extracted private compactness helpers
have complete Lean proofs. The private countable-exactness instance is also proved.
All four existing Brown-specific finite-support/vanishing signatures are preserved.
This is a generalization of the proved necessary compactness condition, allowing the
remaining obstruction to be tested on one object rather than the entire Brown bundle.

## No longer needed

Removed the direct proof import
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarCoproducts`.
The proof uses only repleteness of abelian pro-etale sheaves and transfer of the tower
projection property to module objects, obtained from the two narrower imports named
in the change record. No proper-direct-image theorem is used by these arguments.

The node `lem-sfb-brown-uniform-heart-ext-bound` no longer depends directly on
`lem-sfb-brown-varying-heart-ext-bound`: it uses the new individual-compactness bound
and the existing Brown criterion. The varying-heart public theorem is retained for
other uses, including the positive-Ext obstruction. No existing node or module is
withdrawn. The removed direct import remains elsewhere in the transitive closure;
this packet claims **no whole-module pruning**.

## Where the brief, the DAG or earlier work was wrong

The current local and server queues both mark the item `disputed`, with one hole.
There is no current rework row or B2 return for this item. The old global-build error
file lists failed imports from an earlier revision; the unchanged current file
elaborated successfully but exceeded the 60-second acceptance limit.

The unrestricted Brown theorem is already disputed for arbitrary positive-
characteristic fields. The supported finite-field compactness theorem requires the
geometric field of a finite-field datum, and integral compactness requires an explicit
Ext bound. Finite type over an arbitrary field does not establish these bounds.
The maintenance rollback explicitly retired the false unrestricted compactness
splits. They are not recreated or used here. A correction to the unit statement
still needs the human's decision. This packet proves a necessary condition from
individual compactness; it does not provide a formal field-cohomology counterexample.

## New nodes

`lem-sfb-compact-uniform-heart-ext-bound`: the proved individual-compactness uniform
heart Hom bound and its contrapositive, in the assigned module. Its source, complete
proof, edge cases (zero source, no eligible target, repeated targets, and unbounded
source), and Mathlib searches are recorded. No new holed module is added.

Updated the existing Brown-uniform-bound node's proof and dependencies to follow
its new use of the compactness-only theorem. All other statements are unchanged.

## Related modules compiled before delivery

3 related module(s) compiled against this delivery by deliver3.py: 3 OK.

```json
{"capped": false, "direct": 3, "left_out": 0, "own": {"Sheaf.SixFunctorsBasics.BrownHypotheses": "5619ba3a9c0a46a63c7341fee810d93eac5270b9"}, "results": {"Sheaf.Paper.LocalizingExceptionalAdjoint": {"hash": "9b80929ae886e8305a73db59aae3e626c6c33cd3", "status": "OK"}, "Sheaf.SixFunctorsBasics.BrownHypothesesCoefficientIso": {"hash": "80cf11f0cc781fe2530a33ebe045d127e0d1bae7", "status": "OK"}, "Sheaf.SixFunctorsBasics.BrownHypothesesFiniteField": {"hash": "40b1ac159f94b5a3cd0b71c7acef53f076a729f5", "status": "OK"}}, "seconds": 101, "time": "2026-10-28T02:14:42+0800", "transitive": 0, "version": 1}
```

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
