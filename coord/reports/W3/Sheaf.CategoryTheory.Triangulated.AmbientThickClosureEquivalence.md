## What changed

Proved `CategoryTheory.ObjectProperty.ambient_thickClosure_equivalence` in
`Sheaf.CategoryTheory.Triangulated.AmbientThickClosureEquivalence`, retaining its complete
signature, docstring and public import. The proof follows the node's four steps: ambient
containment by envelope minimality, comparison with relative envelopes, transport through
the two exact functors, and restriction to the full ambient closures. The restricted
forward functor is fully faithful and essentially surjective; its associated equivalence
has the required compatibility isomorphism definitionally.

Three proved private helpers establish retract stability of inverse images, retract
stability of the image under a thick inclusion, and the ambient-relative membership
comparison. These implement the existing node's proof steps directly from Mathlib and
introduce no public interface or unproved dependencies. No node or route changes are
needed.

Resumed the preserved draft and repaired its compiler diagnostics: the seed and target
properties are explicit in envelope-minimality applications, the mapped-seed equality is
rewritten after exposing the local envelope abbreviations, and the proposition-valued
helpers are theorems. The prescribed `lcompile.py` compiled the final module without
errors or warnings in 1.8 seconds.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.ObjectProperty.ambient_thickClosure_equivalence`
(node `lem-trf-ambient-thick-closure-equivalence`).

Proved 1 of 1 original sorries; added 0; split off 0. No `sorry` remains in the item and
no other module is changed. The three private helpers are fully proved from Mathlib.

## No longer needed

None. The sole public import `Mathlib.CategoryTheory.Triangulated.Generators` remains
necessary for the statement and proof. Both declared dependencies, `pur9-def-thick` and
`def-weil-triangulated-category`, are Mathlib leaves and are used. No node, module or unit
step is bypassed. No new imports or modules are introduced.

The preserved prescribed LeanFinder search returned equivalence infrastructure,
including `Equivalence.congrFullSubcategory`, but no closure-transport theorem. Loogle for
`CategoryTheory.ObjectProperty.triangEnvelope` returned the envelope construction and
minimality API. The prescribed grep search found no mapped-envelope theorem; direct `rg`
of Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` confirmed that existing generator
results use envelope minimality rather than asserting this ambient comparison.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The zero seed remains essential for an empty class of
generators. The proof maps existing retract equations and assumes neither idempotent
completeness nor nonempty generators. The unit route and all four node steps are kept.

The preserved draft was unverified: several envelope-minimality applications inferred
the wrong category, one simplification did not unfold local abbreviations, and its two
proposition-valued definitions produced linter warnings. These are repaired. Intermittent
server nonresponses occurred during resumption, but the final prescribed compile succeeded.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
