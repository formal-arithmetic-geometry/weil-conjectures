## What changed

Replaced the proof of
`AlgebraicGeometry.Etale.affineLine_multiplicativeGroup_homology_tateObject`, preserving
its signature, existing public imports, definitions, and all downstream declarations.
Private helpers establish the required comparisons from Deligne's generic direct-image
theorem over a field, extend them over an affine cover, and cancel comparisons to obtain
base change to geometric points. The established algebraically closed field computations
then prove the four clauses, with naturality of the unit and Kummer class identifying
the actual maps in the statement. All added imports are private proof imports.

## Proved and sorry left

The assigned module originally contains one hole, in
`AlgebraicGeometry.Etale.affineLine_multiplicativeGroup_homology_tateObject`.
The complete proof closes that one hole. The delivered module has zero `sorry`;
zero holes are added and zero statements are split off. All 14 private helpers are
proved. The existing projection lemmas and vanishing instances retain their proofs.
The complete module compiles without warnings through `lcompile.py` in 39.9 seconds (a complete diagnostic run; diagnostic settings removed afterward).
The first delivery compile exceeded 60 seconds and pushed nothing. The categorical
comparison was refactored into generic private lemmas, and the complete file was compiled
again before resubmission. Delivery runs the required consumer, source-boundary, and proof checks.
Local reducibility controls keep large derived-functor constructions out of unification;
explicit sheaf-colimit and braiding instance priorities avoid repeated search. The existing separatedness binder is retained even though the proof does not require it.
No upstream
definitions or instances are changed by these local elaboration settings.

## No longer needed

No existing public imports, declarations, nodes, or modules are withdrawn.
Redundant candidate private imports of
`WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne`,
`WeilConjectures.SixFunctors.BaseChange.EtaleDerived`, and
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift` were removed:
the retained imports already expose their declarations. These modules remain transitive
dependencies; this is import cleanup, not a claim that the modules can be withdrawn. The proof
uses `GmRelativeKummer`, retaining the unit's existing relative computation and its
geometric-field inputs. No dependency is claimed pruned merely because its current
Lean importers are absent.

## Where the brief, the DAG or earlier work was wrong

No DAG node has a Lean attachment to this adopted source module. Its docstring cites
unit `sk-prop-a1-kummer`, whose statement is attached to
`prop-pur-gm-relative-kummer`; `thm-pur-kummer-affine-line` is attached to
`Sheaf.AlgebraicGeometry.KummerAffineLine`. These attachments are preserved.
The extension from algebraically closed fields to the arbitrary field in the assigned
signature requires comparisons beyond simply invoking the relative theorem, which
assumes an algebraically closed field and a quasi-compact base.

The launcher paused and resumed this item to reduce the compile queue. The sandbox
budget metadata was reset on resume (original start 2026-10-23 09:56:12 UTC;
resumed metadata start 2026-10-23 17:11:26 UTC). No budget files were edited by this worker.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
