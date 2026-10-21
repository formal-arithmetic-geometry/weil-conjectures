## What changed

Proved `SheafOfModules.ringedStrictTowerProjectionMorphism` in the assigned module.
Its complete signature, original docstring and public imports are unchanged.

The proof reassembles complexes of strict towers using the existing library equivalence,
localizes tensoring with bounded finite-free coefficients, and constructs natural
normalized evaluation isomorphisms. A coefficient-natural chain projection mate descends
using functorial K-injective resolutions. The existing totalization-left equation
identifies its evaluated components with the canonical derived projection mate.
Ordinary-limit coaugmentations and the normalized direct-image/limit comparison give
the augmentation square. Naturality gives all three Roos squares.

All additional proof helpers are private and proved. The proof reuses four existing
private APIs through proof-only `import all`: tensor preservation of quasi-isomorphisms,
the pullback quasi-isomorphism lemma, total-pullback naturality, and the total projection
summand equation. The adopted-source complex/functor equivalence is reused unchanged.

The two auxiliary native records now specialize generic data records over abstract
categories and localization functors. The native direct-image record fixes its counit
predicate to the exact original equation. All native mathematical requirements remain
identical; generated constructor and fully qualified projection names move to the
generic records. The complete old and new definitions and consumer inventory are in
`coord/changes/P3-strict-projection-record-layout.md`. No external consumer needs
adaptation. The node records this proof route and the supporting public interfaces.

Validation: the delivered module compiled cleanly under its actual module path in
56.0 seconds, with zero holes and no warnings. The canonical comparison uses generic
categorical cancellation and transport. The theorem signature and docstring match the
original byte-for-byte; public imports are unchanged; the node's proof dependencies
are exactly the union of its proof-step uses. Delivery dry run: passed (compile and all preflight checks); review class CODEX for the
documented record-interface repair, supporting public declarations and node update.

## Proved and sorry left

Closed the one assigned hole:
`SheafOfModules.ringedStrictTowerProjectionMorphism`.

Holes closed: 1. Holes added: 0. Holes left in the delivered module: 0.
All added private lemmas have complete proofs. No intermediate statement was split off.
The existing named `SheafOfModules.ringedProjectionFormula_totalization_left` theorem
remains a separate project item; this delivery does not claim to close its hole.

## No longer needed

Removed these direct proof imports:

- `Sheaf.Paper.ProjectionFormulaTotalization`: its first inverse equation suffices.
- `Sheaf.Paper.ProEtaleProjectionFormulaArrows`: the proof works on the original
  arbitrary small ringed sites using the generic arrows.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`: the
  normalized transformation is constructed directly using resolutions and localization.
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`: its instances are already available
  through the retained diagram imports.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`: the
  given normalized limit data and naturality suffice.

Removed this node's proof dependency edges to
`lemma-weil-pbc-projection-formula-totalization`,
`lem-weil-pbc-right-adjoint-preserves-kinjective`, and
`lem-weil-tower-category-levelwise-abelian`. The full two-sided totalization theorem is
unnecessary here. Functorial tower resolutions and preservation of quasi-isomorphisms
by evaluation extend the normalized evaluation comparison, so neither the planned
preservation of K-injectives by evaluation nor constant-tower K-injectivity is needed.

No module is withdrawn or globally pruned. Other modules, including
`RingedPushforwardCompletion`, independently import the full totalization and pro-etale
arrows modules. The proper-base-change unit and its realized route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement is unchanged. The plan's augmentation argument is longer
than needed: the normalized common-underived comparison already gives the equation
on representatives, and naturality and resolutions extend it to all derived objects.
Evaluation normalization likewise extends from K-injective tower complexes without
proving preservation of K-injectives by evaluation.

The original native record layout and repeated native comparison conversions made
checking expensive. Generic interfaces, componentwise chain constructions, and generic
categorical cancellation preserve the mathematical objects and permit the required
single-file compile. The independent statement reader should verify the exact native
specializations in the change record. No target declaration or adopted-source
signature, definition, proof, attribute or import is edited.

The read-only checkout prevents using `downstream.py` unchanged because its scanner
registers a repository-local cache write at exit. It was stopped before exit; source
searches over the library and preserved Lean files supplied the consumer inventory.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
