## What changed

Proved `CategoryTheory.exists_perfect_constant_derived_map_local` through the existing
perfect-source local chain-representative theorem and a new, proved bounded-chain
algebraicity theorem. The main module proves exactness of further slice restriction,
the derived composition comparison, localization transport, model-isomorphism
cancellation, and bind composition of coverings. All existing signatures and definitions
are unchanged. The new module constructs algebraic component maps from finitely many
local generator images and reflects their chain equations through injective constant units.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.exists_perfect_constant_derived_map_local`
(lem-sfb-perfect-constant-derived-map-local).
The new theorem `CategoryTheory.exists_bounded_constant_chain_map_local`
(lem-sfb-bounded-constant-chain-map-local) has a complete proof, with no hole added.
No `sorry` remains in either delivered module. No definition contains `sorry`.
Validation: the required dry run completed successfully on 2026-10-19:
`OK (dry run): commit 27e31b1e70 compiles and passes the preflight; nothing pushed`.
Both delivered modules compiled and passed the delivery checks. The review class is
CODEX because the delivery adds a proved helper and its node, updates the original
node, and records declaration-scoped elaboration commands. The original theorem's
signature is byte-for-byte identical to the current library statement. Every Lean
line is at most 100 characters, and both nodes' proof dependencies equal the union
of their proof steps' uses. Existing dependencies retain their own proof obligations;
this delivery adds no hole to them.

The expensive full sheafification-adjunction unit from the retained attempt was
replaced by Mathlib's direct module sheafification unit. The completed dry run
validates this repair within the ordinary compilation limit.

## No longer needed

Removed the item's proof imports:

- `Mathlib.CategoryTheory.Abelian.FunctorCategory`;
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`;
- `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver`;
- `Mathlib.CategoryTheory.Sites.CoverLifting`;
- `Mathlib.CategoryTheory.Sites.PreservesSheafification`;
- `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`.

The proof no longer uses `lem-weil-pbc-site-constant-morphism-local` or
`lem-weil-pbc-site-constant-restriction`: the new module works directly with the
ambient constant-module units and restriction, avoiding a comparison to constants
on the slice. It also does not use `lem-weil-pbc-site-sheafification-sections-local`:
the proved generic constant-section lifting/injectivity API suffices, without the
stronger precoverage assumptions of that module. The explicit import of
`lem-weil-pbc-site-module-presheaf-sheafification-exact` is unnecessary: constant
functor exactness already supplies its consequence. Other users may still need
these nodes. The retained attempt's
`exists_perfect_constant_derived_map_local_of_models` is not delivered: it merely
repackaged the entire original obligation.

## Where the brief, the DAG or earlier work was wrong

The retained attempt destructured perfectness with an obsolete tuple shape. Current
perfectness gives strict upper/lower bounds, termwise projectivity and finiteness,
and a model isomorphism, without requiring ordered bounds. The proof uses min/max
of the bounds. The retained model-level sorry was not a genuine reduction.
The original sheafification-sections-local theorem assumes stronger precoverage
composition classes than IsSiteForCoverings. The new proof uses generic local
injectivity and surjectivity instead. Its covering-refinement lemma derives the
needed presieve refinement directly from the three stated covering axioms.
The zero complex, zero module, unordered support bounds, empty-covered objects,
and an unbounded target are all handled by the written proof.
The imported high-priority `GrothendieckTopology.hasSheafify_of_essentiallySmall`
instance requires a successor universe, which prevents inference at the arbitrary
`max u v` coefficient size here. A declaration-scoped instance removal selects the
standard concrete sheafification construction while elaborating this theorem;
no instance attribute is changed for importers.
No target or existing statement was weakened; the integral-model unit route stays intact.

The interrupted attempt's sandbox was retained and checked against current sources.
The required dry run was run before editing the report, and it passed. The consumer
check (`tools/downstream.py` with `--uses`) finds only the item's own declaration as
a textual use of the theorem. Its public signature and public imports are unchanged,
so none of the 305 transitive importing modules needs adaptation. In particular,
`Sheaf.Paper.WContractibleConstantReductionsML` continues to import the same interface.
The declaration-scoped elaboration change is documented in the change record.

## New nodes

`lem-sfb-bounded-constant-chain-map-local` is the underived finite-component step of
Stacks Tag 09BE, using the generator argument of Modules on Sites Tag 093S(3).
It requires no projectivity, terminal object, or derived-category instances and allows
an arbitrary target complex. Its componentwise conclusion is strictly part of the
derived argument. The theorem is proved in this delivery, with no split-off hole.
The new node carries the retained search records; this resumption repeated the
launcher grep search and found only the unrelated complex-manifold result. There are no
mathematical statement/definition changes or forced consumer adaptations.
The static command-scope change is recorded in
`coord/changes/perfect-constant-derived-map-local-scopes.md`.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
