## What changed

Reconstructed `WeilConjectures.SixFunctors.Etale.Derived.Exchange` from the current
shared source after the returned landing conflict, and filled its sole hole in
`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek`.
All existing signatures, public imports, exported attributes, docstrings and
non-theorem bodies are retained. Two private proof imports supply the existing
constant-complex generation theorem and the proper left-adjoint declaration.

For the proper part of the chosen compactification, explicitly obtain coproduct
preservation from the existing left-adjoint declaration. These instances are
established once, before the objectwise projection argument. Whisker the projection
transformation with the constant-complex functor. The unit projection formula and
`DerivedCategory.isIso_app_singleFunctor_obj` give invertibility at every constant
module. Apply this to the quotient module and then use the existing compactification
projection comparison to obtain the required natural isomorphism.

The finite lower-shriek corollary keeps the existing finite-coefficient comparison
result. The principal lower-star theorem keeps its independent dualizable-quotient
comparison results. A fully proved private `principalIdeal_property` lemma handles
the zero/nonzero generator split for an arbitrary predicate on ideals, avoiding
rewriting the entire categorical comparison expression. The principal lower-shriek
corollary keeps its source open/proper factorization and the principal lower-star
result. Its open comparison is first built in terms of tensor functors and then
transported explicitly to coefficient reduction. Explicit whiskered isomorphisms
from `reductionModIdeal_eq_derivedTensorRight` avoid expensive whole-goal conversion.
Namespace-local
irreducibility and theorem-scoped instance removal control proof elaboration;
`coord/changes/H2-etale-exchange-local-proof-attributes.md` records their scope.

Validation: the complete module compiled cleanly through `lcompile.py` in 28.7 seconds
in the final elaboration form. The required delivery compile checks the file
together with the axiom scan. Diagnostic profiling and
reduced-heartbeat options occur only in scratch copies. No compilation, heartbeat
or kernel-checking limit is raised in the delivered file.

## Proved and sorry left

Current-source holes: 1. Closed: 1, in
`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek`.
Added holes: 0. Split off: 0. Remaining holes in the delivered module: 0.

The unchanged imported instance
`AlgebraicGeometry.Etale.CompactificationUpperShriek.isLeftAdjoint_rightDerivedLowerStar_of_isProper`
remains admitted. This delivery proves the assigned statement from that existing
premise, as stage 3 permits; it does not prove the premise or claim independence from
`sorryAx`. The module-generation theorem used by the proof is already proved.

## No longer needed

None. No source declarations, modules, imports or DAG dependencies are withdrawn.
The original finite and principal comparison dependencies remain in use. No global
module pruning is claimed. The only new declaration is the fully proved private
elementary `principalIdeal_property`; there are no new admitted statements.

## Where the brief, the DAG or earlier work was wrong

The returned packet conflicted with source changes after base `34916ce43`. At the
start of this repair, the shared source had zero holes and two private helpers.
The shared source changed again during the repair (file refreshed at 06:22 UTC):
it now has the original single hole and neither private helper. The final packet
is reconstructed from this latter source, without restoring those rolled-back
helper declarations. The projection argument remains inside the assigned theorem.
The zero-hole count in this repair's earlier draft report has therefore been
replaced by the actual one-hole baseline.

No current DAG node attaches to this module's full name. The unit
`sk-prop-sf-pf-reduction` names its reduction declarations but has empty realized
arrays; no attachment or unit route is changed.

The arbitrary-coefficient proper-adjoint input is stronger than the finite-coefficient
geometric results. This proof uses its existing source declaration explicitly and does
not settle the separate concern about its geometric scope. No new admitted result,
axiom, counterexample or independent geometric justification is claimed.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
