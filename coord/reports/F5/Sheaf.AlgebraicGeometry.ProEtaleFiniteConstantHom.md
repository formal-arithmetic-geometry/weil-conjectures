## What changed

Proved `AlgebraicGeometry.ProEtale.finiteConstantHom_presentation` in
`Sheaf.AlgebraicGeometry.ProEtaleFiniteConstantHom`, with its existing signature unchanged.
The private helpers construct the basis-evaluation linear map, prove its kernel condition and
injectivity, descend a kernel tuple through the ordinary module presentation, and extend the
resulting map on the slice using Mathlib's locally bijective module/scalar Hom equivalences.
The final proof assembles the linear equivalence and proves both naturality equations.
Added the proof-only import `Mathlib.CategoryTheory.Sites.PreservesLocallyBijective`.
Updated the node's clause-(1) proof to this route and its proof-dependency union accordingly.
All existing public definitions and theorem signatures are unchanged.

## Proved and sorry left

Closed one of the item's three original holes:
`AlgebraicGeometry.ProEtale.finiteConstantHom_presentation`
(node `det-pe-finite-local-systems-hom`). This is a proof, not a decomposition.
No holes were added or split off.

Two original holes remain unchanged, both on `det-pe-finite-local-systems-hom`:
- `AlgebraicGeometry.ProEtale.finiteConstantHom_constant`.
- `AlgebraicGeometry.ProEtale.finiteConstantHom_automorphisms`.

The completed argument includes the empty finite ranks, the zero ring and arbitrary target
module sheaves. It uses neither exactness of the section functor nor an arbitrary witness
from an unproved existence statement. All private declarations are proved.

Validation: the retained proof was checked against current sources on 2026-10-19.
`lcompile.py` accepted the finished module again (11.9 seconds), and the required
`deliver3.py --no-push` dry run passed compilation and preflight.
`#print axioms AlgebraicGeometry.ProEtale.finiteConstantHom_presentation` reported exactly
`propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx` in this theorem.

## No longer needed

Removed the proof-only import `WeilConjectures.AlgebraicGeometry.SiteRestrictionExact` and
its node `lem-weil-pbc-site-restriction-exact` from the proof dependencies and tool uses.
Also removed `lem-weil-pbc-abelian-exact-epi-cokernel` from proof dependencies.
Clause (1) uses the ordinary module quotient and the localized sheafification universal
property, so neither exact restriction of abelian sheaves nor a sheaf cokernel calculation
is required. This does not withdraw either shared module: other consumers can still use them.
The remaining planned dependencies concern the still-open constant-Hom and automorphism
clauses and have been retained. The unit's finite-presentation/automorphism route stays.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The first clause admits a direct application
of localized sheafification after the ordinary finite-presentation calculation; transferring
an exact sheaf presentation and then identifying its sheaf cokernel is unnecessary there.
The first baseline compile received no answer from the compile server after 632 seconds;
the instructed retry worked. Subsequent proof checks used only lcompile.py.

Recovery session, 2026-10-19: the initial required dry run passed (commit
`904bde957c`, nothing pushed), and a separate single-file compile passed in 11.9 seconds.
After the validation paragraph was updated, the repeated dry run and the normal delivery
retry both crashed in `sharedrepo.worktree`: its `git checkout -q --detach
origin/sheaf-dag` subprocess exceeded the tool's 600-second timeout. Neither failed
invocation reached publication. The proof, node and report remain in this sandbox.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
