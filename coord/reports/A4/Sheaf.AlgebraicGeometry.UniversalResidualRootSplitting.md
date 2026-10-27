## What changed

Proved `AlgebraicGeometry.UniversalResidualRoot.finiteEtale_splitting` in
`Sheaf.AlgebraicGeometry.UniversalResidualRootSplitting`, preserving its full signature,
public imports, and all four original definitions. All added helpers are private and proved.

The universal-cover argument descends any finite étale cover to a finite étale stage.
An equivalent thin skeleton supplies the directed preorder required by the descent APIs.
Marked uniqueness constructs a section for every geometric fibre point; fibre conservativity
identifies their coproduct with the cover. Thus the proof includes covers not originally
specified over S.

The root algebra is explicitly isomorphic to the tensor product of its individual monic
AdjoinRoot algebras. Their power bases give the specified monomial basis. Explicit ring maps
prove both quotient presentations and their coefficient/root formulas. A finite-ideal binomial
induction proves the exact nilpotence bound. Integral henselian extension and nilpotent adic
completeness give the two henselian pairs. Full faithfulness lifts arbitrary specified
isomorphisms uniquely through both quotients, including their inverses.

The coproduct argument uses universality of finite coproducts directly. Updated the existing
DAG node's proof, proof dependencies, proof origin, and obsolete tool-use entries to match.
No statement, definition interface, target, source-library file, or other consumer was changed.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.UniversalResidualRoot.finiteEtale_splitting`
(blueprint `lem-sfb-universal-residual-root-finite-etale-splitting`).

Item holes: 1 before, 0 after. Holes added: 0. Split-off declarations: 0.
The proof uses the existing named finite-data-descent statement, as intended by stage 3;
this delivery does not claim its transitive dependencies are axiom-free.

The full theorem and the version with minimized imports compiled successfully. The final
version is checked again by the delivery compile and preflight. The proof handles r=0,
n=1, the zero coefficient ring in the algebraic helpers, and empty finite label sets.

## No longer needed

Removed direct private proof imports:
- `WeilConjectures.AlgebraicGeometry.FiniteEtaleGraphClopen`;
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.OpenSubgroups`;
- `Mathlib.RingTheory.Idempotents`.

The new proof does not directly use these planned nodes:
- `lem-weil-pbc-finite-etale-graph-clopen`: replaced by marked sections and conservativity;
- `cor-galois-open-subgroups` and `thm-galois-fundamental`: the existing pointed index is
  thin by injectivity of marked evaluation; its thin skeleton is already a preorder;
- `lem-weil-pbc-locally-nilpotent-extension` and
  `lem-weil-pbc-lift-idempotents-locally-nilpotent`: nilpotent adic completeness gives the
  henselian instance directly;
- `lem-weil-pbc-finite-affine-coproduct-spectrum`: the existing finite-coproduct finiteness
  instance and universality of coproducts suffice without a spectrum/product comparison.

The `FiberEquivalence` import is retained because preflight identifies it as a unit-route
module, although the new argument does not invoke its classification theorem.

Deleted obsolete top-level tool-use approvals for the graph, open-subgroups, and fundamental
classification nodes. These are local dependency removals, not withdrawals: some remain
transitively needed by the unchanged public PointedLimitCech import or by henselian full
faithfulness. No module is withdrawn and no adopted source declaration is removed.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The planned graph/clopen and
open-normal-subgroup arguments were unnecessary for this item. The thin-skeleton and
marked-section arguments prove the same statement. The monic-basis step is implemented
through a finite tensor product instead of successive multivariable quotients.
Nilpotent completeness supplies a shorter proof of the residual henselian pair.
The blueprint unit's route is preserved, including the preflight-required
`FiberEquivalence` import.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
