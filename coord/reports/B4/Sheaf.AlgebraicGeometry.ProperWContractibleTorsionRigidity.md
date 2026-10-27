## What changed

Proved `AlgebraicGeometry.Etale.proper_wContractible_torsion_rigidity` using the
existing proper henselian derived restriction theorem on `F[0]`. The Jacobson
henselian theorem supplies its ring hypothesis. The torsion characterization and
single-complex homology show that `F[0]` has torsion cohomology. The derived-unit
and Ext comparison identify the resulting bijection with the canonical
`cohomologyMap`. Finally the isomorphism supplied by the given pullback square,
cohomology functoriality and topological invariance transport the result to `t`.

Added only private proof imports, including the existing torsion-isomorphism
transport lemma. The theorem has a local heartbeat allowance for its categorical
elaboration; the 60-second file compilation limit is unchanged. Updated the existing node's proof route and
proof dependencies; all existing declaration signatures and public imports are
preserved. No definitions or consumer modules change. No new nodes.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.Etale.proper_wContractible_torsion_rigidity`
(node `lem-sfb-proper-wcontractible-torsion-rigidity`).

Holes added: none. Holes left in the delivered module: none.

The proof uses the already declared
`AlgebraicGeometry.Etale.proper_henselian_derived_restriction`, which still has
its own existing hole; this delivery does not claim that dependency is proved.

## No longer needed

No existing public import is removed. The following planned direct dependencies
are not imported or used separately by this proof:

- `lem-zl-condensed-henselian-lisse-rigidity`
  (`Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity`): no separate
  w-contractibility of the quotient is needed.
- `sk-thm-pbc-henselian-h0` (`Sheaf.Paper.HenselianPairH0`): subsumed here by
  the existing all-degree proper henselian derived restriction.
- `lem-weil-pbc-proper-fp-permanence`: no auxiliary proper identity morphism is
  constructed; the supplied proper morphism is passed directly to that theorem.
- `sk-thm-pe-weakly-contractible-basis`
  (`Sheaf.AlgebraicGeometry.ProEtale.WeaklyContractibleBasis`) and
  `lem-cbc-abelian-etale-proetale-cohomology-comparison`
  (`Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison`): no separate
  proof of exact global sections on the two bases is needed.
- `thm-weil-pbc-bounded-below`
  (`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper`),
  `def-weil-pbc-exact-global-sections-leray`
  (`Sheaf.AlgebraicGeometry.ExactGlobalSectionsLeray`),
  `lem-weil-pbc-exact-functor-complex-cohomology`, and `lem-kun-leray-bdd`
  (`Sheaf.AlgebraicGeometry.LerayBounded`): the existing derived rigidity
  theorem encapsulates the required proper base change and derived comparison.

These are removals from this node's direct proof plan, not withdrawals of
modules. Dependencies still used transitively by proper henselian derived
restriction remain needed. The Jacobson-henselian dependency is retained.
The unit's realized statement and steps remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The original proof plan repeats a more general proper henselian derived
restriction already declared elsewhere in the library. Specializing that result
to a sheaf in degree zero is shorter. Both Lean import reachability and the DAG
statement/proof dependency search show no path back from that result to this
item, so this reuse creates no cycle. The original mathematical statement is
unchanged, including the zero ring, empty schemes, degree zero, and locally
torsion sheaves without a common annihilator.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
