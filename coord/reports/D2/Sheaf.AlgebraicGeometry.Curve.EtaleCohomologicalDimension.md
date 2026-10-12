## What changed

Proved `AlgebraicGeometry.IsConnectedCurve.subsingleton_etaleCohomology_of_two_lt`
with its signature unchanged. The existing complete proof
`IsCurve.subsingleton_sheafH_of_three_le_of_forall` implements the node's nine-step
argument. Its affine H2 hypothesis is supplied by the existing declaration
`IsCurve.subsingleton_sheafH_two_of_isAffine` (lem-sc-affine-curve-h2-vanishing).
The proof then transports subsingletonness across the natural isomorphism
`Scheme.nonempty_sheafH_extDerivedIso` (lem-weil-pbc-sheafH-ext-derived-comparison).
Added its proof-only import, and updated the node with this final transport step.
No new declarations, definitions, or statements were introduced.

The final module compiles cleanly with lcompile.py. LeanFinder, Loogle, and Mathlib
grep found no direct Mathlib result; repository searches found the existing curve
proof and the already implemented comparison. The comparison import passes
import_direction.py. The unit's realized statement and steps lists are empty;
the node's original nine-step route is retained through its existing implementation.

## Proved and sorry left

Proved `AlgebraicGeometry.IsConnectedCurve.subsingleton_etaleCohomology_of_two_lt`
(lem-sc-cohomological-dimension), removing the sole sorry in the item.
No sorry remains in the delivered module and no new sorry is introduced.
This is a proof from existing library declarations; their transitive unfinished
proofs remain downstream work, as required by stage 3.

## No longer needed

Removed these unused direct proof imports:

- `Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.AlgebraicGeometry.EtaleSheaves`
- `Sheaf.AlgebraicGeometry.TorsionFilteredUnion`
- `Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`
- `WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing`
- `WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport`
- `WeilConjectures.AlgebraicGeometry.Sites.TorsionAcyclic`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.EdgeMap`

The modules above need not be imported directly by this item. Their mathematical
nodes are not pruned from the argument: the complete proof reused from
HighDegreeVanishing implements the original nine steps and uses their results
transitively. In particular HighDegreeVanishing remains reachable through
CohomologicalDimension. All three public imports are retained for the existing
statement interface. No unit route or underlying proof node is bypassed.

## Where the brief, the DAG or earlier work was wrong

The statement uses homology of total right-derived global sections, whereas the
existing vanishing theorem uses the Ext model `Sheaf.H`. These are not
definitionally equal. The DAG lacked the explicit final comparison dependency;
the already proved lem-weil-pbc-sheafH-ext-derived-comparison supplies it.
The original nine-step proof had already been implemented in the source library,
so it was reused instead of copied or split into new unfinished statements.


## Second reading by D2

1. **Unchanged public statements: pass.** Compared the sole delivered Lean module against
   the repository. The existing theorem signature is byte-for-byte identical, including
   the algebraically closed field, connected-curve and smoothness instances, torsion
   hypothesis, natural degree and strict bound. No definition, declaration name, public
   import, or target statement changed. There are no change records to review.
2. **Proof and axioms: pass for this stage.** Local compilation completed without errors
   or warnings. A scratch copy with `#print axioms` for
   `AlgebraicGeometry.IsConnectedCurve.subsingleton_etaleCohomology_of_two_lt` reports
   exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter comes
   from existing unfinished dependencies: this is not yet an axiom-closed target proof.
   The delivered module contains no sorry or prohibited declaration. Inspected both
   invoked theorem signatures: connectedness supplies `IsCurve`, affine H2 vanishing
   supplies precisely the universal hypothesis of the high-degree theorem, and omega
   converts `2 < q` to `3 ≤ q`. The comparison component maps Ext cohomology to the
   stated derived cohomology; its inverse is injective, so subsingletonness transfers
   in the correct direction, including the boundary degree q = 3.
3. **Split statements: pass, none.** No new theorem, node, or sorry is introduced, so
   there is no split-off claim to test or duplicate to search for. Read the existing
   comparison declaration and found its other uses by repository search; it is reused
   rather than restated.
4. **Route and pruning: pass.** Read the implementation of
   `IsCurve.subsingleton_sheafH_of_three_le_of_forall`, including its affine-open,
   two-envelope, cokernel, dimension-shift and filtered-union steps. It implements
   the node's retained nine steps. The existing wrapper
   `IsCurve.subsingleton_sheafH_of_three_le` supplies the same affine-H2 hypothesis,
   so using it would merely shorten the spelling of this same argument. No rewrite
   is needed. All eleven removed direct proof imports are reported above; their
   nodes remain used transitively, and no old proof dependency is pruned. The unit
   `sk-prop-cd` has empty realized fields; the pre-existing accepted route departure
   is recorded in the node's `reviewed` field and is not newly introduced here.
   The two retained proof imports provide affine H2 vanishing and the comparison;
   the three unchanged public imports preserve the statement interface.
5. **DAG agreement: pass.** Parsed both node versions. Only `proof`, `proof_deps`, and
   `proof_origin` differ. The original nine proof steps are identical, step ten
   records the concrete theorem application and comparison, the only added
   dependency is `lem-weil-pbc-sheafH-ext-derived-comparison`, and the dependency list
   equals the union of the steps' uses. The statement, source, unit, and Lean record
   are unchanged.

Second reading changed only the node JSON indentation back to the repository's
style and added this review. The proof was left intact. Compilation and axiom
checks used the Lean 4 skill's guidance through the required project wrapper.
