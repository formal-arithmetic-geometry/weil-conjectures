## What changed

The unchanged theorem `WeilConjectures.integralPullbackComposition` is proved by lifting
finite-system composition through coherent reduction. The proof constructs the natural
composition isomorphisms, proves their defining whole-system equation, pastes the evaluated
comparison squares to obtain the specified finite reductions, and proves associativity by
faithful cancellation. It never assumes finite evaluations are faithful on derived morphisms.

Three supporting modules give coherent reduction, the single-morphism pullback comparison,
and associativity of a fixed lift. Coherent full faithfulness and fixed-lift associativity
are proved. The single-morphism comparison is a separate sourced obligation; it asserts no
composition or associativity and is strictly below the assigned theorem.

The existing canonical reduction definition delegates to a lower-level name containing its
original body verbatim. Its signature, value, and all canonical maps are unchanged. The
change record is `coord/changes/A7-integral-pullback-reduction-comparison-api.md`. No existing
consumer needs adaptation. Explicit category/object arguments and small congruence proofs
avoid expensive elaboration through the implementations of derived functors.

## Proved and sorry left

Original module: one hole closed, `WeilConjectures.integralPullbackComposition`; zero remain.
The proof is complete from the declarations it imports.

Two new supporting results are proved without holes:
- `WeilConjectures.integralSystemReduction_fullyFaithful`
  (`lem-pod-integral-system-reduction-fully-faithful`). The proof derives global
  invertibility from residue-field invertibility, transports completeness through the
  existing coefficient model, uses normalized reconstruction, and restricts the adjunction.
- `WeilConjectures.integralSystemPullbackLift_associativity`
  (`lem-pod-integral-system-pullback-lift-associativity`).

One hole is added and remains:
- `WeilConjectures.integralPullbackSystemComparison`
  (`lem-pod-integral-pullback-system-comparison`). It identifies one actual integral
  pullback with finite-system inverse image, naturally, with the specified Roos projection
  at each exponent. Its module includes its source and full proof plan.

This is a decomposition: one original hole closed and one strictly lower hole added,
not a claim of positive net hole reduction. There is no sorry in a definition or private
helper. New definitions use the existing specified coefficient calculus; no arbitrary
object is chosen from a new mere-existence theorem. The remaining existential comparison
is used only within theorem proofs.

The four retained modules compile through `lcompile.py --all` with no diagnostics:
full faithfulness 5.1 s, the remaining comparison statement 5.5 s, associativity 6.6 s,
and the main theorem 9.8 s. Restoring the original theorem statement text verbatim
also compiled in 8.8 s; scoped transparency options preserve its implicit elaboration.
After final line wrapping, the original-statement main module compiled cleanly again
in 25.3 s. Final delivery validation results are recorded in the delivery output.

## No longer needed

The main module removes these proof imports:
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses`
- `Sheaf.Paper.NormalizedDVREffectivity`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.CategoryTheory.StrictRoosComparison`
- `Sheaf.Paper.IntegralOperationsWellDefined`
- `Sheaf.Paper.SemilinearDerivedSections`

Their analytic arguments remain needed in the single-morphism comparison plan or in
existing imported theory. No whole module or node is claimed globally prunable.
`IntegralPullbackComparisonRealization` and `CompletedPullbackTensorComparison` are not
imported: their dependency `IntegralComparisonSequenceSystems` publicly imports this
item, so using them here would create a cycle. Unused experimental square helpers are
not included; the corresponding squares are proved directly in the assigned module.

The normalized reconstruction calculus is used as an external tool: the finite
constructibility unit does not state its reduction-adjunction criterion. The
coefficient-presentation transport and constructible triangulated API identify the
existing completeness predicate with its hypothesis. These existing declared tools
replace reconstructing that bridge here.

The full-faithfulness proof no longer directly uses strict Roos comparison: the existing
normalized reconstruction adjunction calculus and coefficient-presentation transport
already supply that argument. Its node records this shorter route.

## Where the brief, the DAG or earlier work was wrong

The original plan had not packaged the single-morphism coherent comparison with its
projection normalization as an acyclic usable declaration. The remaining node states
that separate result, rather than renaming the composition theorem. Naturality of
its coherent comparison is essential: a family of unrelated finite-level isomorphisms
would not suffice. Existing comparison-realization interfaces cannot be imported here
because of the cycle above; no held module was changed to remove that dependency.

The inherited report described two supporting holes and a noncompiling main proof.
Coherent full faithfulness is now proved, and the main proof compiles. The compile
limit was respected: explicit arguments and congruence identities fixed the expensive
elaboration; the limit was not raised and the theorem was not split to bypass it.

The full-faithfulness helper requires residue-field invertibility, exactly as supplied
at every use by the assigned theorem. Its new node's Lean signature records this.
The comparison statement retains arbitrary schemes, every positive exponent, every
specified good representative, and their canonical adjoint maps. No finiteness
hypothesis on schemes has been added. Empty schemes and zero objects introduce no
exception to the adjunction argument.

## New nodes

`lem-pod-integral-system-reduction-fully-faithful`: proved coherent full faithfulness
on the stated constructible categories with ell invertible; records the reconstruction
and coefficient-transport dependencies actually used.

`lem-pod-integral-pullback-system-comparison`: the remaining single-morphism natural
system comparison, normalized by the actual projection-adjoint finite maps. Its source
is the reduction and completed-inverse-image argument of Stacks 099N and 0941 and
Bhatt--Scholze 3.5.7, already used in the parent plan.

`lem-pod-integral-system-pullback-lift-associativity`: proved associativity for any fixed
lift satisfying the whole-system equation, by naturality and faithful cancellation.

Definition change record: `coord/changes/A7-integral-pullback-reduction-comparison-api.md`.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
