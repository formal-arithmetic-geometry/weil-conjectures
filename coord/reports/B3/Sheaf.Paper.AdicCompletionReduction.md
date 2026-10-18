## What changed

Replaced the only hole in Sheaf.Paper.AdicCompletionReduction,
adicCompletionReduction_restricted_isIso, with a proof using finite generators,
the existing koszulQuotientLimit comparison and its unit square, a new perfect
scalar comparison, and the nilpotent Koszul completion calculation. The final
step proves that the specified evaluation adjoint is inverse to reduction of the
specified completion map; no arbitrary comparison map replaces evaluation.

Extracted the already proved scalar adjunction API to
Sheaf.Paper.AdicReductionAdjunction to avoid an import cycle. All eight existing
signatures and bodies are unchanged; the original module publicly imports this
new home. Added proved reduction-map unit, composition, identity and isomorphism
laws. The downstream --uses checks found no external consumers of the moved API.

Added NilpotentKoszulGradedTower and NilpotentKoszulCompletionUnit. The first
computes every a-step transition by exterior-degree projection. The second
constructs the degreewise limit and a section of one-minus-shift, using a finite
geometric sum on its nilpotent complement and partial sums on the constant part;
the existing kernel/cone quasi-isomorphism then applies to the specified unit.
The argument covers unbounded complexes, the empty generator list and the zero
ring, without removing a prefix of the tower.

Validation: lcompile.py --all compiled all five delivered modules without errors
or warnings. All 17 pre-existing public signatures were compared with the original
file and remain identical. A separate consumer importing only
Sheaf.Paper.AdicCompletionReduction compiled checks of all eight relocated names
and the completion isomorphism/naturality API, confirming the public re-export.
All delivered Lean lines have at most 100 characters.

## Proved and sorry left

Original holes: one. Closed the original declaration
AlgebraicGeometry.Scheme.adicCompletionReduction_restricted_isIso from the named
interfaces. There are no sorries left in the item module or in the relocated API.

Added one remaining hole:
AlgebraicGeometry.Scheme.koszulCompletionScalarComparison, node
lem-weil-pbc-koszul-completion-scalar-comparison. It is strictly the perfect-tensor
comparison for the Koszul product cone and its unit square: it does not assert
nilpotent completion, the quotient-limit comparison, or invertibility of the
completion evaluation. What remains is to implement finite-projective retract
splittings through countable products, bounded totalization, exterior-algebra
base change (using the exterior-basis construction of nonempty_koszulBaseChangeIso,
with its unit and transition compatibility checked explicitly), and transport to the arbitrary K-flat model. Its docstring gives the
complete argument and its module imports the existing ingredients.

The new nilpotentKoszulGradedTower and nilpotentKoszulCompletionUnit_isIso are
proved. Closing the original hole while adding the scalar-comparison hole is a
decomposition, not an unconditional proof: among delivered declarations one hole
is closed and one is added.
No axioms or hollow definitions were introduced.

## No longer needed

Removed the direct proof import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit
(node lem-weil-pbc-ringed-strict-tower-homotopy-limit). The graded split-proconstant
calculation and kernel/cone theorem give precisely the required nilpotent tower
calculation, so that step does not need the general derived tower machinery.
The module remains transitively imported through KoszulQuotientLimit and
KoszulQuotientConeIsIso. This removes a direct import, not a module from the
item's import closure; no global module pruning is claimed.

Removed from the item the direct proof imports
Sheaf.Paper.StrictPerfectCoefficientPackage,
Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact, and
WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts. These are retained
in KoszulCompletionScalarComparison and are not globally pruned dependencies.
Removed the redundant direct import Sheaf.Paper.IntrinsicKoszulCompletion; it is
still used through the comparison and nilpotent modules.

Replaced public import Sheaf.Paper.CompletionMap with public import
Sheaf.Paper.AdicReductionAdjunction. Moved the public Mathlib ExactFunctor import
and the proof imports Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction,
Sheaf.Algebra.Homology.DerivedChangeOfRingsGeneral and
Sheaf.Algebra.Homology.KFlatResolutionGeneral to the extracted adjunction module.
Those modules remain required there; this is relocation, not global pruning.
Removed the obsolete local disabling of scalarReductionSiteSmall in three
remaining proofs, since the proof-only adjunction import no longer exports that
instance into the item. Its disabling remains where needed in the extracted API.

No blueprint unit statement or realized unit proof step was bypassed. No existing
module is withdrawn. New private helpers have no unproved declarations.

## Where the brief, the DAG or earlier work was wrong

The declared ingredients did not yet state the concrete perfect-scalar Koszul
comparison or the nilpotent-unit interface required by the main proof. In
particular, exact countable products and a strict-perfect coefficient package
are ingredients, not that comparison itself. These gaps are now explicit nodes.
The general ringed strict-tower theorem was unnecessary for the concrete graded
calculation. The source theorem isLimit_fan_whiskerRight_quot in
WeilConjectures.CategoryTheory.DerivedCategory.Complete.TensorQuotPow assumes
a principal ideal generated by a nonzerodivisor and uses a different sheaf-module
presentation; those hypotheses are unavailable here. Its special-case proof
cannot close the scalar comparison unchanged. The existing
nonempty_koszulBaseChangeIso does supply its coefficient base-change step.
The signatures of the original statements, including all target signatures,
are unchanged. No false statement was found.

## New nodes

lem-weil-pbc-koszul-completion-scalar-comparison: the remaining perfect scalar
comparison and its canonical unit square. Source: the first part of the current
blueprint's adic-completion-reduction proof. It is independent of the nilpotence
calculation and does not require that its finite list generate the ideal.

lem-weil-pbc-nilpotent-koszul-completion-unit: the proved nilpotent-completion
unit theorem, from the graded splitting and the kernel/cone quasi-isomorphism.

lem-weil-pbc-nilpotent-koszul-graded-tower: the proved degreewise splitting and
uniform transition-factorization formula. Its retractions are explicitly graded
maps, not falsely asserted to be chain maps.

Updated the restricted-comparison node's proof and dependencies to the actual
three-step proof; updated the adjunction node's Lean attachment to its new home.
The existing overall node retains the declarations still in the item module.
Change record: coord/changes/B3-adic-reduction-adjunction.md.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
