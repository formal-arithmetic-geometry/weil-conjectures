## What changed

Replaced the original body of
`AlgebraicGeometry.Scheme.adicResidue_isZero_of_complete_residue` by the independent
Koszul argument, with its existing signature and docstring unchanged.

The proof chooses finite generators of J, identifies the actual completed kernel
on every slice by `flat_and_quotients`, constructs its generating sections, and
uses `CategoryTheory.ringedKoszulCompletionReflector` directly. It transfers
finite-stage acyclicity to acyclicity in the abelian category of strict towers by
exact jointly conservative evaluation. The computation comparison on the zero
K-injective complex proves that the presentation's actual total right derived
inverse limit sends a zero object to zero. The invertible reflector unit then
gives the original conclusion.

Added the proof imports `Sheaf.CategoryTheory.RingedKoszulCompletionReflector`,
`Sheaf.Algebra.Homology.FiniteKoszulResidueAcyclic`,
`Mathlib.CategoryTheory.Functor.ReflectsIso.Exact`,
`WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic`, and the private interface of
`Sheaf.Paper.ConstantCompletionEquivalence` (for its already proved generating
sections, slice-ideal and finite-span helpers).

The new module states precisely the remaining finite Koszul tensor calculation,
without any completeness assumption or inverse-limit conclusion. Its proof in
words follows Tags 0G1T/0G1U and includes replacement invariance and negative
Koszul self-duality. The existing and new DAG records follow this argument.
No definition, existing statement, target, source-library file or consumer changed.

Validation: `lcompile.py --all` compiled both files cleanly on the server, in
4.8 s for the finite-stage statement and 21.6 s for the item assembly. Both are
within the 60 s per-file limit. The item has zero holes and the new module one.

## Proved and sorry left

Closed the one original syntactic hole:
`AlgebraicGeometry.Scheme.adicResidue_isZero_of_complete_residue`
(node `lem-sfb-adic-residue-koszul-nakayama`). There are zero `sorry` occurrences
left in the item module.

Added one hole:
`CategoryTheory.finiteKoszulTensor_acyclic_of_residue`
(node `lem-sfb-finite-koszul-residue-acyclic`), in the new module
`Sheaf.Algebra.Homology.FiniteKoszulResidueAcyclic`.

This is a decomposition: one upper hole closed, one finite-stage hole added,
net zero holes closed. It is not a complete proof without additional holes.
The new obligation is strictly a part of the argument: it proves acyclicity of
a single finite negative Koszul tensor stage, with no derived completeness,
Noetherianity, or reconstruction hypothesis. For example the nonzero complex Z[1/p], with residue map Z -> Z/p,
has zero residue and zero finite Koszul tensors; it becomes zero
only if the separate completeness hypothesis and reflector argument apply.

## No longer needed

No existing import was removed and no module is withdrawn or globally pruned.
The public statement import remains unchanged.

The parent no longer directly uses the K-flat-resolution, K-flat change-of-rings,
tensor-cancellation, acyclic-K-flat tensor, ordered-Koszul torsion, bounded
Postnikov, or derived-change-of-rings nodes: these are dependencies of the finite
stage lemma and remain needed there. They have not been claimed as pruned.
The separate strict-tower homotopy-limit theorem need not be applied again:
its required derived-limit comparison and K-injective computation are fields of
the reflector's existing `RingedKoszulLimitPresentation`.

The specialized `wfCompletionReflector` module is not imported: the original
general ringed-site reflector retained under that node applies directly to the
coefficient-sized slice. The parent node continues to cite that reflector node.

## Where the brief, the DAG or earlier work was wrong

The DAG's attached specialized reflector declaration is unnecessary for the
actual coefficient-sized slice, which is small at its coefficient universe.
The general declaration `CategoryTheory.ringedKoszulCompletionReflector`,
publicly retained by the specialized module, fits directly. No interface repair
is needed.

The existing residue-conservativity/quotient-reconstruction route cannot close
this item independently: its import chain returns to this item. It was not used.
The original four mathematical steps are retained: kernel generation and the
reflector, finite-stage tensor vanishing, strict-tower vanishing, then the
invertible unit. The blueprint unit's route is unchanged.

## New nodes

`lem-sfb-finite-koszul-residue-acyclic` states the finite-stage Tag 0G1T
calculation from steps 2 and 3 of the original node. It applies to an arbitrary
ringed small site and a sectionwise-surjective residue map with kernel generated
by the specified finite global list. Each dual Koszul tensor stage is acyclic
when derived residue extension is zero. It does not assume completeness or
conclude that the original object is zero. Its proof records flat K-flat
replacement, balanced cancellation, the finite ideal-power filtration, bounded
Postnikov devissage, Koszul torsion/self-duality, and invariance on replacing the
input by a K-flat representative. LeanFinder, Loogle, Mathlib grep, and local
library/blueprint statement searches found no existing equivalent declaration.
No change record is required because no existing definition or statement changed.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
