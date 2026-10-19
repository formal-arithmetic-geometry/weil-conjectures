## What changed

Restored `SheafOfModules.isFlat_iff_local_equationalCriterion` with exactly the
`IsSiteForCoverings` / `IsFlatOnSite` statement in the current DAG Lean record.
The old source contained a different, commented-out `IsFlat` statement and a
private proof chain. The new proof specializes the existing fully proved
`isFlatOnSite_iff_local_equationalCriterion` and converts covering sieves to
covering presieves and back. The refinement lemma is proved by induction on
`Precoverage.Saturate`; the reverse direction explicitly restricts each matrix
factorization along a further arrow. No mathematical statement or target changes.

Public imports now provide the actual statement dependencies, including
`SiteCoveringAxioms` and `FlatOnSite`. The general criterion is a proof-only import.
`Grp.FilteredColimits` is retained: its instances are needed to elaborate
the small-site sheafification assumptions in the flatness predicate.
The node's proof, proof dependencies and Lean attachment follow this proof.
Change record: `coord/changes/M5-flat-equational-criterion-restore.md`.

## Proved and sorry left

Proved `SheafOfModules.isFlat_iff_local_equationalCriterion` (node
`lem-weil-pbc-site-flat-equational-criterion`) and the private
`SheafOfModules.covering_presieve_refinement` helper.

The baseline has one active hole: private `SheafOfModules.finite_tensor_relation`.
That hole is removed by pruning its entire unused private argument, not by
retaining and proving that declaration. Thus one old hole disappears, zero holes
are added, zero are split off, and zero remain in the delivered module. The
previously commented-out main criterion is restored as a proved theorem.
The general criterion and its finite tensor-witness dependency already have
complete proofs; this delivery introduces no assumed results.

Validation: the restored module compiled cleanly in 5.0 seconds. Its three
unchanged direct importers (`FlatFinitePresentationRetract`,
`SmallFlatSubextension`, `SmallFlatSubsheaf`) compiled cleanly against it in
3.5, 3.3, and 2.6 seconds. The unchanged consumer copies were removed from
the sandbox after this check; only the assigned module is delivered.
`#print axioms SheafOfModules.isFlat_iff_local_equationalCriterion` reports
exactly `[propext, Classical.choice, Quot.sound]`; the restored theorem's full
imported proof has no `sorryAx`. The signature check prints the intended
single common universe and no extra sheafification-instance hypotheses.

## No longer needed

The old local proof chain is unnecessary: `finite_tensor_relation`,
`tensor_presheaf_mono`, `coefficientIdeal`, `flat_global_coefficients`,
`flat_equational_forward`, `local_matrix`, `local_tensor_kernel`, and the
commented `tensor_mono_of_local_matrix`. Its private local monoidal instances
are also removed. Reusing the existing general theorem avoids duplicating
its finite-matrix and tensor calculations.

Removed imports:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule`
- `Mathlib.Algebra.Homology.ShortComplex.ExactFunctor`
- `Mathlib.CategoryTheory.Monoidal.Closed.Braided`
- `Mathlib.LinearAlgebra.TensorProduct.Vanishing`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat`

`FlatOnSite` becomes a public statement import instead of a proof import.
The old node dependencies `lem-weil-pbc-slice-restriction-flat`,
`def-pur-localized-ringed-site`, and `lem-weil-pbc-tensor-right-exact` are no
longer direct dependencies of this proof. The definitions
`def-weil-sheaf-of-modules-category` and `def-pc-flat-sheaf-modules` remain
statement dependencies. This does not assert that these modules disappear
from every other target import path. No blueprint unit statement or step is
bypassed: this remains the same Tag 08FC criterion in `sk-thm-properbasechange`.

## Where the brief, the DAG or earlier work was wrong

The source and the node disagreed. The node already records the later
`IsFlatOnSite` theorem with `IsSiteForCoverings`, but the source still contained
the earlier monoidal `IsFlat` theorem as a comment. Return P2 of 2026-10-16
lists the two commented declarations and the private algebraic hole.
The corresponding upstream APIs have since been restored: uncommenting the
old proof compiled, apart from the existing private hole. A shorter and more
appropriate repair is to restore the node's intended interface using the
already proved independent-universe criterion. No stronger covering-composition
or global pullback assumptions are needed.

Source read: Stacks `sites-modules.tex`, lemma-flat-eq (08FC), including its
ideal proof, finite-matrix induction and local tensor argument. Existing
library proof read: `FlatEquationalCriterionOfUniverses` and its tensor-witness
input `FlatLocalRelationsOfUniverses`. The refinement helper follows the
already proved private helper in
`PerfectConstantLocalLift` without importing that unrelated module.
The proof handles n = 0, an empty
factorization, empty covers, and the zero ring/module without additional
assumptions. Covering pullbacks are chosen only as supplied by the actual site
axioms; repeated arrows do not force arbitrary indexed closure of coverings.

Searches: launcher LeanFinder returned ordinary tensor-vanishing lemmas;
Loogle's initial query was invalid and gives no absence evidence; launcher
grep found the ordinary module criterion. Direct source search found the
fully proved general sheaf criterion, which is reused here. A direct source
consumer scan found three importers and no active uses of the withdrawn theorem.

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
