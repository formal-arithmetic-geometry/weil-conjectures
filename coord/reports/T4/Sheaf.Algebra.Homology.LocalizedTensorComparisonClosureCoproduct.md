## What changed

Retired Sheaf.Algebra.Homology.LocalizedTensorComparisonClosureCoproduct in favor
of its adopted source twin. Reattached both coproduct-closure DAG nodes to the
existing source declarations, recording their verbatim signatures. The only
signature difference is removal of the unused hC flatness assumption in the
source. The mathematical node statements and all proof dependencies remain.
No source-library file or target changes.

Validation through lcompile.py: the original duplicate compiled cleanly (9.4 s),
the unchanged adopted source twin compiled (15.3 s), the unchanged closure
consumer compiled (2.8 s), and scratch-only proofs of both original signatures
from the stronger source API compiled (5.1 s). The two source declarations have
exactly the permitted axioms propext, Classical.choice and Quot.sound. The
scratch checks are outside the delivered lean tree.

Change record: coord/changes/T4-localized-tensor-coproduct-retirement.md.

## Proved and sorry left

Closed 0 of 0 local holes; added 0 holes; split off 0. This is retirement of an
already proved duplicate, not new proof work. No sorry is left or introduced.
The existing source supplies ModuleCat.localizedTensorComparisonProperty_closure_coproducts
and ModuleCat.localizedTensorComparisonProperty_closure_coproducts_fixed_degree.

## No longer needed

Withdrawn module: Sheaf.Algebra.Homology.LocalizedTensorComparisonClosureCoproduct.
Removed with the duplicate: public imports
WeilConjectures.Algebra.Homology.LocalizedTensorComparisonProperty and
Mathlib.RingTheory.Flat.Basic; proof imports
WeilConjectures.Algebra.Homology.LocalizedTensorComparisonDirectSumSquare,
WeilConjectures.Algebra.Homology.LocalizedTensorComparisonRepresentativeSquare,
WeilConjectures.CategoryTheory.DerivedModuleDirectSums,
WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution, and
WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat.
Its proved private helpers acyclic_coproduct, kFlat_coproduct and
exists_kFlat_representative disappear as well; their source versions remain.
No other module currently imports it, including in quarantine. Its former
consumer, WeilConjectures.Algebra.Homology.LocalizedTensorComparisonClosure,
already imports the source twin and omits hC at the coproduct application.
The DAG parent and fixed-degree node still need the same mathematical results,
now provided by the source attachments. The source still uses the direct-sum
square, representative square, derived module direct sums, flat resolutions,
and K-flat API: none of their nodes or modules is claimed globally pruned.
The unit has no realization requiring this particular Sheaf module, and no
unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The generic repeated-splitting brief does not describe the current item: the
live module has zero holes and coord/retire-items.tsv assigns its retirement.
The old node attachments still named the duplicate. The source twin has an
identical proof and identical remaining binders, with only hC dropped. Both
node statements therefore remain true unchanged, including empty coproducts,
zero rings, arbitrary degrees and unbounded complexes. The original Sheaf
module compiled cleanly before withdrawal. Source-library search found the
stronger existing results; LeanFinder found only general localization/tensor
facts, and Loogle found Sigma.map and its isomorphism-preservation API.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
