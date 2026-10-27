## What changed

Separated the ordinary action-preserving scalar comparison (Stacks 03EK) from the
flatness and total-derived comparison. The original theorem statement is unchanged.
The flatness proof transports exactness to the localization tensor and applies the
single-complex tensor isomorphisms. The derived proof uses the universal left-derived
comparison and evaluates its counit equation on the single complex. Invertibility on
flat objects follows from the existing model computation.

The unchanged ordinary definitions moved to FlatSingleScalarInterface to avoid an
import cycle with FlatSingleScalarOrdinaryComparison. The original module publicly
imports the interface. See coord/changes/D7-flat-single-scalar-interface.md.

## Proved and sorry left

The original hole in
SheafOfModules.FlatSingleScalar.flat_single_scalar_conventions is reduced to the
ordinary comparison. The new remaining hole is
SheafOfModules.FlatSingleScalar.ordinary_scalar_comparison, attached to
lem-sfb-ordinary-scalar-comparison. One hole is closed and one added: this is a
decomposition, with zero net holes closed. No definition contains sorry.

All three delivered modules compiled together through lcompile.py. The remaining
style warning in the final proof was replaced by the compiler's explicit simp list.

The private single_flat_kflat proves both K-flat predicates. The private
derived_compatible proves the universal derived comparison, its counit equation,
both flat degree-zero isomorphisms and the natural compatibility square.

## No longer needed

No module is withdrawn. The ordinary comparison retains the original balancing
coequalizer argument. No mathematical dependency of that argument is pruned.
The unused proof import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedTotalTensor
was removed. The proof import
Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions is also unnecessary:
Mathlib.CategoryTheory.Functor.Derived.LeftDerived supplies the universal comparison.
The proof no longer needs lem-weil-pbc-exact-functor-complex-cohomology (Mathlib
preservation of homology suffices), or lem-pur-derived-change-of-rings as an existence
theorem (the supplied cochain model already records the needed computation).
The exact-functor argument uses Mathlib's preservation of homology and
the existing single-complex tensor isomorphisms directly.

## Where the brief, the DAG or earlier work was wrong

The ordinary action identification was encoded in Identifications but had no
independent declaration asserting its existence. It is substantial underived
mathematics, separate from the exact tensor argument and derived uniqueness.
The new lemma exposes precisely that part of the original six-step proof.

Compilation repeatedly received exit code 124 (no answer from the compile server),
which supplies no diagnostic about Lean correctness. Retried through lcompile.py;
no launcher script or compilation limit was changed. The resumed dispatcher attempt
Sheaf.Paper.FlatSingleScalarConventions.1792729928 reset the reference start to
2026-10-23 04:32:08 UTC, although work and search records begin on 2026-10-22.
The budget metadata was left untouched.

## New nodes

lem-sfb-ordinary-scalar-comparison: ordinary action identification and the natural
comparison preserving the actual coequalizer projection on local pure tensors,
with no flatness assertion or derived comparison. Its proof is the original
steps 1 and 2, with the sectionwise action reconstruction spelled out.

def-sfb-flat-single-scalar-interface: attachment for the seven unchanged ordinary
definitions moved out of the original module. This is solely an import-cycle
separation; names, values, signatures and visibility are preserved.
Change record: coord/changes/D7-flat-single-scalar-interface.md.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
