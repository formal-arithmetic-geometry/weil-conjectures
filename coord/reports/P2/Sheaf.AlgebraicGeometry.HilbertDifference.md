## What changed

`Sheaf.AlgebraicGeometry.HilbertDifference.hilbert_difference` is reduced to the
local kernel comparison from the affine argument of Stacks Divisors, Tag 02P2.
Its original signature and public imports are unchanged.

The new proved theorem `hilbert_denominator_maps` constructs the map out of
`idealModuleProduct` using the coimage/image isomorphism. The two kernel
inclusions give inverse maps between the two images, proving injectivity.
Cokernel preservation by tensoring and the stalk tensor comparison prove the
pointwise support bounds. This categorical argument avoids gluing chosen maps.

The main module proves quasi-coherence of the product as an image, coherence
of both cokernels, strict support-dimension drop, and the Euler difference for
all integer twists. Its private helpers derive finite presentation from
coherence, handle the successor isomorphism for positive and negative powers,
and specialize the existing four-term Euler identity to a monomorphism.
In particular, the case n = -1 uses the evaluation isomorphism and the negative
cases cancel a dual factor explicitly.

Only three Lean modules and their three DAG records are delivered. No existing
definition or theorem statement was changed; no change record or consumer
adaptation is needed. All source-library declarations are preserved.

The full sandbox compiled successfully after import pruning (main module 40.5 s,
maps module 11.9 s, kernel statement 0.2 s). Delivery performs the final compile
and preflight after removal of two redundant imports.

## Proved and sorry left

Original holes: one, `AlgebraicGeometry.Scheme.Modules.hilbert_difference`.
That declaration now has a complete Lean proof.

Added holes: one,
`AlgebraicGeometry.Scheme.Modules.hilbert_denominator_kernel_comparison`, in
`Sheaf.AlgebraicGeometry.HilbertDenominatorKernelComparison`, node
`lem-sc-hilbert-denominator-kernel-comparison`. Its entire proof is `by sorry`.
It states only that the two maps from I tensor F kill one another's kernels.
It has no properness, field, dimension, cokernel-coherence or Euler assertion.
This is the affine multiplication step of Tag 02P2, rather than the original
statement under another name.

The new `AlgebraicGeometry.Scheme.Modules.hilbert_denominator_maps` is proved
without an additional hole, from that comparison. Every private helper in
the packet is proved. The item module has zero holes; the packet has one.
Thus one upper hole is closed and one strictly narrower hole is added:
this is a decomposition, with zero net holes closed, not a completed proof
of the local meromorphic comparison.

The retained local work is precise: identify the actual pullback projection
on an affine trivialization with the denominator-module map characterized by
b sigma(z) = a z, and transfer that equality to tensor sections. The affine
lemma already supplies regularity and the injective module map, but it does
not state this sheaf/tensor comparison. The node and docstring give the
localization and affine-basis argument in full.

## No longer needed

The main module removes these original proof-only imports:

- `WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`:
  the proof constructs quasi-coherence through the kernel/cokernel description
  of an image. It never identifies product sections with an ideal multiple.
  The old direct dependency
  `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections` is removed, and that
  module is absent from this item's Lean import closure.
- `Sheaf.RingTheory.HilbertAffineDenominatorModule`: the main proof no longer
  invokes it directly. It remains a declared proof dependency of the new
  kernel-comparison node; its mathematics is still needed and is not withdrawn.
- `WeilConjectures.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact`:
  integer-twist additivity is obtained from the proved twisted Euler identity.
  The old direct node dependency `lem-sc-ext-tensor-exact` is removed. The source
  module remains in the transitive import closure and is not withdrawn.
- `WeilConjectures.AlgebraicGeometry.Cohomology.LongExact`: the proved four-term
  Euler identity supplies the arithmetic consequence. Euler additivity remains
  a proof dependency and this module remains imported transitively.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: supplied by the retained
  public imports. Its definition node and transitive imports remain needed.

Exploratory direct imports of `Modules.ProjectionFormula`,
`Modules.QuasicoherentCokernel`, `Cohomology.DirectImage.AffineMorphism`, and
`Algebra.Homology.ModuleStalkExact` were also removed. The first two are already
public dependencies of retained imports; the last two were unnecessary.

No Lean files or declarations are deleted. No global pruning claim is made
for a module that another target or an adopted source declaration still needs.

## Where the brief, the DAG or earlier work was wrong

The original natural-language route is mathematically sound. Its affine-module
lemma does not by itself give a morphism from the sheaf-theoretic image used by
`idealModuleProduct`; the projection/tensor comparison is an additional formal
step. That precise step is now the single retained kernel lemma. The rest of
the gluing and support argument has been replaced by a compiled categorical
proof, and the DAG records this route.

The no-embedded-primes condition was checked against the needed regularity:
full support and finite generation make the minimal associated primes the ring's
minimal primes; minimality among associated primes then excludes all embedded
ones. Nonzerodivisors consequently act regularly on the section module.
The kernel statement remains true on empty schemes, and zero chart modules
cause no exceptional case. For the main theorem the original nonemptiness and
finite dimension hypotheses remain exactly as stated.

Four actual searches were made for the retained comparison and the image
assembly: LeanSearch, LeanFinder, Loogle and grep. LeanSearch found tensor-kernel
and categorical image lemmas, but neither new statement. LeanFinder found flat tensor kernel
lemmas, which require flatness not assumed here. Loogle found the coimage/image
isomorphism used in the proved assembly. The grep hits concerned analytic
meromorphic kernels. Blueprint searches for Tag 02P2, denominator and kernel
comparison found no duplicate of either new statement. The blueprint unit's
statement and route remain unchanged.

The first delivery preflight requested the missing LeanSearch category in both
new node records. Both searches were run and their actual results recorded.

Provider interruptions occasionally removed live tool sessions. Compiles were
rechecked using a sandbox log; no earlier delivery was attempted or repeated.

## New nodes

`lem-sc-hilbert-denominator-kernel-comparison`, module
`Sheaf.AlgebraicGeometry.HilbertDenominatorKernelComparison`, isolates the
local affine multiplication calculation of Tag 02P2 as the two zero kernel
composites. It is the one new hole and has its own complete source proof.
Its dependencies retain the existing affine denominator-module theorem.

`lem-sc-hilbert-denominator-maps`, module
`Sheaf.AlgebraicGeometry.HilbertDenominatorMaps`, states the canonical
monomorphism from the ideal-module product and the two pointwise cokernel
support implications. It is fully proved using the kernel comparison,
coimage/image factorization, tensor right exactness, and the tensor stalk
comparison. Neither new node repeats the coherence, dimension, or Euler
conclusion of the item.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
