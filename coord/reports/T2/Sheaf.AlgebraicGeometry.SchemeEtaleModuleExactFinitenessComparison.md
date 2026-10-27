## What changed

Replaced the proof of
`AlgebraicGeometry.Scheme.Modules.scheme_etale_module_exact_finiteness_comparison`.
Its signature, the canonical comparison abbreviation, and all existing public imports
are unchanged. No other existing Lean module is modified.

The ambient exactness clause is implemented from the existing comparison and flat
pullback theorems. The private, proved `comparison_mono` transports monomorphisms
through the natural tensor-section comparisons on every small-etale object. Flatness
preserves the original monomorphism under scheme pullback, and sectionwise evaluation
preserves it. Faithful forgetful functors reflect monomorphisms. The extension is an
additive left adjoint, so it preserves cokernels and epimorphisms. These facts give the
mapped short exact sequence by `ShortComplex.Exact.map_of_epi_of_preservesCokernel`.
This avoids constructing quasi-coherent kernels for the exactness argument.

The finiteness argument is reduced to two new source-backed steps in separate modules:
transporting finite generators/presentations forward, and recovering them on members
of an etale fpqc cover. The reverse finite-type implication then applies the existing
`isFiniteType_of_fpqc_tensorPullback`. The reverse finite-presentation implication
uses the generated covering sieve and the canonical descent datum of F with its
identity comparison in `isFinitePresentation_of_toDescentData_iso`. Thus the assembly
includes the descent argument; the local-recovery statement does not assume or assert
global reflection of finiteness.

Validation: `lcompile.py --all` compiled all three modules, with no errors or warnings:
local recovery 7.3 s, preservation 7.1 s, item 15.3 s. All lines are at most 100
characters. Every referenced DAG dependency exists. The statement checks include the
empty scheme/empty cover, zero module, and zero generator or relation ranks. The
local recovery families have an arbitrary index in Type (u+1), the small-etale site's
object universe; no finite global atlas or Noetherian assumption was introduced.

## Proved and sorry left

Original item: one hole in
`AlgebraicGeometry.Scheme.Modules.scheme_etale_module_exact_finiteness_comparison`.
Its proof is now complete Lean from the named declarations, and the item has zero
remaining direct holes. The private `comparison_mono` is proved without a new hole;
the ambient exactness clause uses no new unproved statement.

Two holes are added, each the entire proof of one public theorem in its own module:

- `AlgebraicGeometry.Scheme.Modules.zariskiEtale_finiteness_preservation`, node
  `lem-sfb-zariski-etale-finiteness-preservation`.
- `AlgebraicGeometry.Scheme.Modules.zariskiEtale_finiteness_local_recovery`, node
  `lem-sfb-zariski-etale-finiteness-local-recovery`.

This is a decomposition of the original combined theorem, not a complete proof of
its finiteness assertions. Counts: one original hole replaced, two split off,
zero direct holes left in the item, two in the delivery, net minus one hole closed.
The pre-existing comparison and fpqc finite-type descent declarations may themselves
use sorry; they are the existing stated dependencies prescribed by this stage.

## No longer needed

Removed the following private proof imports from the item:

- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`: the specified
  context already supplies its adjunction.
- `WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`:
  ambient right exactness follows directly from the left adjunction. The local
  recovery node still needs the quasi-coherent-cokernel result.
- `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`:
  exactness is proved using monomorphisms and preserved cokernels.
- `Sheaf.AlgebraicGeometry.GlobalSectionsLeftExact`: the proof uses Mathlib's
  limit-preserving `toPresheaf` and component evaluation directly.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`: replaced by the functor-category
  mono API import; the public statement dependencies already expose module limits.
- `WeilConjectures.AlgebraicGeometry.TensorPullback` and
  `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`: the former is already
  exposed by statement dependencies and no direct tilde calculation is used.
- `Sheaf.AlgebraicGeometry.FpqcFinerThanEtale`: the local-recovery helper supplies
  precoverage membership; its node retains the etale-to-fpqc dependency.

The item's direct DAG proof dependencies and top-level tool-use list no longer
include `lem-weil-pbc-ringed-topoi-module-adjunction`,
`lem-weil-pbc-quasi-coherent-module-cokernel-image`,
`lem-weil-pbc-quasi-coherent-module-kernel`, `lem-sc-global-sections-left-exact`,
`lem-pc-module-pullback-identity-composition`,
`lem-weil-pbc-module-pullback-quasi-coherent`,
`lem-weil-pbc-fpqc-finer-than-etale`, or
`lem-weil-pbc-etale-composition-cancellation`. Presentation transport/recovery keeps
its own needed dependencies. No global module withdrawal or claim that these modules
leave the entire targets' closure is made; existing comparison dependencies also
continue to use some of them. No source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original exactness plan is longer than necessary:
right exactness plus preservation of monomorphisms suffices, so an explicit ambient
kernel comparison and a quasi-coherent-kernel theorem are unnecessary here.

The original recorded declarations do not directly provide the finite local
presentation transport/lifting interface for this theorem. The two new statements
make those genuine steps of the original argument explicit. Their docstrings give
complete proofs following descent.tex, Tag 05VG. Source Tag 06VE parts (3)-(5) and
Tag 05VG were read, including their proofs. Searches used LeanSearch, Loogle,
LeanFinder and grep, with actual queries recorded in searches.jsonl; the results
provided the site finiteness definitions and ring tensor finiteness, not either
comparison step. The existing `etaleExtension_free_presentations_hom` supplies
arbitrary free presentations and Hom comparison, and
`etalePresentedModule_effectiveRecovery` concerns effective module recovery;
neither states finite-generator/relation transport for a specified F. The existing
etale-neighbourhood finite-presentation theorem concerns scheme-module pullback,
not finiteness of its small-etale associated module.

The inherited blueprint provenance has from.node=null, as reported by
`blueprint_refs.py ancestor`. The new nodes preserve that provenance and extend its
via chain, rather than invent a blueprint ancestor. The unit record is unchanged;
its realized arrays do not attach this supporting comparison to a unit statement or
step. The source argument and unit route are preserved.

## New nodes

`lem-sfb-zariski-etale-finiteness-preservation` is in
`dag/nodes/sec-six-functors-basics/` and realizes the original node's step 3. Its Lean
module is `Sheaf.AlgebraicGeometry.ZariskiEtaleFinitenessPreservation`. It asserts only
the two forward finiteness implications for canonical tensor extension. The proof is
local finite free presentation transport, with no global reflection or exactness
assertion.

`lem-sfb-zariski-etale-finiteness-local-recovery` is in the same node directory. Its
Lean module is `Sheaf.AlgebraicGeometry.ZariskiEtaleFinitenessLocalRecovery`. It
realizes the original step 4 and the covering-identification part of step 5, stopping
before global finiteness descent. It produces etale fpqc families on which the
Zariski pullbacks have finite type or finite presentation. The item performs the
remaining descent. Tensor and ordinary pullback in its two clauses match the
interfaces of the existing descent theorems and are canonically isomorphic.

No change record is needed: no existing signature, definition, instance, attribute
or public import was changed.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
