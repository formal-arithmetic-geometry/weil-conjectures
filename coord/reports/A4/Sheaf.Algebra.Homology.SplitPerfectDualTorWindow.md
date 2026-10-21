## What changed

Proved `CategoryTheory.splitPerfect_dual_torWindow` in
`Sheaf.Algebra.Homology.SplitPerfectDualTorWindow`, with its existing signature.
The proof combines the declared finite-retract dual/exactness theorem, the signed
bounded-dual component theorem, the derived internal Hom representative comparison,
the bounded-flat K-flatness criterion, and the K-flat single-tensor comparison.
The package's finite products are converted to the existing free-sheaf coproducts
by finite biproducts and reindexing; flatness follows from the library's tensor-unit,
coproduct and retract lemmas. The dual splitting is composed explicitly with the
canonical projection isomorphisms. Homology vanishing is transported from a zero
term of the actual termwise tensor complex.

Added `Sheaf.Algebra.Homology.IndependentBoundedExactTermHom`, whose public theorem
`CategoryTheory.SplitPerfectHom.quasiIso_homComplex_map_of_bounded_exact_terms`
extends the existing bounded exact-term Hom argument to independent site-object,
site-morphism and coefficient universes. Its private helpers prove the one-degree
case and the natural split stupid-tail sequences; its final proof is finite-width
induction. The adopted source modules and their signatures are preserved.
Updated the item's proof route and added the helper's DAG node. The proof also imports
`TensorColimitsIndependentCoefficients` for its proved `siteSheafTensorRightIso`,
to transport categorical tensor exactness to the site-flatness predicate. This is
a generic comparison of the two recorded tensor spellings, not a different unit route.

The remote compiler checked the Hom module and the assigned module. The latter
check was clean in 24.9 seconds. After a later loaded-server compile exceeded
60 seconds for the Hom module, its product-splitting calculation was replaced by
a generic categorical product-splitting construction and `ShortComplex.Splitting.map`.
This keeps the module intact and avoids large Hom-specific rewrite terms.
The final delivery checks recompile both files.

## Proved and sorry left

Closed: `CategoryTheory.splitPerfect_dual_torWindow`
(`lem-sfb-split-perfect-dual-tor-window`), the item's only original hole.

Added holes: none. The independent-universe bounded exact-term Hom theorem and all
private helpers are proved. No `sorry` remains in either delivered module.

The declared dependencies `SheafOfModules.ringedSite_finite_retract_dual_exact`,
`CategoryTheory.RingedSiteBoundedDual.boundedDualComponents`, and
`SheafOfModules.ringed_kFlat_single_tensor_comparison` are used as existing stated
results, as intended by this stage; this delivery does not claim to close their holes.

## No longer needed

Removed the proof import
`WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso` from the item.
Its node `lem-pc-bounded-exact-term-hom-quasi-iso` is replaced in this proof's route
by the proved independent-universe extension; its obsolete top-level `tool_uses` entry
is removed. The original declaration remains
unchanged in the source library and may still be used elsewhere; no module is withdrawn.
The proof follows all other mathematical dependencies in the original plan.

The new helper does not need the original equal-universe proof's import
`Mathlib.Algebra.Category.Grp.FilteredColimits`: abelian sheafification is explicit
at the ambient universe. Its duplicate direct sheaf-Abelian import is also omitted,
since `RingedSiteModules` already exports that module.

## Where the brief, the DAG or earlier work was wrong

The planned bounded exact-term Hom dependency has `{C : Type u} [SmallCategory C]`
and coefficient sheaves in universe `u`. The item allows independent site-object,
site-morphism and coefficient universes, so that declaration cannot be directly
specialized to the item. The new proved extension supplies the same argument on
the original site, with no source-signature change or additional hypothesis on the item.

The finite-retract dependency is stated using free sheaves indexed by
`ULift (Fin n)`, whereas the package uses products indexed by `Fin n`.
The explicit finite-biproduct and reindexing isomorphism resolves this interface
mismatch. Zero ranks, zero sheaves and rings, empty sites, and empty support
intervals are included in these constructions; no positivity assumption was added.

## New nodes

`lem-sfb-independent-bounded-exact-term-hom` in
`dag/nodes/sec-six-functors-basics/`: the fully proved bounded-source exact-term
Hom comparison at independent universes. Its statement is a separate general tool
and only proves the quasi-isomorphism step of the assigned theorem. It leaves no
new hole, preserves the unit route, and uses the source library's proved long exact
homology sequence. Searches found the existing equal-universe argument but no
applicable independent-universe statement. No existing definition or statement is
changed. Remote preflight nevertheless requires a record for the scoped proof-instance
commands: `coord/changes/A4-split-perfect-dual-proof-instances.md` documents them
and the zero downstream Lean consumers. No forced adaptation is required.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
