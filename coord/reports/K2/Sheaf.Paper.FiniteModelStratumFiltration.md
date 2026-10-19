## What changed

Completed `AlgebraicGeometry.ProEtale.CondensedRing.exists_finiteModelStratumFiltration`
with its signature and all three existing definitions unchanged. The previous sandbox's
geometric argument is retained: use the proved Noetherian open-chain theorem, construct
reduced closed complements, factor reduced sources through the original strata, and
pull back their finite constant local models. Noetherianity supplies quasi-compactness.

Repaired the previous kernel timeout in finite-model pullback by abstracting the cover
and its component maps in a proved private helper before instantiating the pullback
cover. This prevents type checking beneath the module functors from unfolding the
whole cover construction. No limit was raised and no definition was weakened.

Completed the new `Sheaf.Paper.OpenFiltrationSuccessor` module. Its local quotient
proof uses the proved `open_cokernel_zero`, `supported_unit` and `closed_pull_open_zero`
helpers from `ContinuousConstructibleIntegralGluing` through proof-only `import all`.
The closed unit on the cokernel and the closed restriction of its projection are
natural isomorphisms. A proved generic adjunction helper transports this quotient
through restriction and exact extension by zero, proves counit compatibility by
uniqueness of left adjoints, and preserves the cokernel through both whiskering
functors. Thus the successor theorem itself is proved, rather than left as a split-off.
The main theorem uses counit compatibility to deduce monicity of the successor maps.

## Proved and sorry left

Closed the original 1 of 1 holes:
`AlgebraicGeometry.ProEtale.CondensedRing.exists_finiteModelStratumFiltration`
(node `lem-sfb-finite-model-stratum-filtration`).

Also proved the new theorem
`AlgebraicGeometry.ProEtale.CondensedRing.exists_openFiltrationSuccessor`
(node `lem-sfb-open-filtration-successor`). Added holes: 0. Remaining holes in the
delivery: 0. No definitions contain holes. The new helper theorem no longer needs
another session. Imported existing results retain their existing proof obligations.

The geometric filtration, reduced factorization, finite-model pullback, compactness,
endpoints, local natural quotient and generic adjunction-composition helpers compile.
On resuming after the provider interruption, `lcompile.py --all` passed again for
both retained modules (exit code 0). The current repository comparison confirms
that the existing definitions, public signatures and visibility are unchanged.
The fresh compilation in this delivery session passed both modules again without
diagnostics (1.2 and 1.4 seconds respectively). The completed downstream scan found
98 transitive importers and no uses of the changed module's four public names
outside the item itself; no consumer adaptation is necessary.
Delivery preflight also checks each module with its axiom probe.

## No longer needed

Removed `Sheaf.Topology.NoetherianGoodStratificationRefinement` and its dependency
`lem-sfb-noetherian-good-stratification-refinement`: the existing proved
`Topology.Stratification.exists_chain_opens` already puts each difference inside an
original stratum. A good refinement, closure order and linear extension are unnecessary.

Removed direct proof imports `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`,
`Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`,
`Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage`, and
`Mathlib.CategoryTheory.Adjunction.CompositionIso`. The direct sectionwise-module
localization comparison is replaced by the proved internal closed-support helpers.
Removed redundant proof import
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale` from the main module;
cover operations are already available from its other imports.

The original dependencies `def-sfb-finite-upper-star-monoidal`,
`def-sfb-module-linear-open-lower-shriek`,
`def-weil-pbc-internal-abelian-sheaf-module-equivalence`, and
`lem-weil-pbc-proetale-ringed-open-closed` are not directly used by this proof.
The module-upper-star, module-lower-star, open-lower-shriek and quasi-separatedness
notions remain in the statements or the available API. The alpha comparison,
pullback-composition and cover base-change facts remain used by model pullback.
Also removed the redundant direct proof imports
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal`,
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
the retained imports expose the required factorization and module pullback API.
No statement-level public imports were removed. Removed the obsolete ringed
localization entry from the item's top-level tool approvals; its other approvals stay.
This reports proof dependencies removed here, not global unreachability claims.

## Where the brief, the DAG or earlier work was wrong

The original good-refinement-and-ordering route was longer than necessary: the source
library already proves the required open chain by Noetherian induction. The preceding
attempt left the successor quotient as a hole; it can be proved from the existing
internal closed-support helpers without a new sectionwise-module comparison.
The two definitionally associated functor expressions must be compared by an explicit
associator in the final application; asking elaboration to infer that comparison
caused avoidable unfolding of the extension functor.

The unchanged theorem allows empty schemes, empty differences, equal successive
opens, zero coefficients, arbitrary nonreduced X, and torsion local models. The proof
adds no nonemptiness or reducedness hypothesis. For the local theorem W=V gives a
zero quotient, W empty gives the closed piece, and V empty makes all terms zero;
the uniform categorical argument handles these cases.

## New nodes

`lem-sfb-open-filtration-successor`, module `Sheaf.Paper.OpenFiltrationSuccessor`,
states and proves the natural quotient for one pair of nested opens and its closed
complement. Source: Stacks Tags 09AH and 03DI–03DJ, the categorical part of the
original filtration steps 5–7. It has no constructibility, Noetherianity, geometric
filtration or finite-model assertion, and contains no sorry. Blueprint ancestry was
checked with `tools/blueprint_refs.py ancestor`; the node belongs below
`lem-sfb-dc-hom-preserves`. The proved private helpers of
`ContinuousConstructibleIntegralGluing` are reused as generic tools; its integral-model
statement is not invoked. The existing public mathematical declarations are unchanged. Preflight requires
a scope-change record for the elaborator option and private smallness instance:
`coord/changes/finite-model-filtration-elaboration.md`. No consumer is adapted.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
