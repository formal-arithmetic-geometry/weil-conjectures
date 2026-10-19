## What changed

Proved the assigned open-direct-image theorem by a finite family of stalk-injective
adjunction units. For each point of U, give its closure the reduced induced structure,
restrict F to a dense lisse open, and shrink again to a nonempty normal open V. The
point is generic in its closure, so it belongs to V. The unit F → h_*h^*F for V → U
is injective on that point's geometric stalk by the adjunction triangle identity.
The scheme-theoretic image of V → X is integral, and V is open in it. Apply the
existing normal-open direct-image theorem there, then closed direct image to X.
The existing finite-selection theorem gives a finite product injection out of F.
Apply j_*, commute it with this finite product, and use constructibility of
subsheaves to finish. The theorem signature is unchanged. The stalk-injectivity calculation is categorical:
the triangle identity factors an isomorphism through the stalk map, hence that
map is monic. Finite biproduct setup is confined to the proof body; the interface
checker reports no public-interface changes.

The only delivered Lean module is the assigned module; its two private helpers
are fully proved. No definitions or existing public signatures change. Added proof
imports are `WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`,
`WeilConjectures.ConstructibleSheaf.Noetherian`,
`WeilConjectures.ConstructibleSheaf.Monoidal`,
`WeilConjectures.ConstructibleSheaf.ExtensionByZero`,
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`.
The DAG proof and dependencies now describe this route. In particular the existing
finite-selection node is used through its source-library module-sheaf version,
`Etale.exists_finset_mono_pi_lift`. The pullback-stalk node supplies the natural
isomorphism used in the triangle calculation. These are generic tools and change
no unit-level step. Additions to the maintainer-owned `tool_uses` list are left for
independent review.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_lowerStar_of_openImmersion_over_field`
(node `thm-fin-open-degree-zero`): 1 of 1 original holes closed, 0 added,
0 remaining in the delivered module. This is a proof from existing declarations, including the already stated
normal-open theorem; it does not claim that theorem's transitive dependencies are
sorry-free.

## No longer needed

The proof avoids ambient reduction, the nondense-open induction, and the supported
kernel/extension argument. The following original proof dependencies are not used:
`lem-weil-pbc-reduction-universal-homeomorphism`,
`thm-weil-pbc-universal-homeomorphism-invariance`,
`prop-weil-pbc-inverse-image-modules-exact`, `lem-fin-reduction-open-direct-image`,
`lem-weil-pbc-etale-constructible-surjective-pullback`,
`lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`,
`lem-weil-pbc-reduced-source-factors-through-closed-subscheme`,
`lem-weil-pbc-noetherian-finite-components`,
`lemma-weil-pbc-finite-stalk-formula`,
`lemma-weil-pbc-geometric-stalk-conservative`,
`lem-weil-pbc-closed-immersion-finite`, `lem-kun-open-immersion-restriction`, and
`lem-weil-pbc-inverse-image-stalk-germ`. The plain natural pullback-stalk
isomorphism suffices; germ compatibility is unnecessary. The constructible-complex
definition remains a statement dependency, without a separate proof step.
Some remain transitive inputs to dependencies elsewhere; this is pruning this
item's direct proof route, not an assertion that no target uses them.

Removed proof-only imports:
`Mathlib.AlgebraicGeometry.Morphisms.Finite`,
`WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism` (both copies),
`Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance`,
`WeilConjectures.ConstructibleSheaf.OpenClosed`,
`Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`,
`Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`,
`Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`,
`Sheaf.AlgebraicGeometry.ConstructibleSurjectivePullback`,
`WeilConjectures.ConstructibleSheaf.KernelCokernel`,
`Sheaf.AlgebraicGeometry.ConstructibleSubsheafNoetherian`,
`WeilConjectures.SixFunctors.Finite.Stalk`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`,
`WeilConjectures.ConstructibleSheaf.Pullback`,
`WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm` (both copies),
`Sheaf.AlgebraicGeometry.OpenImmersionRestriction`,
`WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`,
`Sheaf.SecSmoothPurity.FinReductionOpenDirectImage`,
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
The existing public header is retained. The reduced-closed-subscheme construction,
pullback, finite sums and subobjects are used through the existing source-library
interfaces now imported. In particular, the closed-image step uses
`IsConstructibleSheaf.lowerStar_of_isClosedImmersion_of_quasiCompact`, the
comparison uses `isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf`, and
the final subobject step uses `IsConstructibleSheaf.of_mono`. These are existing
source-library versions of the recorded dependencies. No new split module is needed. Removed obsolete top-level
`tool_uses` entries for ambient reduction, descent, exactness, the open counit,
reduced-source factorization, minimal closed subsets and germ compatibility;
retained the inverse-image, reduced-closure and constructible-subobject entries.

## Where the brief, the DAG or earlier work was wrong

The original plan is valid, but finite selection of stalk tests supplies a shorter
route to a monomorphism with constructible direct image. It eliminates the kernel
induction. The unit's realized routes do not list this node or its internal steps,
so no unit-level route is bypassed. The earlier sandbox-only generic-lisse split
was not needed and is not delivered.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
