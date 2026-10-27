## What changed

Extracted the existing public diagonal and coefficient interface into
`Sheaf.Paper.DiagonalTowerSystemInterface`, publicly re-exported by the original module.
This allows the three proof components to share their actual interface without an import cycle.
The existing relative Cartier criterion proves the diagonal ideal invertible, with explicit
finite/flat/finitely-presented witnesses after removal of unused proof imports.

Constructed the strict ordinary cokernel tower, its quotient transitions, and its unbounded
pointwise triangulated left derived functor in `DiagonalDerivedReductionExists`.
The proof uses flat-term resolutions and the exact scalar extension from Z to Z_l.
Multiplication by each positive prime power is monic on the supported integral source;
its derived single counit is therefore invertible. The original existence theorem then
constructs its one system Ext class by the inverse of the standard Ext/Hom equivalence.

`DiagonalReductionCompletion` proves the entire scalar and limit comparison: additive
maps out of a prime-power killed module are p-adic linear; its integral quotient therefore
has the same cokernel universal property. The quotient generators determine the natural
ordinary strict-tower comparison. Exact tower restriction has a derived right adjoint,
so it preserves the pointwise Kan extension defining the left derived reduction.
Uniqueness gives the derived tower comparison. K-injective resolutions construct both
total right derived limits and the restriction comparison. Transporting the separate
integral reflector's unit and Hom bijection completes this theorem.

The remaining mathematical statements are the integral strict completion reflector and
the normalized strict Kummer calculation. Neither includes the other component or the
construction and scalar comparisons proved in this packet.
The change record is `coord/changes/diagonal-tower-system-interface.md`.

The derived restriction and Kan-extension comparison are proved with generic private
lemmas in the same completion module, before specialization to sheaves. Profiling
identified the earlier specialized derived-adjunction kernel conversion as the main
compile cost; the generic proof checked cleanly in 21.3 seconds. The ordinary
p-adic quotient construction is unchanged.

The named sheaf Abelian structures now explicitly use the sectionwise
full-subcategory preadditive structure, with the other Abelian fields inherited.
Local irreducibility attributes keep the already constructed coefficient functors and
Cartier maps folded when the geometric predicate is elaborated. They do not change
the definitions or export global transparency changes.

The integral boundary source transport and the finite exact-functor Ext image are
also factored through generic definitions containing the same operations. No file or proof
is split for performance. The original boundary is definitionally equal.

The cycle specification is factored through a generic boundary predicate to avoid
repeated elaboration of geometric finite endpoints. `normalizedBoundarySystem_iff_target`
proves the equivalence by the injective Ext/Hom correspondence, including existence of
the same system class and its full transported finite-class equation. The source and
roots normalizations are retained. Independent review of this definition repair is needed.

Validation: the main existence signature is textually unchanged up to whitespace.
The interface and all proof components have clean individual lcompile checks.
The final combined check timed out at the interface; the delivery tool supplies
the authoritative packet compilation and preflight. The generic completion comparison checked in 21.3 seconds.
The unchanged consumers `DiagonalCoefficientUniformizerReduction`,
`DiagonalNonTorsionBaseChange`, `DiagonalTowerTrace`, `RationalP1KernelContractions`,
`TowerClassDiagonal`, and `DiagonalTowerCoefficients` checked without Lean errors.
The consumer batch and a focused retry both timed out at the unchanged
`DiagonalTowerLimit`, without a Lean error. `RationalP1Triangle` and
`DiagonalTowerTraceLimit` are being checked separately. No consumer adaptation is included.
The downstream statement audit and the generic predicate equivalence preserve their
mathematical meaning; the definition repair needs independent review.

## Proved and sorry left

Closed the original body hole of
`AlgebraicGeometry.ProEtale.exists_diagonalTowerSystem` (1 original hole).
The new public theorem `AlgebraicGeometry.ProEtale.exists_diagonalDerivedReduction`
is completely proved, node `lem-sfb-diagonal-derived-reduction-exists`.
`AlgebraicGeometry.ProEtale.diagonal_reduction_completion` has a complete combining
proof from the integral reflector, node `lem-sfb-diagonal-reduction-completion`.
`normalizedBoundarySystem_iff_target` is proved without additional theorem holes.

Two public theorem holes remain in the packet, each with an exact `:= by sorry` body:

- `AlgebraicGeometry.ProEtale.integral_strict_completion_reflector`, in
  `Sheaf.Paper.IntegralStrictCompletionReflector`, node
  `lem-sfb-integral-strict-completion-reflector`.
- `AlgebraicGeometry.ProEtale.diagonal_kummer_reduction`, in
  `Sheaf.Paper.DiagonalKummerReduction`, node `lem-sfb-diagonal-kummer-reduction`.

Thus 1 upper hole is closed and 2 lower holes are added: this is a decomposition,
with net -1 holes before the ledger's closure/import accounting. No definition or
private helper has a hole. Each lower result is strictly a component of the original
argument: integral completion has no p-adic scalar extension, diagonal or cycle class;
Kummer calculation assumes the
already supplied derived reduction and source isomorphism and asserts no completion.

## No longer needed

The following old proof imports are removed from the packet's direct imports.
They can still occur transitively in the library; this list does not assert withdrawal
of any upstream declaration or pruning of any module still needed elsewhere.

- `Sheaf.Paper.ConstantCompletionEquivalence` (explored, but not retained).
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`.
- `Sheaf.Algebra.Homology.KFlat`.
- `Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`.
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`.
- `Sheaf.Paper.PurTwistSheafLocallyFree`.
- `Sheaf.Paper.DivisibleExtensionDerivedReduction`.
- `Sheaf.Paper.CompletedPullbackAdjunction`.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FreeSheafFlat`.
- `Sheaf.CategoryTheory.SiteInverseImageTensor`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`.
- `Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck`.
- `WeilConjectures.SixFunctors.Finite.Stalk`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`.
- `Sheaf.Paper.ProEtaleTateTwistsOfUniverses`.

The original module also drops its seven redundant direct public imports; they remain
public imports of the re-exported interface, so the public import closure is preserved:
`Sheaf.AlgebraicGeometry.CartierReductionSiteComparison`, `Sheaf.Paper.ProEtaleTateTwists`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`,
`Mathlib.Algebra.Category.Grp.ZModuleEquivalence`, `Mathlib.NumberTheory.Padics.RingHoms`,
`Mathlib.CategoryTheory.Abelian.FunctorCategory`, and `Mathlib.CategoryTheory.Sites.Adjunction`.
The explored `WeilConjectures.Algebra.Module.PadicTorsionLinear` import is also removed;
the proof needs its source approximation congruence, already in the public Padic import.

The main node now uses the explicit reduction construction and the two component nodes.
Its original proof dependencies removed at the upper level are:

- `def-kun-truncations`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `def-pc-kflat-complex`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `def-pur-roots-of-unity-sheaf`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `def-weil-abstract-derived-category`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `def-weil-pbc-site-comparison-morphism`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `def-weil-triangulated-category`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `lem-amb-kummer-any-base`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `lem-pc-kflat-resolution`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `lem-pur-derived-change-of-rings`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `lem-pur-kinjective-degreewise-existence`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `lem-pur-left-derived-from-kflat-class`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `lem-pur-ringed-site-grothendieck-abelian`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `lem-pur-twist-sheaf-locally-free`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `lem-sf-derived-ses-triangle`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `lem-sfb-divisible-extension-derived-reduction`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `lem-sp-completed-pullback-adjunction`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `lem-weil-pbc-comparison-pullback`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `lem-weil-pbc-derived-single-fully-faithful`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `lem-weil-pbc-etale-algebra-flat`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `lem-weil-pbc-free-sheaf-flat`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `lem-weil-pbc-functor-abelian-colimits`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `lem-weil-pbc-left-exact-site-inverse-image-tensor`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `lem-weil-pbc-pid-torsion-free-module-flat`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `lem-weil-pbc-proetale-ringed-open-closed`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `lem-weil-pbc-right-adjoint-preserves-kinjective`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `lem-weil-pbc-ringed-topoi-module-adjunction`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `lem-weil-pbc-small-module-diagrams-grothendieck`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `lemma-weil-pbc-finite-stalk-formula`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `lemma-weil-pbc-geometric-stalk-conservative`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `prop-weil-pbc-geometric-stalks-exact`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.
- `sk-def-sp-tate-twist`: its role is below the component result, or replaced by the explicit cokernel/resolving-class construction; it is not required as a direct dependency of the assembly proof.

The following old top-level tool-use approvals are removed from this upper proof node:

- `lem-pc-kflat-resolution`.
- `lem-pur-derived-change-of-rings`.
- `lem-pur-left-derived-from-kflat-class`.
- `lem-pur-ringed-site-grothendieck-abelian`.
- `lem-weil-pbc-functor-abelian-colimits`.
- `lem-weil-pbc-small-module-diagrams-grothendieck`.
- `lem-pur-kinjective-degreewise-existence`.
- `lem-weil-pbc-right-adjoint-preserves-kinjective`.
- `lem-sp-completed-pullback-adjunction`.
- `lem-weil-pbc-pid-torsion-free-module-flat`.
- `lem-weil-pbc-free-sheaf-flat`.
- `lem-weil-pbc-ringed-topoi-module-adjunction`.
- `lem-weil-pbc-proetale-ringed-open-closed`.
- `lem-weil-pbc-comparison-pullback`.
- `prop-weil-pbc-geometric-stalks-exact`.
- `lemma-weil-pbc-geometric-stalk-conservative`.
- `lem-weil-pbc-etale-algebra-flat`.
- `lem-weil-pbc-left-exact-site-inverse-image-tensor`.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
- `lem-amb-kummer-any-base`.
- `lem-pur-twist-sheaf-locally-free`.
- `lemma-weil-pbc-finite-stalk-formula`.

No module is withdrawn. The blueprint unit statement and its numbered route are retained.
The interface remains public through the original module; source-tree signatures and
public imports are unchanged.

## Where the brief, the DAG or earlier work was wrong

The ordinary reduction must be constructed as one strict cokernel tower; independent
level choices would not establish the system claim. The source monomorphism proof
must use the specified ULift integer constant explicitly, rather than identifying it
by definitional equality with an inferred tensor unit. The full residue-linear finite
Cartier class is retained, as required; equality of underlying Chern composites alone
would not prove the asserted level equation.

The current shared source is present and is the basis of this packet. No current
rework row or return for this item was found. Nothing is deleted from the library.
No mathematical statement is disputed and no target binder is changed.

## New nodes

`lem-sfb-diagonal-derived-reduction-exists`: explicit strict ordinary quotients and
an everywhere-defined pointwise triangulated derived reduction, computed on complexes
with monic prime-power multiplication. Its proof is complete.

`lem-sfb-diagonal-reduction-completion`: the completion and scalar-forgetting part
of original step 4, including both universal total derived limits and the reflector
unit. Its proof is complete from the integral reflector; the scalar, tower,
and total derived-limit comparisons are proved in this module.

`lem-sfb-diagonal-kummer-reduction`: original steps 5--7, including strict roots
tower transitions, quotient and Kummer normalizations, and equality of the full
finite Cartier classes. Its public theorem remains a hole.

`lem-sfb-integral-strict-completion-reflector`: the integral core of original step 4.
It assumes the integral reduction and the universal total derived inverse limit and
asserts the natural orthogonal-reflector unit. It has no p-adic scalar extension or
Cartier data. Its public theorem remains a hole, with the constant-ring/Koszul proof
spelled out and its declarations identified.

The existing interface node is reattached to its extracted module. The existing
existence node's proof, dependencies and proof origin now describe the actual
assembly. Change record: `coord/changes/diagonal-tower-system-interface.md`.

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
