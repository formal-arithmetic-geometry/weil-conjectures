## What changed

Completed `AlgebraicGeometry.Scheme.Modules.exists_finitePresentation_affine_replacement`
in `Sheaf.AlgebraicGeometry.ModuleFinitePresentationAffineReplacement`. Its signature and
public imports are unchanged. The earlier attempt is simplified using the now-compiled
`exists_finiteType_affine_generators`: choose a finite free map to H on V that is epi
on the overlap, rather than first capturing a finite-type target and generating it globally.
The remaining proof makes the restricted kernel finite type, captures its relations, and
constructs the required finitely presented cokernel. Cokernel uniqueness proves the overlap
isomorphism. This follows the affine construction in Stacks 01PI, read at
https://stacks.math.columbia.edu/tag/01PI; the unit sk-thm-p1 realization is unchanged.

Added proof-only imports of ModuleFiniteTypeAffineGenerators, ModuleFiniteTypeAffineCapture,
QuasiCoherentExtensionQcOpen, and CoherentKernelConditionRestriction. The latter two use
`import all` to reuse their proved private quasi-coherence and finite-type transport helpers.
Private helpers prove preservation of finite presentation, quasi-coherent and finite-type
kernel transport, finite presentation of finite free modules, and restriction limit
preservation. Three proved slice helpers are registered only as local instances, so
importers acquire no new global instances. No statement, definition, public import, or
other module is changed; no forced adaptation is required. The static preflight requires
a record for changed open/attribute commands:
`coord/changes/proof-elaboration-environment.md`. This documents only proof elaboration;
no public interface changes.
The existing node's proof, proof_deps, and proof_origin now describe the actual route.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.Modules.exists_finitePresentation_affine_replacement`
(node lem-weil-pbc-module-finite-presentation-affine-replacement).
No sorry remains in the item, no holes added, and no statements split off.
This is a complete proof from existing dependency declarations; any remaining sorries
in those dependencies stay with their own items. All private helpers are fully proved.

Edge cases: the finite generator family may have rank zero, the overlap may be empty,
and the scheme may be noncompact. Compactness is used only for the overlap and the
affine open; restriction, kernel, cokernel, and equivalence arguments do not require
nonemptiness or positive rank. The epimorphism is required only after restriction.

## No longer needed

Removed direct proof-only imports AffineFiniteTypeGeneratingSections and
ModuleFiniteTypeSubmoduleExtension, and their nodes
lem-weil-pbc-affine-finite-type-generating-sections and
lem-weil-pbc-module-finite-type-submodule-extension from this node's proof dependencies.
No first finite-type capture or finite free epimorphism onto a captured target is needed.

Compared with the original item, these project modules are absent from this item's
import closure (other target branches may still need them):

- `Sheaf.AlgebraicGeometry.AffineFiniteTypeGeneratingSections`
- `Sheaf.AlgebraicGeometry.ModuleBinaryLocalProperties`
- `Sheaf.AlgebraicGeometry.ModuleFiniteTypeAffineEnlargement`
- `Sheaf.AlgebraicGeometry.ModuleFiniteTypeAffineUnion`
- `Sheaf.AlgebraicGeometry.ModuleFiniteTypeApproximation`
- `Sheaf.AlgebraicGeometry.ModuleFiniteTypeSubmoduleExtension`
- `Sheaf.AlgebraicGeometry.ModuleSubmoduleBinaryGluing`
- `Sheaf.AlgebraicGeometry.ModuleSubmoduleBinaryGluingCore`
- `Sheaf.AlgebraicGeometry.ModuleSubmoduleBinaryGluingProperties`
- `Sheaf.AlgebraicGeometry.ModuleSubmoduleBinaryGluingSecondRestriction`
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`
- `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechAcyclic`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`
- `WeilConjectures.AlgebraicGeometry.Modules.FaithfullyFlatDescent`
- `WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent`
- `WeilConjectures.AlgebraicGeometry.Modules.FpqcFullyFaithful`
- `WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine`
- `WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank`
- `WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde`
- `WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit`
- `WeilConjectures.AlgebraicGeometry.Modules.ZariskiDescent`
- `WeilConjectures.CategoryTheory.Abelian.DimensionShifting`
- `WeilConjectures.CategoryTheory.Sites.SigmaPresheaf`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Projective`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free`
- `WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Scheme`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc`
- `WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`
- `WeilConjectures.Mathlib.RingTheory.Filtration`
- `WeilConjectures.Mathlib.RingTheory.FinitePresentation`
- `WeilConjectures.Mathlib.RingTheory.Finiteness.Descent`
- `WeilConjectures.Mathlib.RingTheory.Flat.Localization`
- `WeilConjectures.Mathlib.RingTheory.Ideal.Operations`
- `WeilConjectures.Mathlib.RingTheory.Ideal.RegularPrincipal`
- `WeilConjectures.Mathlib.RingTheory.IsTensorProduct`
- `WeilConjectures.Mathlib.RingTheory.LocalRing.Basic`
- `WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Fiber`
- `WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.FreeLocus`
- `WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Noetherian`
- `WeilConjectures.Mathlib.RingTheory.TensorProduct.DirectLimitFG`
- `WeilConjectures.RingTheory.FaithfullyFlat.FamilyDescent`
- `WeilConjectures.Topology.Sheaves.Cech`
- `WeilConjectures.Topology.Sheaves.CechCriterion`

The recorded nodes in those modules, pruned on this branch, are:

- `def-pc-euler-characteristic`
- `def-weil-pbc-module-binary-submodule-pullback`
- `def-weil-pbc-stein-factorization`
- `lem-galois-fpqc-family-descent-of-local-property`
- `lem-pc-affine-cech-complex`
- `lem-pc-affine-sections-finite-locally-free-criterion`
- `lem-pc-affine-vanishing`
- `lem-pc-finite-flat-affine-sections-projective`
- `lem-pc-scheme-connected-iff-idempotents`
- `lem-pc-topological-injective-cech-positive-exact`
- `lem-pc-topological-ses-cech-sections-surjective`
- `lem-weil-pbc-affine-finite-type-generating-sections`
- `lem-weil-pbc-finite-presentation-affine-sections`
- `lem-weil-pbc-flat-variant-local-criterion`
- `lem-weil-pbc-fpqc-family-descent-of-single-morphism-descent`
- `lem-weil-pbc-local-ring-idempotent-zero-one`
- `lem-weil-pbc-module-binary-local-properties`
- `lem-weil-pbc-module-binary-submodule-mono`
- `lem-weil-pbc-module-finite-type-affine-enlargement`
- `lem-weil-pbc-module-finite-type-affine-union`
- `lem-weil-pbc-module-finite-type-global-approximation`
- `lem-weil-pbc-module-finite-type-submodule-extension`
- `lem-weil-pbc-module-submodule-binary-gluing`
- `lem-weil-pbc-module-submodule-binary-gluing-restrictions`
- `lem-weil-pbc-module-submodule-binary-gluing-second-restriction`
- `lem-weil-pbc-noetherian-flat-locus-neighborhood`
- `lem-weil-pbc-pushforward-spec-global-sections`
- `lem-weil-pbc-quasi-coherent-finite-type-affine`
- `lem-weil-pbc-quasi-coherent-module-cokernel-image`

## Where the brief, the DAG or earlier work was wrong

The original mathematical plan works on the affine scheme V, but its global submodule
extension interface needs compactness of its ambient scheme. Affine capture supplies
the needed relations directly without a global finite-affine-cover induction.
The kernel lives on the slice site over V; extend it through 01PE(3) with its zero map
into H, then capture this ambient extension on the overlap. Only the returned restriction
isomorphism is needed. All objects are constructed inside the existential proof;
no public definition chooses arbitrary data from an unproved existence theorem.

The earlier attempt's local build lacked ModuleFiniteTypeAffineGenerators; it is now
available and gives the simpler proof. The inherited private slice instances were globally
registered despite being described as local; this attempt registers them locally.
The inherited generic change record was replaced by a precise record of the changed
open commands and local registrations, required by the static preflight. The first dry
run of this attempt passed compilation and the axiom probe, and requested that record
and the second reading. The latter is the independent reader's responsibility; the
worker dry-run tool permits that sole pending check. No second-reader section is written by this worker.

## Second reading by S3

1. Interface: compared the sole delivered module with the repository version. The existing
   theorem signature is byte-for-byte identical, as are its public imports and visibility.
   All added helpers are private proved theorems; no public definition is changed. The
   change record accurately documents only open commands and local instance attributes.
   Verdict: pass.
2. Proof: read the finite-generator, kernel, capture and cokernel construction, including
   each private transport helper. There is no sorry, axiom, unsafe, opaque, extern,
   implemented_by, or hollow definition in the delivered module. Local compilation and
   the explicit axiom probe are recorded below once completed. All existence choices are
   local to an existential proof; E is the categorical cokernel of the constructed map.
3. Split statements: none added. Checked the existing generator, affine capture and
   quasi-coherent extension interfaces and the finite-type kernel/cokernel applications.
   Empty overlap, zero rank, W empty, and noncompact X do not invalidate any step. Further
   grep, Loogle and LeanFinder searches found no direct replacement theorem; the proof
   already uses the standard cokernel uniqueness theorem returned by Loogle. Verdict: pass.
4. Route and pruning: read from the target down. The proof removes the unnecessary first
   capture of H and generates H directly on the overlap. Each direct proof import is used
   (the two import-all modules supply proved private transport helpers). Both old removed
   proof dependencies are listed under No longer needed. Checked every pruned node against
   all unit realized records: none realizes a unit statement or step. The sk-thm-p1 route
   is preserved. Checked the affine construction against Stacks 01PI. Verdict: pass.
5. Nodes: the sole node changes only proof, proof_deps and proof_origin. Its dependencies
   equal the union of uses in its proof steps and match the actual Lean argument; its
   statement, source, unit, chapter and Lean signature are unchanged. No new node is
   required because there is no split statement. Verdict: pass.

Second reading changes: appended this independent review and its validation evidence;
no Lean proof, import, signature, definition or node repair was needed.

Validation: a scratch copy of the complete candidate compiled locally with no warnings
(exit 0, 49.8 seconds). Its explicit `#print axioms` for
`AlgebraicGeometry.Scheme.Modules.exists_finitePresentation_affine_replacement` printed
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter comes from existing
open imported dependencies, not a hole in this delivery. This closes the item's one
syntactic hole without claiming that the target's full import closure is already proved.

The second-reader dry run returned OK: commit 23544d675b compiled and passed preflight.
The tool classified it CODEX because of the updated node, change record and local
open/attribute commands; the unchanged signature and absence of global registrations
were independently checked above.
