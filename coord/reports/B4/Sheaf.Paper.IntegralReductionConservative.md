## What changed

Return repair (2026-10-16): import and reuse the existing proved private helpers
instead of proving them again. All ten helpers named in the return are removed
from `ConstructibleCokernelsExtensions`, along with eight associated copies. It
uses a proof-only `import all Sheaf.AlgebraicGeometry.CondensedConstructibleSerre`.
Its new generic finite-presentation cokernel and extension constructions remain.

A full independent run of `import_prune_check.py` on every delivered module found
further copies in three supporting modules. These are also repaired:

- `IntegralConstructibleNakayama` imports `ProEtaleAbelianClosedSupport` with
  `import all` and reuses `abDetectMaps`. Its copied instance and section-detection
  proof block are removed. It also imports `CondensedConstructibleSerre` with
  `import all` for local splitting and the regular-module inverse-image comparison.
- `IntegralScalarContractive` imports `CondensedFieldLfpLocalTriviality` with
  `import all` and reuses its coefficient-independent helpers. Its actual
  generalization from fields to totally disconnected coefficient rings remains.
- The never-landed `ProEtaleFreeEpiLocalSplitting` module is removed entirely.
  Both its callers apply the existing proved private theorem
  `AlgebraicGeometry.ProEtale.freeEpiLocalSplitting` directly. Its DAG node is
  retained and attached to that existing declaration, accessible via `import all`.

The assigned theorem's signature and original public coefficient import are unchanged.
Its proof takes a distinguished cone, makes it bounded constructible using weak
Serre closure, and observes that its derived reduction is zero. The coefficient
short exact sequence and K-flat tensor/cone comparison make multiplication by ℓ
invertible on the cone. Additivity transfers this to its cohomology modules;
internal constructible Nakayama makes them zero. Homology detects the zero derived
object, so the original morphism is invertible.

The seven retained new modules are `IntegralReductionScalar`,
`IntegralScalarContractive`, `IntegralFiniteFreeContractive`,
`IntegralConstructibleNakayama`, `ConstructibleCokernelsExtensions`,
`IntegralConstructibleSerre`, and `IntegralConstructibleKernels`. The last contains
the sole remaining hole. No field-specific Serre or local-freeness theorem, or public
closed-support theorem, is applied. The reused generic private helpers are proved.
All comparison, matrix and presentation data in the proofs are constructed explicitly.

No existing library module other than the assigned item is changed. No existing
statement or definition changes. Node proof records describe the actual imports
and helper reuse. No forced adaptations or change records are needed. The
earlier delivery's historical review is retained below; the fresh review is
recorded under `## Second reading by B4`.

## Proved and sorry left

Closed the assigned module's original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.integralReduction_reflects_isIso`.

These six retained new public theorems have complete Lean proofs without local holes:

- `AlgebraicGeometry.ProEtale.CondensedRing.integralReduction_isIso_nsmul_of_isZero`.
- `AlgebraicGeometry.ProEtale.CondensedRing.integralRegular_one_sub_nsmul_isIso`.
- `AlgebraicGeometry.ProEtale.CondensedRing.integralFiniteFree_one_sub_nsmul_isIso`.
- `AlgebraicGeometry.ProEtale.CondensedRing.integralConstructible_isZero_of_isIso_nsmul`.
- `AlgebraicGeometry.ProEtale.CondensedRing.constructible_cokernels_extensions`.
- `AlgebraicGeometry.ProEtale.CondensedRing.integralConstructible_serre`.

Exactly one added hole remains from the returned delivery:
`AlgebraicGeometry.ProEtale.CondensedRing.integralConstructible_kernels`, in
`Sheaf.Paper.IntegralConstructibleKernels`, node
`lem-weil-pbc-integral-constructible-kernels`. Its proof is exactly `by sorry`.
There are no other holes in the delivered files and none in definitions. This
repair adds no further hole. The deleted splitting module has no replacement hole;
its existing library theorem is proved.

The overall delivery is a decomposition: one original hole closed and one strictly
simpler hole added. The kernel, Serre and assigned theorems still depend on that
kernel hole; the other five supporting public theorems have no such dependency.
This does not claim the target is free of `sorryAx`.

The kernel remainder still needs comparison of local finite presentations with
finite constant integral models on a topologically noetherian scheme, followed by
kernel finiteness. Its docstring and node give the specialization argument and
continuous integral pivot operations. For a map between presented, possibly torsion
modules, diagonalize both the target relation matrix B and the augmented matrix
(F,-B); lift source relations to present the desired kernel from their kernels.
This avoids incorrectly treating torsion modules themselves as free. Coherence of
continuous section rings alone does not supply this comparison or justify kernel
restriction. Bhatt--Scholze Definition 6.8.10 and Proposition 6.8.11(1) are the source.

The proofs include empty schemes and strata, zero objects and rank-zero free modules.
The scalar reduction assertion permits unbounded complexes; the norm-one reciprocal
argument uses neither completeness nor finite dimensionality of the normed extension.
The assigned theorem keeps every original hypothesis and binder.

## No longer needed

The repair removes these ten flagged private copies from
`ConstructibleCokernelsExtensions`: `fp_cokernel_of_free`, `fp_comap`, `fp_map`,
`fp_of_comap`, `fp_of_iso`, `free_biprod`, `free_map`, `lfp_comap`, `lfp_of_comap`,
and `lfp_of_iso`. It additionally removes `fp_pullback`, `finiteFreeBiprodIso`,
`abUpperStarCompMonoidalInv`, `fp_pullback_comp_iff`, `lfp_pullback`,
`lfp_pullback_comp_iff`, `common_lfp_stratification`, and `free_pullback`.
All are replaced by reuse of the existing generic library helpers, with no wrappers.
Its direct imports of `WeilConjectures.ConstructibleSheaf.Refinement`,
`WeilConjectures.CategoryTheory.Monoidal.Conjugate`, and
`WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal` are removed.

From Nakayama the copies `abPreservesColimitsOfShape`, `abLocalVanish`,
`abDetectSections`, and `abDetectMaps` are removed. From the scalar module the
copies `CategoryTheory.pushforwardRingMonObj`, `absoluteProjection`,
`absoluteProjection_natural`, `isIso_of_affine_weaklyContractible`,
`pointComponentsEquiv_target`, `canonicalComponentArrow`, and
`canonicalComponentArrow_terminal` are removed. The unused CategoryTheory helper
section and its variables disappear as well.

`Sheaf.Paper.ProEtaleFreeEpiLocalSplitting` and all its copied helper declarations
are pruned entirely. Its private imports of `Mathlib.CategoryTheory.Sites.EpiMono`
and `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`
therefore disappear. Both callers remove their import of this new module. It was
never landed, so no library deletion or `deleted.txt` entry is required.

The original redundant proof import
`WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory` is removed from
the assigned item; its coefficient interface already imports that API publicly.
Two original planned proof nodes remain pruned:

- `lem-weil-pbc-integral-stratified-perfect-characterization`: a different completed
  category, stronger hypotheses and no compatible internal weak Serre interface.
- `lem-weil-pbc-nakayama-jacobson`: an ordinary module statement without the internal
  sheaf-module interface. The actual proof uses finite generators and matrix radicals.

`prop-weil-pbc-module-bounded-constructible-triangulated` remains needed through its
proved source-library instance. No unit statement or required realized step is bypassed.

Earlier import minimization retained in the delivery removed
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage` from the scalar module;
`Mathlib.CategoryTheory.Preadditive.Biproducts` and
`Mathlib.CategoryTheory.Endomorphism` from the matrix module; a redundant flat-model
import from derived scalar reduction; and direct pullback-basic, site-sheaf,
natural-isomorphism and locally-injective imports from Nakayama. It removed
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence` and
`Mathlib.CategoryTheory.Triangulated.Adjunction` from the assigned item, and
`Mathlib.CategoryTheory.Abelian.Refinements` from generic closure. The retained
imports supply those APIs. Explicit proof-only `import all` is used for private
helpers, without changing the public interfaces of importers.

The second reading removed `integralTestProjection` and
`integralTestProjection_natural`, reusing the existing `profiniteTestProjection`
and `profiniteTestProjection_natural` directly. It also removed the redundant imports
`WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant`,
`WeilConjectures.CategoryTheory.RingObjects.ContinuousMap`, and
`Sheaf.Paper.ProEtalePointComponentsMaps` from `IntegralScalarContractive`.

## Where the brief, the DAG or earlier work was wrong

The returned delivery and its earlier second reading overlooked private helper
duplicates already in the library. The fresh second reading also found the copied
projection construction and naturality proof under renamed identifiers, and removed them. The original return identified ten; an additional
scan found the same issue in Nakayama, scalar comparison and local splitting. The
repair reuses existing proofs, removes the copied blocks, and prunes the splitting
module instead of merely renaming any duplicate.

The integral stratified-perfect statement uses a different completed category and
stronger scheme hypotheses. Ordinary module Nakayama does not directly apply to
internal `Mod` objects. The actual internal arguments and the narrower kernel
remainder handle these interface mismatches.

Bhatt--Scholze Proposition 6.8.11(1) supplies Serre closure; part (3) supplies the
derived comparison. Definition 6.8.10 uses finite constant integral models, whereas
the library uses local finite presentations. Their comparison is real work, retained
explicitly in the kernel remainder, and does not follow from noetherianity alone.

Old-root pro-etale cover and stratum detection imports conflict with the actual
coefficient interface's finite-coefficient pushforward notation. The repair uses
the existing compatible abelian closed-support module's proved generic helpers;
no conflicting source-library module is changed.

An earlier concrete scalar reduction argument approached the time limit due to
coefficient-instance unfolding. Its generic private auxiliary is retained in the
same file. No file is split to evade the compilation limit.

## New nodes

`lem-weil-pbc-integral-constructible-kernels` records the sole remaining hole,
ordinary integral constructible kernel closure including its finite-model comparison.

`lem-weil-pbc-integral-constructible-serre` records the proved Serre conjunction
from that kernel assertion and generic cokernel/extension closure.

`lem-weil-pbc-constructible-cokernels-extensions` records the new generic closure
proof, using existing finite-presentation helpers and local splitting.

`lem-weil-pbc-proetale-free-epi-local-splitting` is retained and now attaches to the
existing proved private `AlgebraicGeometry.ProEtale.freeEpiLocalSplitting` in
`Sheaf.AlgebraicGeometry.CondensedConstructibleSerre`, accessed with `import all`.
Its formerly new module is unnecessary and removed from the sandbox.

`lem-weil-pbc-integral-reduction-scalar` records the unbounded derived scalar
assertion via the concrete coefficient sequence and K-flat cone comparison.

`lem-weil-pbc-integral-constructible-nakayama` records internal constructible
Nakayama using existing local splitting and abelian detection, and finite-free units.

`lem-weil-pbc-integral-finite-free-contractive` records the finite-free matrix
assertion via scalar units and Mathlib's matrix radical identity.

`lem-weil-pbc-integral-scalar-contractive` records the regular-module scalar assertion,
using existing generic comparison helpers and the constructed ring generalization.

All eight nodes inherit the assigned node's chapter and unit. Their Lean records
and proof dependencies describe the final proof. No change records are necessary.

## Earlier second reading (a previous round; superseded)

1. **Interfaces: pass.** Compared every delivered module with the shared repository.
   Only the assigned module already exists; its universes, variable binders, theorem
   signature and public coefficient import are unchanged, byte for byte. The other
   eight modules and their declarations are new. No definition, existing statement,
   target statement or other group's module is changed. No change record is needed.

2. **Proofs and axioms: pass, with the declared remainder.** Read all nine modules
   (2,366 lines before the documentation repair) and compiled the complete set locally
   through `lcompile.py --all`: all succeeded, without warnings, in 3.6–51.9 seconds
   per file. The only `sorry` is the body of the public named theorem
   `integralConstructible_kernels`; no definition contains a hole, and no prohibited
   declaration or kernel bypass occurs. Independently compiled a scratch module
   printing axioms of all nine public theorems: the seven complete supporting
   theorems use only `propext`, `Classical.choice`, `Quot.sound`; the kernel theorem,
   Serre theorem and assigned theorem additionally use `sorryAx`. The scratch file
   was removed. All comparison and presentation data in the proved modules are
   explicitly constructed; none is chosen from an unproved mere existence assertion.

3. **Split statements: pass after proof-plan repair.** There is one new open statement,
   integral constructible kernel closure, strictly narrower than derived conservativity.
   Its hypotheses concern precisely the continuous integral ring, not an arbitrary
   ring on a noetherian space. Checked empty schemes and strata, zero matrices, rank
   zero, and maps between finite torsion modules. The completed scalar assertions
   also include arbitrary normed extensions without an unjustified completeness
   assumption. Repeated searches with different words using LeanFinder, Loogle and
   `rg` on both Lean roots: ordinary finite-presentation kernel finiteness, classical
   constructible kernels and adic constructible kernels do not provide this internal
   continuous-coefficient interface. Search results are recorded in the kernel node.
   Read [Bhatt–Scholze, Definition 6.8.10 and Proposition 6.8.11](https://arxiv.org/pdf/1309.1198),
   pp. 60–61: its constant finite integral models require the comparison explicitly
   retained in this remainder. This comparison is not inferred just from scheme
   noetherianity. The remainder is not closeable by an existing lemma in a few minutes.

4. **Route and pruning: pass.** The actual proof starts at the assigned cone, uses the
   already proved weak Serre triangulated criterion, the two-term coefficient
   resolution and the proved internal Nakayama argument. It never replaces the
   integral internal module objects by an ordinary module without a comparison.
   The two removed planned dependencies are both listed under `No longer needed`;
   the weak Serre triangulated node is retained. Checked `sk-thm-properbasechange`'s
   `realized` statement and all three steps: none is bypassed or altered. Checked
   public versus private imports and searched public import chains for redundant
   direct imports. Public imports supply signatures or their required structures;
   the existing proof-only derived-category import is redundant through the public
   coefficient interface and is now explicitly reported as removed.

5. **DAG: pass after repair.** All nine attached Lean signatures occur verbatim in
   their modules. Each new node has the source, complete proof plan, three kinds of
   searches, creation and blueprint provenance, chapter, unit and Lean fields.
   For every node, `proof_deps` is exactly the union of the proof steps' `uses`.
   The assigned node describes the actual cone/scalar/Nakayama argument. Updated
   the kernel node's last step and proof origin to match its repaired docstring,
   and added the proved generic cokernel dependency used there. Its new private
   import records that dependency. There are no circular dependencies.

**Second-reading changes.** Corrected the omitted removed import in the pruning
report. Replaced the kernel remainder's compressed appeal to Smith data of a map
between possibly torsion modules by an explicit finite-presentation construction:
refine also for its constructible cokernel, lift a matrix F between presentations,
diagonalize B and the augmented free matrix (F,-B), and present the kernel from
the source relation module and ker B into ker(F,-B). Local lifts of the finitely
many relation columns supply the presentation map. This explains why torsion
causes no gap and avoids claiming that the given modules themselves are free.
Updated that node, its independent searches, and the proof-only import accordingly.
No completed proof or theorem signature needed a change. The delivery remains a
one-hole-for-one-hole decomposition, with seven new supporting theorems proved.

## Second reading by B4

1. **Interfaces: pass.** I compared the delivered assigned module byte for byte
   with the repository version. Its theorem binders, hypotheses, conclusion and
   public coefficient import are unchanged; only the proof and its proof-only
   imports changed. The seven supporting modules and their new declarations are
   confined to this delivery. No existing definition, target statement, or
   declaration held by another group was changed, and no change record is needed.

2. **Proofs and axioms: pass with the declared remainder.** I compiled all eight
   delivered modules with `lcompile.py --all`; every file compiled without errors
   or warnings, and each file stayed below the delivery time limit. The only
   `sorry` is the named theorem
   `AlgebraicGeometry.ProEtale.CondensedRing.integralConstructible_kernels` in
   `IntegralConstructibleKernels`; it is a public theorem with its source,
   natural-language proof plan, and node. No definition contains `sorry`, and I
   found no `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or kernel
   bypass. An independent scratch `#print axioms` probe confirms that the five
   supporting theorems for scalar reduction, regular and finite-free contractive
   maps, Nakayama, and cokernel/extension closure use only `propext`,
   `Classical.choice`, and `Quot.sound`. The kernel theorem, the Serre conjunction,
   and the assigned theorem additionally use `sorryAx` through the declared
   kernel remainder.

3. **Split statements: pass.** The sole open split is integral constructible
   kernel closure. It is strictly below conservativity: it states only closure of
   the concrete continuous integral internal modules under kernels, with the
   noetherian-space hypothesis. Its docstring and node give the finite-presentation
   comparison, torsion-safe augmented-matrix construction, and continuous pivot
   argument. I repeated searches with different phrases through LeanFinder,
   Loogle, and `rg`; no existing Mathlib, upstream, or Sheaf declaration supplies
   this internal coefficient-specific result. The edge cases of zero and
   rank-zero presentations, empty strata, and torsion modules are explicitly
   covered by the statement's proof plan.

4. **Route and pruning: pass.** The assigned proof follows the planned route:
   integral weak-Serre closure, a distinguished cone, derived reduction, the
   coefficient short exact sequence, scalar invertibility, and constructible
   Nakayama on homology. The realized proper-base-change unit route is retained.
   I reran the import-pruning check over all delivered modules. It found no
   remaining redundant imports after removing
   `WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant`,
   `WeilConjectures.CategoryTheory.RingObjects.ContinuousMap`,
   and `Sheaf.Paper.ProEtalePointComponentsMaps` from
   `IntegralScalarContractive`; each was already reachable through the generic
   comparison imports. I also removed the renamed `integralTestProjection` construction and
   `integralTestProjection_natural` proof, using the existing
   `profiniteTestProjection` and `profiniteTestProjection_natural` directly.
   The report's pruned helper copies and modules agree with the files on disk.

5. **DAG: pass.** I checked that every delivered declaration's signature is
   verbatim in its node, that each new node has source, proof steps, searches,
   provenance, chapter, unit, and Lean record, and that `proof_deps` is the union
   of the uses in its proof steps. The assigned node records the final cone and
   scalar/Nakayama route. The sole remaining hole is attached to
   `lem-weil-pbc-integral-constructible-kernels`; no node merely restates the
   assigned target.

**Second-reading changes.** Removed the three redundant proof-only imports and
the two copied projection helpers listed above; all remaining comparison helpers
are actual coefficient generalizations. Updated the scalar node's proof record.
No public theorem statement, definition, node statement, or unit route changed.
