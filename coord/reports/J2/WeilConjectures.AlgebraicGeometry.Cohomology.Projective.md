## What changed

Repair of the landing return: removed the duplicate private theorem
AlgebraicGeometry.isZero_openCohomology_union from the new uniform-bound module.
The matching theorem in LocalUniformHigherDirectImageBound is private and cannot be
used by an importer. The induction now uses the existing public
RingedSpace.module_mayerVietoris directly and derives vanishing in its proof body.
No existing library module, signature, or visibility was changed.

Closed all five original holes in `WeilConjectures.AlgebraicGeometry.Cohomology.Projective`.
All existing declaration signatures, visibility, definitions, and public imports stay identical.
No module belonging to another worker is adapted.

The uniform base-change bound now has a complete finite-affine-cover proof. A new, fully proved
module `Sheaf.AlgebraicGeometry.UniformAffinePullbackCohomologyBound` supplies the cover induction:
for every affine h:Y->X and quasi-coherent F on Y, cohomology vanishes above a bound depending only
on the quasi-compact quasi-separated X. Its proof uses quasi-compact-open induction, affine-open
vanishing, and module Mayer-Vietoris with bound max(max(a,b),c)+1. The proof compares derived
open sections at top with module global sections by exact forgetful homology and then with H.
The original theorem takes maxima over a finite affine cover of its base, constructs an affine
cover after every base change, proves the restricted cartesian projections affine, and uses
zero sections on that cover to show the higher direct image's zero endomorphism epi.

Both finiteness holes reuse `finite_H_projective_affine_independent`, an existing proof of the
same descending-induction argument over affine schemes. Finiteness over Gamma(Spec A,top)
is transported to A through an explicit identity semilinear surjection and GammaSpecIso's
inverse law. This avoids general proper coherence in both new finiteness proofs.

Closed-subscheme cohomology vanishing uses affine pushforward quasi-coherence, the projective
space dimension bound, and the abelian-sheaf affine-pushforward cohomology comparison. The
comparison works over every commutative ring; the field-linear version is unnecessary.
Relative vanishing restricts the embedding to each affine open, transports its base to the
spectrum of global sections, and applies that closed-subscheme vanishing. Open-module and
affine-open higher-direct-image comparisons then give zero sections on an affine cover.
The previously proved coherence theorem is untouched.

The four existing node copies record these actual proofs and dependencies. The unit record
sk-thm-picard-coherence has empty realized lists; no realized unit statement or step is bypassed.
The descending-induction and Cech machinery remain in the reused finiteness module.

Validation: both sandbox modules compile in import order without errors or warnings after
pruning. Existing and new signatures include empty schemes, empty coordinate types where
appropriate, degree zero for finiteness, arbitrary commutative rings for vanishing, and
arbitrary base changes for the uniform bound. No new unproved data or existence choice is used.
Ordinary choices in the proofs choose affine opens, integers, and proved comparison maps.

## Proved and sorry left

Original holes closed (5):

- AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage_of_isPullback
  (lem-pc-finite-support-hi).
- AlgebraicGeometry.ProjectiveSpace.finite_H
  (lem-pc-projective-space-coherent-finiteness).
- AlgebraicGeometry.Scheme.Modules.finite_H_of_isClosedImmersion
  (lem-pc-projective-coherent-finiteness).
- AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_isClosedImmersion
  (lem-pc-projective-coherent-finiteness).
- AlgebraicGeometry.Scheme.Modules.isZero_higherDirectImage_of_isClosedImmersion
  (lem-pc-projective-coherent-higher-images).

New proved theorem:
AlgebraicGeometry.exists_uniform_affine_pullback_openCohomology_bound
(lem-pc-j2-uniform-affine-pullback-cohomology-bound).
The induction step applies the existing public RingedSpace.module_mayerVietoris directly;
there is no duplicate private union theorem.

Sorry left in delivered modules: none. New holes added: zero; split off: zero.
These are stage-3 proofs from existing declarations. Some dependencies still contribute
sorryAx transitively, in particular the existing finite-source cohomology segment and
alternating-Cech inputs; no claim of globally axiom-free target completion is made.

## No longer needed

The duplicate private isZero_openCohomology_union declaration is removed. Its module-level
interface is unnecessary: the existing public ModuleMayerVietoris theorem supplies the
exactness used directly in the induction step. No additional imports or nodes were added.

Removed eleven direct proof imports:

- Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
- Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction
- Sheaf.AlgebraicGeometry.Modules.QuasicoherentExtension
- Sheaf.AlgebraicGeometry.Morphisms.Projective
- Sheaf.AlgebraicGeometry.QuasiCoherentMayerVietorisOpenCover
- Sheaf.AlgebraicGeometry.QuasiCompactOpenInduction
- Sheaf.Paper.HigherDirectImagePresheaf
- Sheaf.Paper.PQFCohomology
- WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech
- WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
- WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections

For the uniform bound, the old relative-Mayer-Vietoris quasi-coherence construction is not
used: lem-pc-restrict-derived-direct-image-open, lem-weil-pbc-higher-direct-image-presheaf,
lem-pc-quasi-coherent-extension, and lem-weil-pbc-module-presheaf-sheafification-exact leave
this node's direct proof dependencies. The ordinary quasi-coherence theorem is reused instead.
The new bound still uses open induction, affine vanishing and Mayer-Vietoris; these nodes are
not pruned, only their unnecessary direct imports are removed. The presheaf and restriction
modules can remain reachable through the proved comparison dependencies.

For finiteness, the original direct twist-quotient, twist-cohomology, dimension-bound and
Noetherian-submodule steps are packaged in the existing independent affine finiteness proof.
They remain needed transitively and are not claimed pruned. General proper coherence is not
used in either newly written finiteness proof. Projective-morphism definitions, finite-type
Noetherianity and locally-Noetherian finite-type arguments leave the direct dependencies of
lem-pc-projective-coherent-finiteness; its new vanishing proof needs only quasi-coherence.

For relative vanishing, pqf-lem-coherent-ft-locnoeth and the affine tilde-Gamma adjunction
are not used as proof steps; vanishing is detected by the zero endomorphism being epi on an
affine cover. The earlier, already proved coherence theorem still invokes proper coherence;
its route is recorded rather than counted as newly proved or pruned. Removed direct imports
do not by themselves assert removal from the full target import closure: all three public
imports are preserved and their transitive modules may still reach these same modules.


Complete list of removed direct DAG proof dependencies (not a claim of closure pruning):

- `lem-pc-finite-support-hi`: `lem-pc-affine-morphism-hi`, `lem-pc-affine-vanishing`, `lem-pc-quasi-coherent-extension`, `lem-pc-restrict-derived-direct-image-open`, `lem-sc-invert-s-cohomology-induction`, `lem-sc-mayer-vietoris-open-cover`, `lem-weil-pbc-higher-direct-image-presheaf`, `lem-weil-pbc-module-presheaf-sheafification-exact`.
- `lem-pc-projective-coherent-finiteness`: `def-pc-proj`, `def-pc-projective-morphism`, `lem-pc-projective-space-coherent-finiteness`, `lem-weil-pbc-finite-type-over-noetherian`, `pqf-lem-locnoeth-lft`.
- `lem-pc-projective-coherent-higher-images`: `lem-pc-cohomology-sections-affine-base`, `lem-pc-finite-support-hi`, `lem-weil-pbc-affine-tilde-gamma-adjunction`, `pqf-lem-coherent-ft-locnoeth`.
- `lem-pc-projective-space-coherent-finiteness`: `lem-pc-projective-space-cohomology-bound`, `lem-pc-projective-space-twist-cohomology`, `lem-pc-projective-space-twist-quotient`, `lem-weil-pbc-noetherian-submodule-finite`, `pqf-def-cohomology`.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery duplicated the private union theorem of
Sheaf.AlgebraicGeometry.LocalUniformHigherDirectImageBound. The landing checker correctly
rejected that declaration. This repair removes it and uses the public Mayer-Vietoris
exactness theorem directly; importing LocalUniformHigherDirectImageBound would not expose
its private helper. The earlier second-reading record below describes the returned version,
not independent validation of this repair.

The original uniform-bound docstring asserted a bound equal to the number of affine charts
with affine pairwise intersections. A quasi-separated scheme need not have affine
intersections, and this justification is not valid in that generality. The proof and docstring
now use quasi-compact-open induction and max-plus-one bounds including the intersection term.
The edge cases of an empty base and empty inverse images are handled by Finset.sup and the
same induction, without a nonempty hypothesis.

The blueprint finiteness plan is already formalized independently in
Sheaf.AlgebraicGeometry.ProjectiveAffineFiniteCohomologyIndependent; no new twist or exact
segment holes were required. The source affine-pushforward theorem over a field is not the
right interface for arbitrary A, but its general abelian-sheaf comparison is proved and
usable. Its instantiated target group is definitionally the H of the module pushforward.

The existing projective-higher-images node described a direct affine-local coherence proof,
whereas the already-proved library theorem uses proper coherence. This delivery leaves that
Lean proof unchanged and updates the node to name the actual dependency. There is no proof
path from lem-pc-coherent-hi back to lem-pc-projective-coherent-higher-images.

The local Stacks TeX source is absent on this machine; the named source Tag 01XJ was read
at https://stacks.math.columbia.edu/tag/01XJ. It explicitly gives the finite-affine-cover
argument uniform in arbitrary base changes. LeanFinder and Loogle searches were run through
msearch; grep found no existing uniform affine-pullback cohomology bound. LeanSearch returned
Internal Server Error and is recorded unavailable. Blueprint searches for affine pullback,
uniform cohomology and cohomology bound found no duplicate blueprint node.

Cross-unit tools: lem-sc-mayer-vietoris-ringed-space supplies precisely the module
Mayer-Vietoris exactness needed by the induction; pqf-lem-affine-vanishing supplies affine-open
module-cohomology vanishing; lem-sc-module-cohomology-source-comparison supplies the additive
bridge to the source H. The existing open-comparison module is also reused. These are generic
tools, not replacements for a realized unit route; tool_uses is left for the maintainer.

## New nodes

lem-pc-j2-uniform-affine-pullback-cohomology-bound is a fully proved uniform cohomology bound
under affine morphisms to a fixed quasi-compact quasi-separated scheme. It is strictly the
finite-cover part of the uniform higher-direct-image argument: it does not mention direct
images, arbitrary non-affine base changes, or the finite affine cover of the original base.
Its module is Sheaf.AlgebraicGeometry.UniformAffinePullbackCohomologyBound and its node is
in dag/nodes/sec-picard-framework/. The proof handles the affine base case, the
Mayer-Vietoris gluing, and the final comparison with source H. There are no change records
because no existing statement, definition or public import changes.

## Earlier second reading (a previous round; superseded)

1. Compared the entire original Projective module with the sandbox and checked its parsed
   declaration table: all existing signatures are byte-for-byte identical, no declaration or
   visibility is removed, moduleHOfSpec is unchanged, and all three original public imports
   are unchanged. Only proof bodies, proof imports and explanatory proof docstrings differ.
   No change record is required. Verdict: pass.
2. Compiled both delivered modules in import order with lcompile.py, without errors or warnings.
   Text inspection finds no sorry, axiom, unsafe, opaque, implemented_by or extern and no hollow
   definition. Explicit #print axioms probes cover the new bound and all original declarations;
   the new bound uses only propext, Classical.choice and Quot.sound; original theorems also
   use the acknowledged transitive sorryAx.
   Comparison maps and numeric bounds are proved constructions/existentials; none introduces
   arbitrary data from an unproved mere existence theorem. Verdict: pass.
3. No statement is split off with sorry. Read the new fully proved bound and its node: affine
   preimages vanish above degree zero; max(max(a,b),c)+1 controls the union via the degree-q
   intersection term. The empty scheme/open, zero module and empty finite cover are covered;
   no field, Noetherian or nonempty hypothesis is hidden. LeanFinder and Loogle searches with
   different terms found no applicable replacement; rg found local uniform bounds and a
   field/affine-diagonal dimension bound, which do not assert uniformity over arbitrary affine
   morphisms. The helper is strictly the finite-cover cohomology part of the target, not a
   restatement. Verdict: pass.
4. Read each proof from its conclusion down to its inputs. The independent affine finiteness
   proof retains descending induction and the existing twist/Cech machinery. The vanishing
   argument uses the general abelian affine-pushforward comparison, not the field-linear
   theorem. Restricted cartesian projections are affine, so the bound is independent of base
   change. The unit sk-thm-picard-coherence has realized.statement=[] and realized.steps=[[]];
   no recorded unit route is bypassed. The report now explicitly lists every old proof_deps
   entry removed, separately from transitive reachability. Corrected the new helper's
   proof-only OpenModuleCohomology public import to a plain import. Verdict: pass after repair.
5. Read all five delivered nodes and compared the four existing nodes to their originals:
   only proof, proof_deps and proof_origin change. Proof dependencies equal the union of the
   uses in their proof steps. The new node has its source, complete verbal argument, statement
   dependencies, searches, creation/blueprint records and verbatim Lean statement. Existing
   proper coherence remains unchanged and is correctly named in the higher-images node.
   Verdict: pass.

Second reading changed only the new helper's proof-only import visibility and the report's
complete direct-dependency pruning inventory and this review. No proof or statement required
repair. Both delivered modules were recompiled after the import correction.

## Second reading by J2

1. Compared the Projective module with the repository using diff and parsed declaration tables. All seven existing signatures are byte-for-byte identical; visibility and public imports are unchanged. The abbreviation body and existing coherence proof are identical. Verdict: pass.
2. Independently compiled both modules in import order without errors or warnings. No local sorry or forbidden declaration occurs. Explicit axiom probes cover every declaration: the new bound and closed-subscheme cohomology vanishing use only the three allowed axioms; other results retain documented transitive sorryAx. No unproved arbitrary witness defines data. Verdict: pass.
3. No statements remain split off with sorry. Read the new bound's proof: the affine bound is 1 and the union bound controls the intersection in degree p-1. Empty schemes, empty opens and zero modules are included. Independent LeanFinder, Loogle and rg searches found no replacement uniform affine-pullback theorem; the existing local bound only handles affine open base changes. Checked the source at https://stacks.math.columbia.edu/tag/01XJ. The helper is strictly the finite-cover cohomology component. Verdict: pass.
4. Read every proof from its conclusion to its inputs. Finiteness reuses the independent descending induction; vanishing uses the general abelian affine-pushforward comparison. The repaired cover induction uses public Mayer-Vietoris directly and contains no duplicate private union declaration. The unit has no realized node bypassed. Removed imports and old direct dependencies are completely listed above, without claiming closure pruning. Verdict: pass.
5. Checked all five nodes: existing nodes change only proof metadata, proof_deps equals the union of proof-step uses, and each dependency resolves to its library declaration. The new node's verbatim statement, source, searches, blueprint and creation records agree with Lean. Verdict: pass.

This second reading changed only this report: no further Lean or DAG repair was required. It independently validates the repaired duplicate-helper removal and supersedes the earlier reading of the returned version.
