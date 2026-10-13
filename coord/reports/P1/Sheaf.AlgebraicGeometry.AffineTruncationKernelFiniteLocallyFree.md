## What changed

Replaced the sole sorry in AlgebraicGeometry.affine_truncationKernel_finiteLocallyFree
by a complete Lean assembly with its original signature and visibility unchanged.
Added PrincipalOpenFiniteProjectiveTilde.lean for the generic final gluing step.
Updated the item's proof route and added the matching new node. The repair generalizes
its private finite-limit helper to a categorical theorem; no public statement or
definition changed, and no other existing module is adapted.

The proof tests derived tensor vanishing against the tensor unit, transports its
homology through the representing isomorphism, and constructs the image/kernel
isomorphism from an actual limiting kernel fork. Mathlib's image preservation
comparison proves the required inclusion identity. Exactness of tilde is obtained by applying the generalized private theorem
preservesFiniteLimits_of_kernel_in_essentialImage. This theorem has explicit arbitrary
abelian categories C and D, an additive fully faithful functor T, and an essential-image
hypothesis for kernels of mapped morphisms. It lifts and reflects each kernel fork.
For tilde, the source's quasi-coherent-kernel lemma and affine counit prove the
essential-image hypothesis; no exactness theorem is merely assumed.

Functor.mapDerivedCategoryFactors and mapHomologicalComplexCompIso bridge the
statement's representation with affine_truncation_kernel_flat's representation.
The existing lower-kernel theorem is then applied, and Mathlib's finite-presentation
instance and Module.Flat.projective_of_finitePresentation yield finite projective
principal localizations. The new general lemma gives local freeness for the linear
range; ModuleCat.imageIsoRange transfers it to the categorical image. The source
finite-local-freeness instance gives finite presentation, and the already proved
finiteLocallyFree_tensorLeft_exact plus braiding gives right tensor exactness.

The local compile checks the entire delivery in import order. The main theorem has
an increased heartbeat budget only for definitional equality in its derived and
image comparisons; each single-file compile remains below the 60-second limit.

## Proved and sorry left

Closed: AlgebraicGeometry.affine_truncationKernel_finiteLocallyFree
(node lem-sc-affine-truncation-kernel-finite-locally-free).
No sorry remains in the assigned module.

Added and left: AlgebraicGeometry.finiteLocallyFree_restrict_tilde_of_principalOpen_projective
(node lem-sc-principal-open-finite-projective-tilde), in its own new module
Sheaf.AlgebraicGeometry.PrincipalOpenFiniteProjectiveTilde.
This is a decomposition: one upper hole closed and one strictly smaller general
localization/gluing hole added. Net holes closed minus added: zero. The existing
AlgebraicGeometry.affine_truncation_kernel_flat is used as intended and not changed.
All private helpers are fully proved. No arbitrary object is defined by choosing
from an unproved existence theorem.

## No longer needed

Repair: removed the duplicate private AlgebraicGeometry.tilde_preservesFiniteLimits
statement and both calls to it. The replacement private categorical theorem is strictly
more general, including additive fully faithful functors that are not left adjoints.
No import of AffineProjectiveSectionsSheafification is needed or added. The existing
QuasicoherentKernel import remains necessary for the tilde specialization.

Removed the direct proof import Sheaf.RingTheory.FiniteProjectiveStandardFreeCover
from the assigned module; it is now the planned proof dependency of the generic
gluing module, so its node and module remain needed in this decomposition.
The old proof dependency lem-pc-affine-tor-amplitude-criterion is no longer used
directly (its statement import stays); lem-weil-pbc-finite-projective-standard-free-cover
is no longer a direct dependency of the item and is used by the new gluing node.
No globally reachable module is claimed pruned. The affine Tor-amplitude criterion
is not applied directly in the final assembly: its role is already in the existing
flat-kernel theorem, and its public import remains required by the statement's
interfaces. The four original public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

Repair of the return at head 7a42c0b2b: the first delivery duplicated the existing
private Scheme.Modules.tilde_preservesFiniteLimits helper word for word.
An import cannot use that private declaration (lcompile reported Unknown constant
AlgebraicGeometry.Scheme.Modules.tilde_preservesFiniteLimits). Changing its visibility
would violate the unheld-module adaptation rule. Accordingly this repair takes the
return's generalization option in the assigned module: the kernel-lifting argument
is now a theorem for arbitrary abelian categories and additive fully faithful functors,
and its tilde specialization supplies only the essential-image hypothesis. This is
a different, strictly more general mathematical statement, with explicit binders,
not a renaming or alternate packaging of the affine finite-limit conclusion.
The former second-reading text below records the previous delivery; a new independent
reading is required after this repair.

The mathematical statement is unchanged and no disputed statement was found.
The flat-kernel interface uses derived restriction of Q(tilde P), whereas this
item uses Q of termwise restriction; the needed comparison was proved using
Mathlib rather than assumed definitionally. The categorical image differs from
the linear range, and their canonical isomorphism is explicitly used.

The original plan did not state the generic gluing theorem needed to pass from
finite projective localizations on ambient principal opens to the actual over-site
sheaf on U. That step is isolated below, not folded into a restatement of the item.
The unit record sk-thm-picard-duality has empty realized.statement and realized.steps
entries; the same source truncation route is preserved.

The clone has no literature/stacks-project/perfect.tex. The recorded sources were
read at https://stacks.math.columbia.edu/tag/08EG and
https://stacks.math.columbia.edu/tag/00NX, with the tensor-flatness criterion at
https://stacks.math.columbia.edu/tag/05NE. The source's Tag 08ED miscitation was
already corrected in the item's docstring; existing source/statement fields are
not changed in this proof delivery.

## New nodes

lem-sc-principal-open-finite-projective-tilde:
Sheaf.AlgebraicGeometry.PrincipalOpenFiniteProjectiveTilde states that finite
projectivity of M_f for every D(f) inside U implies finite local freeness of tilde M
restricted to U. Its argument uses principal-open localization of tilde, the finite
standard free cover over A_f, and open-cover descent of local freeness. This is
independent of complexes and only the final property step of the original theorem.
The hypothesis does not impose finiteness on M away from U. Edge cases checked in
words: empty U/zero ring (empty cover), zero module (rank zero), disjoint components
with different finite ranks, and modules not finite outside U. None needs a common
rank, a nonempty open or a noetherian hypothesis.

Searches: LeanFinder and Loogle find Module.basicOpen_subset_freeLocus_iff, whose
global finite-presentation assumption is unavailable here. The existing source
isFiniteLocallyFree_of_isAffineOpen takes section modules on every affine open,
not the ambient principal localizations in this interface. Grep found no duplicate.
The new node records these searches. LeanSearch was also attempted and returned
Internal Server Error; its unavailability is recorded. The already proved principal
localization transport and the finite standard free cover are used as generic tools
from the proper-base-change unit; they do not replace the Picard unit truncation route.
No change record is needed.

## Earlier second reading (a previous round; superseded)

1. PASS: diffed the existing module against the read-only repository and compared
   the original theorem signature byte for byte through its proof delimiter. It
   is identical, including universes and visibility. No definition or existing
   statement changed. Only proof, proof_deps and proof_origin changed in its node.
2. PASS: both delivery modules compile in import order (5.4 s and 38.0 s).
   Read every private helper and the full assembly: homology is transported
   through actual isomorphisms; the image comparison comes from a limiting fork,
   with its inclusion identity proved; the affine counit is used only for a
   quasi-coherent kernel. There are no definitions with postponed data and no
   forbidden declarations. Scratch #print axioms checks show exactly propext,
   Classical.choice and Quot.sound for all three private helpers; the main and
   split theorem additionally use sorryAx, as expected from the named open lemma.
   The only explicit sorry is the reported new theorem.
3. PASS: the new theorem is a strictly smaller general sheaf-locality statement,
   with no complexes, Tor amplitude, image/kernel conclusion or derived category
   assumptions. Its principal opens cover U even without compactness; finite
   projectivity is applied over each A_f. Checked empty U, the zero ring, zero
   module and varying component ranks. Its docstring supplies a complete proof
   and its node matches. Independently searched LeanFinder, Loogle and rg using
   associated module sheaf/localization and restrict-iso-free terminology. The
   source LocallyFreeAffine criterion requires all affine section modules; the
   Mathlib free-locus criterion requires global finite presentation. Neither is
   an immediate replacement for this hypothesis. The gluing proof needs several
   localization and over-site comparisons, so is left as the named decomposition.
4. PASS after repair: the proof follows the source truncation route and uses the
   lower flat-kernel statement. The unit realized fields are empty, and no unit
   route is bypassed. Checked all four removed old proof-dependency references;
   expanded No longer needed to name both removed direct dependencies explicitly.
   All proof-only imports have plain import; public imports provide signatures.
5. PASS after repair: the existing node records the actual four assembly steps
   and the new node gives its source, dependencies, searches, provenance, unit,
   blueprint and verbatim Lean statement. Added the missing plain import of
   TildePrincipalLocalizationTransport to the new module, matching its planned
   first step. Added the existing quasi-coherent-kernel node to the main route
   because the proved finite-limit helper uses it.

Second reading changed only dependency bookkeeping, the missing proof-dependency
import, and this report. No Lean proof or signature needed repair. The delivery
closes affine_truncationKernel_finiteLocallyFree and adds
finiteLocallyFree_restrict_tilde_of_principalOpen_projective: one-for-one
decomposition, net zero holes, no globally pruned module. Source paragraphs
checked independently at https://stacks.math.columbia.edu/tag/00NX and
https://stacks.math.columbia.edu/tag/08EG.


## Second reading by P1

Independent reading of the repaired delivery, superseding the earlier reading above.

1. PASS. Diffed the assigned module against the read-only repository and checked
   the existing theorem signature byte for byte, through its proof delimiter:
   identical. Its four public imports, universes and visibility are unchanged.
   There are no changed definitions, target statements or forced adaptations.
   Compared the JSON objects: the existing node changes only proof, proof_deps
   and proof_origin.
2. PASS. Read all three private helpers and the final assembly. Compiled both
   delivery modules in import order (5.1 s and 35.4 s), without errors or warnings.
   A fresh scratch copy of the repaired module printed axioms for all five
   declarations: the three helpers use only propext, Classical.choice and
   Quot.sound; the main and new open theorem also use sorryAx. The sole explicit
   sorry is the reported public gluing theorem. No forbidden declaration or
   hollow definition occurs. In particular the generalized kernel helper lifts
   the kernel inclusion by fullness, proves its composite zero by faithfulness,
   transports the limiting fork along the essential-image isomorphism, then
   reflects its limit. Its assumptions suffice in arbitrary abelian categories;
   unlike the earlier affine helper it assumes neither an adjunction nor tilde.
   The application supplies quasi-coherence and the affine counit explicitly.
3. PASS. Read the new theorem, its complete docstring argument, both dependency
   statements, and its node. It only asserts local freeness of an associated
   module sheaf from finite projective principal localizations; it contains none
   of the original complex, homology, derived-representation or kernel/image
   assertions. Principal neighborhoods inside U cover U; the finite standard
   free cover is applied over A_f, not A. Checked empty U, the zero ring, zero
   module and varying component ranks: no nonemptiness, constant rank,
   Noetherian condition or global finiteness is tacitly needed. Independently
   searched LeanFinder with distinguished-neighborhood/associated-sheaf wording,
   Loogle for SheafOfModules.IsFiniteLocallyFree (unknown identifier, not evidence
   of absence), and rg throughout lean/, upstream WeilConjectures and Mathlib
   categorical sources. Read AffineFiniteModuleFreeLocus: its sheaf criterion
   assumes a Noetherian ring and a globally finite module. Read LocallyFreeAffine:
   its converse requires sections on all affine opens. The Mathlib free-locus
   hits assume global finite presentation. None directly replaces this lemma.
   Closing it requires the localization/over-site comparisons in its docstring,
   rather than a short application, so it remains the explicitly reported split.
4. PASS. Read Stacks 08EG's truncation paragraph and 00NX's finite projective
   equivalences at https://stacks.math.columbia.edu/tag/08EG and
   https://stacks.math.columbia.edu/tag/00NX. The assembly retains the lower
   flat-kernel theorem, then finite presentation plus flatness gives projectivity
   on principal opens. The actual limiting image/kernel fork proves the requested
   inclusion identity. The derived restriction comparison is an explicit iso;
   ModuleCat.imageIsoRange transfers the final local-freeness property. Tensor
   exactness and the braiding prove the stated right-tensor flatness. The unit
   sk-thm-picard-duality has empty realized entries, and its route is unchanged.
   Checked the old proof_deps: No longer needed names both removed direct nodes,
   affine-tor-amplitude-criterion and finite-projective-standard-free-cover;
   the latter remains a dependency of the new gluing node. No globally pruned
   module is claimed. All added proof imports are plain imports; the new
   module's public imports supply its signature (including moduleRings).
5. PASS. The existing node's four steps agree with the Lean, including the
   quasi-coherent-kernel dependency used by the repaired categorical helper.
   Their uses union equals proof_deps. The new node records the exact Lean
   statement, localization and standard-free-cover dependencies, source places,
   searches, blueprint provenance, chapter, unit, creation and Lean records.
   No new statement duplicates the assigned theorem or changes its meaning.

Second reading changed only this report and added independent search-log entries;
no Lean proof, signature, import or node needed repair. Closed hole:
AlgebraicGeometry.affine_truncationKernel_finiteLocallyFree. Added hole:
AlgebraicGeometry.finiteLocallyFree_restrict_tilde_of_principalOpen_projective.
This is a one-for-one decomposition, net zero holes, with no globally pruned module.
