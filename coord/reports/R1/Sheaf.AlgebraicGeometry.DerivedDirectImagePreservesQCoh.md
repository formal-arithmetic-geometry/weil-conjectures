## What changed

Replaced the sole sorry in Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesQCoh,
AlgebraicGeometry.schemeDerivedDirectImage_preserves_QCoh, with a compiling proof
from two strictly smaller intermediate statements. The public signature and public
imports are unchanged. The proof constructs the zero witness for the quasi-coherent
object property, applies the existing homologyProperty_truncGE theorem to obtain
quasi-coherent canonical truncations, applies bounded-below preservation, transports
quasi-coherence through the actual restricted truncation-map isomorphism, and glues
on the cover of all affine opens. It does not assume the target is quasi-compact.

Added two new modules, one statement per module:
Sheaf.AlgebraicGeometry.DerivedDirectImageBoundedBelowQCoh and
Sheaf.AlgebraicGeometry.DerivedDirectImageAffineTruncationComparison. Their docstrings
contain complete sourced proofs in words. Updated the parent DAG proof to the
reduction actually compiled, and supplied the two new DAG nodes. No definition,
existing statement, unit record, or target was changed.

Read the source proof of perfect-lemma-quasi-coherence-direct-image (Tag 08D5),
including its bounded-below spectral sequence paragraph and final canonical
truncation paragraph, in the local Stacks source copy at
/home/ubuntu/c1-stacks-review/perfect.tex, lines 444--513. The logical route is the
same as the original DAG: bounded-below spectral sequence and finite filtration,
then degreewise truncation on affine opens. The unit record sk-thm-picard-duality
has no realized node that this reduction bypasses.

## Proved and sorry left

The original declaration AlgebraicGeometry.schemeDerivedDirectImage_preserves_QCoh
(node lem-pc-derived-direct-image-preserves-qcoh) now has a complete Lean proof.
It is a reduction, not an axiom-free closure: its proof still depends on the
following two named new sorries, as intended in stage 3:

- AlgebraicGeometry.schemeDerivedDirectImage_preserves_QCoh_of_isGE,
  node lem-pc-derived-direct-image-bounded-below-qcoh, in
  Sheaf.AlgebraicGeometry.DerivedDirectImageBoundedBelowQCoh. It requires a fixed
  lower cohomological bound, and contains the spectral sequence/finite filtration
  portion only. It cannot handle an arbitrary unbounded input.
- AlgebraicGeometry.exists_isIso_schemeHigherDirectImage_truncGE_over_affine,
  node lem-pc-derived-direct-image-affine-truncation-comparison, in
  Sheaf.AlgebraicGeometry.DerivedDirectImageAffineTruncationComparison. It asserts
  only that the restricted canonical map is an isomorphism, for a fixed degree
  and affine open. It asserts no quasi-coherence of either side.

The node proof_deps fields were checked against the union of all step uses.
No new dependency reaches the parent item. A broader DAG traversal encountered
existing cycles between lem-weil-pbc-sheaf-algebraic-structures-objects and
lem-weil-pbc-sheaf-algebraic-structures-abelian-component; these do not involve
any new node and were not modified in this delivery.

These are all sorries introduced by this delivery; none remains in the item's
module. All three delivered modules compile locally together in import order.
The new statement edge cases were checked mathematically: zero input and empty
scheme/open give maps between zero objects; the bounded-below statement covers
all integer degrees, including q below the bound, when the negative total-degree
quadrant vanishes. No uniform n over a non-quasi-compact target is asserted: n
may depend on E, q and U. The local comparison uses the actual canonical
truncation projection, rather than an unspecified object with the same property.
The universe binders wX and wY are independent throughout.

## No longer needed

Removed the following direct proof imports from the item's module:

- Sheaf.Algebra.Homology.KInjectiveRestrictOpen
- Sheaf.AlgebraicGeometry.DerivedCategory
- Sheaf.AlgebraicGeometry.DerivedDirectImageUniformTruncationBound
- Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
- Sheaf.AlgebraicGeometry.Modules.QuasicoherentExtension
- Sheaf.CategoryTheory.TruncationHypercohomology
- WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

DerivedCategory is already a public dependency of SchemeDerivedDirectImage. The
other proof ingredients remain below the two intermediate nodes, so they are
not claimed as globally pruned modules. KInjectiveRestrictOpen is reached through
the existing open-restriction comparison. The parent proof no longer directly
uses lem-sc-derived-k-injective-restrict-open,
lem-pc-derived-direct-image-uniform-truncation-bound, thm-sp-truncation-e2,
lem-pc-finite-support-hi, lem-weil-pbc-quasi-coherent-module-kernel,
lem-weil-pbc-quasi-coherent-module-cokernel-image or
lem-pc-quasi-coherent-extension, or def-pc-derived-direct-image; those remain
dependencies of the intermediate arguments. The derived-direct-image definition
also remains a public dependency through SchemeDerivedDirectImage. Thus no substantive part of the original mathematical route is pruned.

Added only private proof imports to the parent: the two new modules,
WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty and
WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.

## Where the brief, the DAG or earlier work was wrong

The node lem-pc-finite-support-hi includes quasi-coherence of higher direct images
as clause (1), but its lean record names only
Scheme.Modules.exists_isZero_higherDirectImage_of_isPullback in
WeilConjectures.AlgebraicGeometry.Cohomology.Projective, which is the vanishing
clause. The required quasi-coherence declaration actually is
Scheme.Modules.isQuasicoherent_higherDirectImage in
WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections. It still has
sorry, which itself is permitted for this stage; the difficulty is an import
cycle: import_direction.py reports that both source modules already reach the
parent DerivedDirectImagePreservesQCoh. Neither is imported in this delivery.
The worker of the bounded-below intermediate will need an acyclic interface for
that existing clause, together with the comparison between the Scheme.Modules
right-derived encoding and the shared SheafOfModules derived direct image. No
second definition of either derived category was introduced to conceal this.

The existing original proof also implicitly needed naturality of open restriction
and exact restriction's compatibility with truncation. The local intermediate
states precisely this canonical-map comparison, and its proof plan names
schemeDerivedDirectImage_openRestriction and the existing
Functor.mapDerivedCategoryHomologyFunctorIso / mapDerivedCategoryTruncGEIso.

Mathlib searches were run using msearch.py and are recorded in searches.jsonl.
LeanSearch returned Internal Server Error and is recorded as unavailable, not as
no match. LeanFinder returned generic truncation/derived-category results; grep
found no scheme-derived quasi-coherence preservation theorem. The blueprint
searches for bounded-below quasi-coherence and truncation direct image returned
no duplicate; the broader truncation search found only generic or etale results.

## New nodes

lem-pc-derived-direct-image-bounded-below-qcoh is the bounded-below spectral
sequence and finite-filtration portion of Tag 08D5. Its statement has the genuine
extra hypothesis E.IsGE a, and its remaining work is separately scoped. It keeps
the original thm-sp-truncation-e2 tool use and kernel/cokernel/image and extension
closure route; those off-unit tools are inherited from the original argument
and should be retained by the reviewer.

lem-pc-derived-direct-image-affine-truncation-comparison is the degreewise,
affine-local canonical truncation comparison from the final paragraph of Tag
08D5, combined with Tag 08FE open restriction and Tag 08BS. It keeps the existing
uniform-truncation-bound node as its main input. Its statement contains no
quasi-coherence conclusion, so it is not the original statement renamed.

Both nodes inherit sec-picard-framework and sk-thm-picard-duality, and refer to
the same nearest blueprint ancestor lem-sc-finite-duality through the parent
node. No change records were needed.


## Second reading by R1

1. Compared the parent Lean file with the repository using diff, and compared the
   existing node field by field. The theorem signature is byte for byte unchanged;
   the three public imports are unchanged. There are no changed definitions or
   other existing declarations. Only proof, proof_deps and proof_origin changed
   in the existing node. No change record is required. Verdict: pass.
2. Compiled all three files locally in import order with lcompile.py: no errors
   or warnings. The parent has no sorry; the two new public named theorems each
   have exactly `:= by sorry`, as reported. There are no forbidden declarations
   or hollow definitions. In a temporary scratch copy, #print axioms for all
   three declarations returned only propext, Classical.choice, Quot.sound and
   sorryAx. The reduction therefore does not claim axiom-free closure. Checked
   the direction of e.symm: quasi-coherence of the truncated image transfers to
   the original image. Verdict: pass.
3. Read perfect.tex, Tag 08D5, lines 444--513, including the bounded-below spectral
   sequence paragraph and the truncation triangle. The bounded-below lemma adds
   the genuine IsGE a hypothesis and supplies only that portion; the affine lemma
   concerns only a canonical map in one degree and makes no QCoh assertion.
   Neither restates the original item. Checked zero input, empty open, q < a,
   independent derived-category universes, and a target without quasi-compactness.
   The spectral sequence has only 0 <= p <= q-a in degree q; when q < a there
   are no surviving terms. The local threshold may depend on U and q. Read the
   existing uniform-bound second clause and the natural open-restriction theorem:
   they supply the proposed comparison, with exact restriction commuting with
   truncation and its projection. Both new docstrings give the sourced argument,
   and their nodes match the signatures. Independent LeanFinder search for QCoh
   higher direct images of bounded-below derived objects gave generic derived
   category lemmas only; msearch grep for truncGEπ/preserves_QCoh and rg over both
   library roots found no replacement. The generic homology truncation iso does
   not apply to a non-exact direct-image functor. Neither substantial remaining
   lemma can be closed by a few-minute application of these results. Verdict: pass.
4. Reviewed all imports against the statements and proof plans: signature imports
   are public, proof imports private. The top proof uses the existing generic
   homologyProperty_truncGE and QCoh locality results rather than splitting those
   elementary reductions. The seven removed imports are listed, and the removed
   direct DAG dependencies are now complete. They remain under the intermediate
   lemmas; no global pruning is claimed. Opened sk-thm-picard-duality.json: its
   realized statement and step lists are empty, so no realized unit node is
   bypassed. The bounded-below spectral sequence and unbounded truncation route
   of the old plan are retained. Verdict: pass.
5. Checked the three nodes: proof_deps is exactly the union of each proof's uses;
   the parent steps follow the compiled truncation, zero witness, iso transport,
   and affine cover proof. The new nodes have source, origin, searches, creation,
   blueprint ancestry, chapter/unit and verbatim Lean signatures. The existing
   higher-direct-image node's recorded declaration does not supply its QCoh
   clause; the first reader correctly reports this upstream interface issue
   rather than adding a duplicate definition or concealing it. Verdict: pass.

Changed only this report: completed the removed-direct-dependency list with
 def-pc-derived-direct-image and added this independent reading. No Lean repair
was needed. The scratch axiom-check copy was removed before delivery.
