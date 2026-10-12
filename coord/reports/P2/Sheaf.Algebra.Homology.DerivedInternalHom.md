## What changed

Proved all three theorems in Sheaf.Algebra.Homology.DerivedInternalHom without changing
any signature or the derivedInternalHom definition. The inversion theorem applies
quasiIso_homComplex_map directly to a pair of morphisms. The comparison uses the natural
zigzag I0 -> I0 composed with I <- I, so no homotopy-class lifting is needed. The object
formula uses the resolution map of the already K-injective representative.
Updated the existing DAG node to record this route. No new modules or nodes.
The import interface change is recorded in coord/changes/DerivedInternalHomImports.md.

## Proved and sorry left

Proved CategoryTheory.derivedInternalHom_inverts,
CategoryTheory.derivedInternalHom_comparison and CategoryTheory.derivedInternalHom_obj_iso.
Holes closed: the three declarations just listed. Holes added: none.
No sorry remains in the delivered module. The proof uses the existing stated dependency
CategoryTheory.quasiIso_homComplex_map (lem-pur-rhom-well-defined), whose sorry is outside
this delivery, and the existing Hom-complex construction. These remain future items.

## No longer needed

Removed Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions: the source-library
K-injective resolution functor and SheafOfModules.isGrothendieckAbelian already provide
the data actually used. This module's localized generator and degreewise-injective
resolution clauses are unnecessary here. The stronger node prop-pur-kinjective-resolutions-exist is not used by the proof and
was removed from proof_deps at second reading: the upstream resolution construction
supplies exactly the required data. Its statement-dependency citation is unchanged.
Changed Sheaf.Algebra.Homology.QuasiIsoHomComplexMap from public import to proof-only
import, since its theorem is needed only in proofs. No other import was removed.
No chain-map lifting, uniqueness-up-to-homotopy, or homotopy-invariance lemma is needed
for comparison or representative independence; no such extra node was previously a
proof dependency of this node. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The existing comparison and object-isomorphism docstrings describe a valid but longer
route through homotopy classes. The composite-resolution zigzag makes those steps
unnecessary. The existing node had an empty proof; its proof now records the Lean route.
No statement dispute, signature correction, or target change.

## Second reading by P2

1. PASS. Compared the complete module against the repository using diff and checked
   all four declaration signatures byte for byte. The complete derivedInternalHom
   definition is unchanged. Only the three proof bodies and the declared import
   interface change differ. The import change has its change record at
   coord/changes/DerivedInternalHomImports.md; no target statement changes.
2. PASS. Compiled the delivered module locally without warnings or errors. A scratch
   copy with #print axioms for all four declarations reports only propext,
   Classical.choice, Quot.sound and sorryAx from existing dependencies. No sorry,
   axiom, unsafe, opaque, implemented_by, extern or kernel-check bypass occurs in the
   delivered module. In particular, no definition contains a new hole.
3. PASS. No statement is split off, no new declaration or node is added, and no hole
   is moved elsewhere. Checked the comparison maps on identity replacements and
   already K-injective inputs: both maps have common target I(I0(M)), and naturality
   plus two-out-of-three gives the required quasi-isomorphism of I(eta0.app M).
   The object formula uses the actual resolution map of Ic with the correct inverse.
4. PASS after bookkeeping repair. Read HomComplex, QuasiIsoHomComplexMap and the
   upstream KInjectiveResolution construction. Searched the library and Mathlib for
   localization factorization and whiskered isomorphisms; the proof already uses
   Localization.fac and componentwise isomorphisms directly. No extra homotopy
   comparison theorem is needed. The proof-only Hom-complex quasi-isomorphism import
   is correctly private to proofs. The removed ringed-site module is unnecessary.
   The original proof_deps was empty, so there are no omitted old dependency ids.
   The unit sk-def-sf-operations has no proof steps and empty realized lists; its
   ambient derived-Hom functor and the chapter route are preserved.
5. PASS after repair. Only proof, proof_deps and proof_origin differ in the existing
   node. The three proof steps match inversion, the natural zigzag comparison and
   representative transport; proof_deps is exactly the union of step uses. Removed
   prop-pur-kinjective-resolutions-exist from proof uses: its stronger ringed-site
   theorem is never applied, and retaining it would invite reintroducing its import.
   The upstream functorial resolution used instead is explicitly named in the proof.

Changed at second reading: removed the unused resolution proposition from the DAG
proof dependencies, clarified the order of the composite resolution in the DAG,
recorded holes closed and added explicitly, and added this review. No Lean proof,
signature or definition was changed. The three closed holes remain conditional on
existing imported statements; this delivery does not claim an axiom-free target.
