## What changed

Proved CategoryTheory.siteCohomology_pullback with its original signature and public
imports preserved. Added four modules for family/evaluation notation, existence,
uniqueness, and composition. The helpers use Mathlib exact-functor Ext maps and
injective dimension shifting. This delivery reuses the earlier T2 sandbox proofs,
which were found during library search, and recompiles them in the T1 sandbox.
No existing downstream module is adapted.

## Proved and sorry left

Closed the one original hole: CategoryTheory.siteCohomology_pullback.
Holes added: none. No sorry occurs in any delivered module.
The new proved helpers are CategoryTheory.siteCohomology_pullback_exists,
CategoryTheory.siteCohomology_pullback_unique,
CategoryTheory.siteCohomology_pullback_composite,
CategoryTheory.Sheaf.objectCohomologyEval₀_naturality, and
CategoryTheory.Sheaf.objectCohomologyEval₀_injective.
The proof still uses the existing exactness theorem sitePullback_abelian_exact;
its transitive dependencies are not claimed to be closed by this delivery.

## No longer needed

Removed proof imports Sheaf.CategoryTheory.Abelian.HorseshoeResolutions,
Sheaf.CategoryTheory.EffaceableDeltaFunctorUniversal, and
Sheaf.CategoryTheory.InjectiveResolutionSESComplexes.
Removed the redundant proof import Mathlib.CategoryTheory.Limits.Preserves.Finite
from the new composition module (the required API is already available).
Original public imports are retained to preserve downstream visibility; their
presence is not a claim that their theorem declarations are needed by this proof.
The site/cohomology definitions and enough injectives for abelian sheaves remain
needed and are supplied by Mathlib.
The following old proof dependencies are not used by the new proof:

- lem-weil-pbc-left-exact-injective-resolution-degree-zero.
- lem-weil-pbc-derived-functor-map-via-lift (`Mathlib.CategoryTheory.Abelian.RightDerived`).
- lem-weil-pbc-dplus-injective-representative.
- lem-weil-pbc-kinjective-hom-derived.
- def-weil-abstract-derived-category (`Mathlib.Algebra.Homology.DerivedCategory.Basic`).
- lem-weil-pbc-site-morphism-composition (`Sheaf.CategoryTheory.SiteMorphismComposition`).
- lem-weil-pbc-injective-resolution-ses (`Sheaf.CategoryTheory.Abelian.HorseshoeResolutions`).
- lem-weil-pbc-horseshoe-delta-functor (`Sheaf.CategoryTheory.Abelian.HorseshoeDeltaFunctor`).
- lem-weil-pbc-injective-resolution-ses-complexes (`Sheaf.CategoryTheory.InjectiveResolutionSESComplexes`).
- lem-weil-pbc-complex-ses-homology-long-exact.
- lem-weil-pbc-complex-ses-long-exact-naturality.
- def-weil-pbc-delta-functor (`Sheaf.CategoryTheory.DeltaFunctor`).
- lem-weil-pbc-derived-functor-injective-vanishing.
- lem-weil-pbc-effaceable-delta-functor-universal (`Sheaf.CategoryTheory.EffaceableDeltaFunctorUniversal`).

These are local proof-dependency removals, not assertions that no other target
branch needs those nodes. The item does not realize any fixed unit proof step;
the sk-thm-p1 unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The old node planned resolution/horseshoe glue, whereas the Lean statement uses
Yoneda extension classes directly. Mathlib's Ext.mapExactFunctor_comp and
Ext.mapExactFunctor_extClass support a shorter direct route. The universal
characterization is proved by dimension shifting rather than the separate delta
functor interfaces. LeanSearch was unavailable; Loogle, LeanFinder and local rg
confirmed the exact-functor Ext and injective vanishing APIs.

## New nodes

lem-weil-pbc-site-cohomology-pullback-data records the family/normalization notation
and the natural, injective degree-zero evaluation. All data is explicitly constructed.

lem-weil-pbc-site-cohomology-pullback-exists records the proved construction by the
free-sheaf generator, exact-functor Ext map, and precomposition.

lem-weil-pbc-site-cohomology-pullback-unique records the proved dimension-shifting
uniqueness lemma, requiring only two sites and an exact inverse image.

lem-weil-pbc-site-cohomology-pullback-composite records the proved composition law
for the three supplied normalized families and a unit-compatible isomorphism.

No change record is required: existing signatures and public imports are unchanged.

## Second reading by T1

1. PASS: compared the original module with the repository by diff, and independently
   compared its complete theorem signature without whitespace normalization. It is
   byte-for-byte identical. No existing definition, hypothesis, conclusion, visibility,
   or public import changed. The four helper modules and nodes are new, and no
   downstream module is adapted.
2. PASS: read every construction and proof in the five delivered modules. The free
   presheaf lift, sheafification lift, pullback generator, and Ext family are explicit
   constructions, with no arbitrary witness chosen from an unproved existence theorem.
   No delivered file contains sorry, axiom, unsafe, opaque, implemented_by, extern,
   or a kernel-check bypass. Compiled all helper modules and the repaired main theorem
   through lcompile.py. Independent scratch #print axioms checks show only propext,
   Classical.choice and Quot.sound for evaluation, its two properties, existence,
   and uniqueness. Composition and the original theorem additionally use sorryAx
   transitively from the existing exactness dependency; no delivered declaration
   introduces it directly. The delivery's per-declaration probe is the final check.
   The existing exactness theorem and its transitive dependencies remain outside this
   delivery's claim of closed holes.
3. PASS: no statement is split off with sorry, and none merely renames the whole target.
   Existence, uniqueness, and composition are separately proved parts of the argument.
   Checked degree zero by evaluation injectivity, positive degrees by the surjective
   boundary after embedding into an injective, and the orientation of e.inv by the unit
   equation and cancellation. Empty source categories make the family clauses vacuous;
   zero coefficients and degree one introduce no missing nonzero or positivity assumption.
   Repeated searches with different words using LeanFinder, Loogle, msearch grep, and rg
   on both source roots. Read Mathlib's freeYonedaHomEquiv, Ext injective vanishing and
   exact-sequence declarations, and related upstream cohomology bijectivity declarations.
   These provide ingredients or use another free-object presentation, not this complete
   normalized-family theorem. Search queries and results are logged in the sandbox.
4. PASS: the proof constructs the family via exact-functor Ext maps, rather than
   resolution/horseshoe glue, and uses the existing abelian inverse-image exactness theorem.
   Confirmed the old proof_deps removals listed above, including definitions and enough
   injectives still used through Mathlib and the new helpers. Checked sk-thm-p1.json:
   this item is not one of its realized statement or step nodes. The unit route is intact.
   New proof-only imports are plain import; the new composition module's Additive and
   abelian-sheaf construction imports support its signature. Removed its redundant
   finite-preservation proof import. Original public imports preserve existing visibility.
5. PASS: existing node fields changed only in proof, proof_deps and proof_origin.
   For every delivered node, proof_deps equals the union of the proof steps' uses,
   all cited nodes exist, and the recorded Lean declaration and module match the file.
   New nodes include source, searches, created, blueprint, chapter, unit, and lean records.
   The composition node describes its actual dimension-shifting induction. Repaired
   the data node's incomplete informal statement to specify evaluation, family notation,
   and all normalization clauses explicitly.

Second-reading changes: added a proof-only change to the abbreviated first conjunct
before assembling ExistsUnique. This avoids slow elaboration of the expanded statement;
the original proof timed out at 60 seconds twice, whereas the repaired file compiled
in 54.9 seconds. Removed the redundant finite-preservation import from the new composition
module, corrected its module blueprint label and proof explanation, repaired the data
node's informal statement, and recorded the independent searches and this review.
No hole was added, and no existing signature or definition changed.
