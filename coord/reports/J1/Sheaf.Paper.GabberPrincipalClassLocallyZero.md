## What changed

Proved AlgebraicGeometry.Etale.gabber_principal_class_locally_zero with its signature
unchanged. The proof transports strict henselianity from R_p to the stalk of D(h),
uses the upstream positive-degree Ext vanishing theorem, spreads vanishing to an
open neighborhood, chooses a principal neighborhood, and uses pullback composition.
A private, fully proved factorization helper handles the final cohomological step.

Added Sheaf.Paper.EtaleClassVanishingSpreads with the proved theorem
AlgebraicGeometry.Etale.etale_class_vanishing_spreads. It derives the global-class
vanishing criterion from the existing etaleCohomology_localRing_colimit statement,
including its comparison and elementwise vanishing clauses. Both modules compile
without warnings through lcompile.py --all. The original public imports stay unchanged;
all new dependency imports are private proof imports.

Edge cases: q=0 is allowed in the continuity bridge, which assumes the actual local
pullback vanishes; it does not assert degree-zero local vanishing unconditionally.
The principal-class theorem retains q>0. When h=0 or R is the zero ring there are
no primes avoiding h, and the point-dependent argument is vacuous. The refinement
uses D(fh) contained in D(f), so no invertibility or nonzero-divisor assumption on h
is introduced. No torsion hypothesis is introduced.

## Proved and sorry left

Closed the sole original hole:
AlgebraicGeometry.Etale.gabber_principal_class_locally_zero
(lem-weil-pbc-gabber-principal-class-locally-zero).

Added and proved AlgebraicGeometry.Etale.etale_class_vanishing_spreads
(lem-weil-pbc-etale-class-vanishing-spreads). No new holes; zero split off.
There is no sorry in either delivered module. The proof still depends on the existing
sorry in AlgebraicGeometry.etaleCohomology_localRing_colimit; that is an existing
stage-3 dependency, not a newly added hole. This delivery proves from the library's
stated dependencies and does not claim to eliminate all transitive sorryAx usage.

## No longer needed

Removed the private imports Sheaf.AlgebraicGeometry.ZariskiCohomologyLocallyZero and
Sheaf.Paper.StrictHenselianZariskiEtaleComparison. The item no longer directly uses
lem-weil-pbc-zariski-cohomology-locally-zero or
lem-weil-pbc-gabber-strict-henselian-zariski-comparison. Their modules are unnecessary
for this item's route; other target routes may still reach them.

Kept Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial and the spectrum-stalk
Mathlib dependency. Added the upstream StrictlyHenselian and CohomologyMap modules
and the continuity bridge. The unit's statement and realized proof steps remain
untouched; the replaced comparison route was strictly below that level.

## Where the brief, the DAG or earlier work was wrong

The comparison dependency has a corrected, detailed canonical-map interface and
lives at Scheme.{u+1}, while the local Zariski vanishing theorem uses coefficients
AddCommGrpCat.{u} on Scheme.{u}. They are not immediately composable for this item's
AddCommGrpCat.{u+1} coefficients. No correction of their statements is attempted.
The existing local-ring colimit theorem and the upstream Ext acyclicity theorem
provide a shorter compatible route.

The original spectrum-stalk node also mentions function fields of domains; only its
prime-localization clause is used, with no domain assumption. Pullback functoriality
is required in all degrees; the upstream cohomologyMap_eq_zero_of_fac helper only
covers degree one, so the private helper derives the needed version from the existing
all-degree functoriality theorem.

## New nodes

lem-weil-pbc-etale-class-vanishing-spreads, in
lean/Sheaf/Paper/EtaleClassVanishingSpreads.lean, is a proved specialization of the
local-ring cohomology colimit statement to a global class. Its proof includes the
actual neighborhood diagram, both comparisons, the filtered-colimit vanishing
criterion and removal of coefficient transports. It does not repeat the item's
conclusion: it applies to arbitrary schemes and degrees, assumes local vanishing,
and neither proves henselian acyclicity nor chooses a principal open. No change
record is needed because no existing public signature or public import changed.


## Second reading by J1

1. Compared the existing module to the repository with diff and the delivery declaration
   parser. The full existing theorem signature is byte-for-byte identical. No existing
   definition, public import or target statement changes. The only added declarations
   are a private proved factorization helper and the new proved continuity theorem.
   Verdict: pass; no change record required.

2. Compiled both modules in import order through lcompile.py --all, without warnings.
   Read both proofs, including the coefficient transports and open-immersion factorization.
   Neither delivered file contains sorry, axiom, unsafe, opaque, implemented_by or extern,
   and neither introduces a definition with chosen data. Appended #print axioms in
   temporary probe copies through lcompile: both public theorems use only propext,
   Classical.choice, Quot.sound and sorryAx from existing dependencies. The local-ring
   colimit theorem remains unproved upstream in this project. Verdict: pass as a proof
   from stated dependencies, not a claim of complete transitive axiom closure.

3. No statements are split off with sorry. The new continuity theorem is fully proved
   from the canonical object-cohomology local-ring colimit statement. Checked q=0:
   local pullback vanishing remains a necessary hypothesis; a nonzero constant section
   is not asserted to vanish. For an empty scheme there is no point x; for h=0 or a
   zero ring the principal theorem has no prime avoiding h. The principal refinement
   requires no invertibility assumption. Searched independently using leanfinder
   (cohomology class restricts to zero on neighborhood if zero in stalk), loogle
   (CategoryTheory.Sheaf.H, AlgebraicGeometry.Scheme), and rg over Sheaf, upstream
   Sites and Mathlib SheafCohomology. No existing theorem replaces the new bridge.
   The structure-sheaf germ lemma is a different statement; the upstream factorization
   lemma is only degree one. Verdict: pass; zero new holes, no restatement reduction.

4. Checked the route from strict-local Ext acyclicity through continuity to a principal
   neighborhood. Each private import is used; public imports provide the signatures.
   Both obsolete proof dependencies, the strict-henselian Zariski comparison and
   Zariski local vanishing, are listed under No longer needed. The new route is below
   the unit level: neither removed node realizes a statement or step in
   dag/units/sk-thm-p1.json, and all of that unit's realized entries remain untouched.
   Read the original source arguments at [Stacks 0GY0](https://stacks.math.columbia.edu/tag/0GY0),
   [09AX](https://stacks.math.columbia.edu/tag/09AX) and
   [03QO](https://stacks.math.columbia.edu/tag/03QO); local literature copies are absent
   on this machine. Verdict: pass; no missed shorter all-degree route found.

5. Compared both nodes to the Lean code. The original proof_deps now names stalk
   localization, strict-local acyclicity, the continuity bridge and pullback composition;
   the acyclicity is taken from the proved upstream Ext theorem, as the proof text now
   explicitly records. The new node has statement dependencies, source, proof steps,
   proof origin, searches, creation/blueprint metadata, chapter/unit and Lean record.
   Its proof_deps are precisely local-ring continuity and pullback functoriality.
   Verdict: pass.

Second-reading changes: corrected the principal theorem's stale natural-language proof
and source citations to describe strict-local acyclicity and continuity; clarified the
node's upstream Ext use and proof origin; recorded the independent searches; removed
trailing whitespace. The compiled proof terms and all existing signatures were retained.
The sole original hole is closed, no hole is added, and zero statements are split off.
