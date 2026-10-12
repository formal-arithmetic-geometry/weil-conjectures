## What changed

Proved AlgebraicGeometry.Proj.proj_sheafification_shortExact without changing its
signature. On each positive homogeneous chart, transport degree-zero localization
exactness along the given injective additive chart identifications. The positive
standard opens are a basis; pass to sheaf exactness and assemble ShortExact.

Added Sheaf.Algebra.Module.ProjAwayDegreeZeroExact for the algebraic chart step.
Added Sheaf.AlgebraicGeometry.Modules.BasisExactness and proved its theorem in Lean
from the existing local lifting criterion: the proof constructs the basis cover,
proves zero composite and monicity by sheaf separation, and supplies local lifts
for epicity and exactness. Its hypotheses are generic scheme/basis sectionwise
conditions, independent of Proj, gradings and localization.

All three modules compile locally. Updated the item's DAG proof to this route.
The existing theorem docstring records the original stalk route; the implemented
route is the equivalent standard-chart route documented by the node and helpers.

## Proved and sorry left

Proved AlgebraicGeometry.Proj.proj_sheafification_shortExact (the one original
sorry), node lem-sc-p1-proj-sheafification-exact.
Proved AlgebraicGeometry.Scheme.Modules.exactness_of_basis_sections,
node lem-sc-p1-module-basis-exactness, from
AlgebraicGeometry.RingedSpace.module_exactness_local_lifting.

The only new sorry is LocalizedModule.proj_away_degreeZero_exact,
node lem-sc-p1-away-degreezero-exact. It is strictly the algebraic single-chart
step; its statement involves additive groups and fraction maps, not sheaves or
categorical exactness. Existing imported standardOpenProperties and
module_exactness_local_lifting remain obligations outside this delivery.

Edge cases checked mathematically: f=0 (zero localizations), negative module
degrees (multiply by powers of positive-degree f), zero graded modules, empty
basis members, and the empty scheme. The generic sheaf theorem does not assert
surjectivity on arbitrary opens.

## No longer needed

Removed the item's private imports:
- Sheaf.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting (now used by BasisExactness).
- Sheaf.Algebra.Module.ProjDegreeZeroLocalizationExact.
- Sheaf.AlgebraicGeometry.ProjGradedModuleSheafExists.
- Sheaf.Topology.PresheafModuleStalkFunctor.
- WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules.

The implemented proof does not use the original stalk-route nodes
lem-sc-p1-proj-degreezero-localization-exact,
lem-weil-pbc-proj-graded-module-sheaf-exists, def-weil-pbc-module-stalk,
def-weil-pbc-proj-twisting-sheaf, or lem-sc-p1-proj-tilde-functorial.
These are removed from this node's proof_deps. Retained the existing public
ProjTildeFunctorial import to preserve the file's public import interface and
provide the statement's types; hence its transitive modules may remain reachable
from other import edges. No claim is made that these modules are globally unused.
The old direct dependency lem-weil-pbc-ringed-space-module-exactness-local-lifting
is also removed from the item's proof_deps; it remains required through the proved
generic basis lemma.
The new algebra lemma uses ordinary localization and homogeneous-component
exactness; no homogeneous-prime stalk localization is needed.

## Where the brief, the DAG or earlier work was wrong

The old proof plan is mathematically valid, but its Lean dependencies do not
connect directly: tilde_functorial requires supplied stalk identifications,
whereas this theorem supplies only chart data. The prime-localization theorem
also uses homogeneous denominators outside a prime, rather than powers of one
homogeneous chart element. A single-chart algebra lemma avoids that bridge.
The unchanged scalar and restriction hypotheses are unnecessary for this route:
i and q are already morphisms of module sheaves and their chart formulas suffice.
LeanSearch returned HTTP 500 for both new-node queries; this is recorded as
unavailable without a mathematical search verdict. LeanFinder, Loogle and
source grep were completed.
No statement is disputed, no existing definition or signature was changed, and
the unit's sheafification step is retained.

## New nodes

lem-sc-p1-away-degreezero-exact: algebraic exactness after degree-zero away
localization, transported to additive groups via chart identifications. New
module Sheaf.Algebra.Module.ProjAwayDegreeZeroExact; one named sorry.

lem-sc-p1-module-basis-exactness: categorical exactness of module sheaves from
sectionwise exactness on a basis. New module
Sheaf.AlgebraicGeometry.Modules.BasisExactness; fully proved from the existing
local lifting criterion. No change records are needed.

## Second reading by W2

1. Compared the delivered ProjSheafificationExact module with the repository
   using diff. The existing declaration, all hypotheses (including hscalar and
   hres), conclusion, and docstring are byte-for-byte unchanged. Changes are
   confined to its proof and private imports. Both helpers are new declarations;
   there are no definition changes or change records.
2. Compiled all three files in import order with lcompile.py, without errors or
   warnings. Searched the delivered Lean for forbidden constructs and sorries:
   the only sorry is the public named proj_away_degreeZero_exact. A scratch
   module printed axioms of all three delivered theorems; each has only propext,
   Classical.choice, Quot.sound and sorryAx. The latter is expected from the
   algebraic chart obligation and the existing local-lifting/basis obligations;
   this delivery does not claim an axiom-free closure of the target.
3. Read Constructions lemma-proj-sheaves (01M7), including its exact-functor
   paragraph, and Modules section-kernels and lemma-abelian (01AF/01AG) in the
   local Stacks copies at /home/ubuntu/c1-stacks-review/. The algebraic helper
   assumes exactly an internal integer grading, homogeneous scalar action,
   degree-preserving injective/exact/surjective maps, and injective chart maps
   with the prescribed ranges and fraction formulas. These suffice. For f=0,
   powers contain zero, all localizations are zero, and injective alpha makes
   the A_j zero. For f nonzero, f^m has the unique polynomial degree md, so its
   degree-zero numerator convention omits nothing, even for negatively graded
   modules. Clearing a finite homogeneous relation preserves distinct degrees,
   which validates internality after localization. Zero modules are included.
   The basis lemma uses naturality, separation and the existing local lifting
   equivalences correctly; its basis cover also works for empty W and empty X.
   It requires surjectivity only on basis members, not arbitrary opens.
   Repeated searches with different words: LeanFinder homogeneous localization
   degree zero exact functor graded module powers, Loogle Function.Exact with
   DirectSum, logged Mathlib grep, and rg over Sheaf and WeilConjectures.
   The upstream GradedLocalizationExact theorem covers middle exactness under
   an integer ring grading, but not injectivity/surjectivity and additive chart
   transport; ProjDegreeZeroLocalizationExact uses prime complements. Neither
   is an exact replacement. No duplicate or restatement of the sheaf target
   was introduced. Formalizing the internal localized grading remains the
   substantive algebraic obligation, not a few-minute closure.
4. Read the proof from the target downward. The standardOpenProperties basis
   clause and the new chart theorem give precisely hsections; the proved basis
   lemma supplies the categorical properties needed by ShortExact. The basis
   proof itself gives the explicit cover, zero composite and monicity, then
   applies the existing epi and exact local-lifting clauses. The positive chart
   route retains the graded-resolution sheafification step. The unit realized
   arrays do not name any of the replaced stalk-route nodes. The report now
   enumerates all six removed old direct proof dependencies, distinguishing
   the local-lifting node that is still used indirectly.
5. Compared each node with its Lean signature and proof: the original node uses
   exactly chart exactness, standard-open basis and basis exactness; the basis
   node follows separation and local lifting; the open algebraic node records
   ordinary localization, homogeneous components and transport. New lean
   statement fields match their declarations and have their required source,
   creation, blueprint, chapter and unit fields. Revised the algebraic proof
   step to match the expanded argument and repaired grep search records to
   use queries actually run and describe their actual results.

Changed: removed the unused public GradedModule import, reduced DirectSum.Module
 to DirectSum.Basic, and reduced the basis helper's ShortExact import to Exact.
Expanded the new algebraic helper's docstring with the f=0 case, unique
 denominator degrees, construction and independence of localized components,
 and explicit transfer of exactness. No existing statement was changed.
