## What changed

Completed the saved reduction of
CategoryTheory.filteredHomologyCouple_quotient_pages without changing its signature,
visibility, or existing docstring. Added proof-only imports of
FilteredHomologyTowerQuotients, FilteredHomologyTowerDifferential, and the existing
FilteredComplexDifferentialRepresentativesCover.

The proof constructs each comparison isomorphism by the cokernel universal property:
the tower quotient composite is epic and its kernel is the boundary image. It proves
the page-zero normalization by cancelling the supplied epic representative map and
using the initial tower projection equation. It proves compatibility with every
supplied D by cancelling an epic simultaneous representative cover followed by the
tower quotient. Associativity, explicit index transports, and the cokernel comparison
projection equations combine the two calculations.

The two new modules each state one strictly smaller component of the original
induction, with source and full proof descriptions. Their normalization equations
uniquely determine all maps: j by its monic graded-cycle inclusion, t by the monic
tower inclusion followed by the initial isomorphism. No arbitrary witness is used
as data in a definition. The main theorem only eliminates their existential proof
inside a theorem. Updated the existing node's proof, proof_deps, and proof_origin.
No definitions, interfaces, target signatures, or other existing modules changed.

## Proved and sorry left

Closed the original textual hole in
CategoryTheory.filteredHomologyCouple_quotient_pages
(lem-sp-filtered-homology-couple-quotient-pages). The item contains no sorry.
This is a decomposition, not an unconditional proof of the mathematical result:
one original hole closed, two holes added, net minus one before downstream pruning.

Every added hole is listed here:

- CategoryTheory.filteredHomology_tower_quotients, in
  Sheaf.CategoryTheory.FilteredHomologyTowerQuotients,
  node lem-sp-filtered-homology-tower-quotients.
- CategoryTheory.filteredHomology_tower_differential, in
  Sheaf.CategoryTheory.FilteredHomologyTowerDifferential,
  node lem-sp-filtered-homology-tower-differential.

Both proofs are exactly `:= by sorry`. The first states normalized epic tower maps
and their boundary kernels, with no comparison isomorphisms or differential claim.
The second states a differential calculation on arbitrary simultaneous
representatives, with no existence of those maps or quotient isomorphisms. The main
proof supplies the cokernel comparison, normalization, and cancellation argument
that combine them; neither helper restates the whole original conclusion.

All three modules compile together without warnings via lcompile.py --all.
deliver3.py V2 Sheaf.CategoryTheory.FilteredHomologyCoupleQuotientPages --no-push
printed OK (dry run): compilation and preflight passed except for the second reading,
which the designated second reader writes. Nothing was pushed. The original theorem
signature and docstring were compared byte-for-byte and remain identical; all node
proof dependency unions and Lean line lengths were checked.

## No longer needed

No original import or module is pruned from the target closure. The old direct
proof dependencies def-sp-exact-couple and def-sp-filtered-complex-subquotients
are no longer direct steps of the main reduction and were removed from its
proof_deps. Both remain needed in the component lemmas' proof plans; this is
replacement of direct dependencies, not closure pruning. The old dependencies
def-sp-filtered-homology-exact-couple and
lem-sp-filtered-complex-page-differential remain direct dependencies.
Removed unused draft public imports of FilteredComplexPageDifferential from both
new helper modules, since their statements mention no differential data D and their
remaining imports supply their signatures. This is draft cleanup, not a claim of
pruning a module from the target closure.

The existing FilteredComplexPageHomology does not identify the concrete homology
exact couple or its differential with the filtered quotients, so it cannot by itself
close this item. Its underlying successor-cycle and boundary lemmas are cited in
the new quotient node's induction. No unrelated spectral-sequence construction or
first two-step quotient connecting comparison is imported into this proof.

## Where the brief, the DAG or earlier work was wrong

The earlier missing FilteredHomologyExactCouple.olean blocker is resolved in the
current compiled baseline. It was not rebuilt, copied, or bypassed by this worker.
The saved main proof had never reached elaboration: repairs were needed to supply
the explicit ShortComplex and its zero equation, use Mathlib's actual
comp_coconePointUniqueUpToIso_hom name, associate compositions correctly, and unfold
filteredComplexPageObject/filteredComplexPageπ during the final comparison.

Searched Mathlib through leanfinder, loogle, and grep; LeanSearch was attempted
and returned Internal Server Error, recorded as unavailable. Searched the source library and
Sheaf modules by rg. The logged searches give general homology/cokernel APIs, not a
ready comparison theorem. Read the existing successor-cycle and boundary-image
signatures and the concrete homology-couple maps. Read the source's cycle/boundary
and differential formulas at https://stacks.math.columbia.edu/tag/012K and derived
maps at https://stacks.math.columbia.edu/tag/011R. The node proof is an agent's
componentwise expansion of these sources, not a quotation of omitted source details.

Checked the new statements on zero complexes, zero differentials, filtration
positions outside the support, s=0, and negative p,q. For a zero differential,
Z_r=Z_1 and B_r=B_1 while the connecting and derived differentials vanish; the
claimed maps remain normalized epic quotients. At zero objects the maps are both
epic and monic, so no nonzero or projective-object hypothesis is needed. Arbitrary
representative objects A need not be projective: local lifts in the proof plan use
pullbacks along epimorphisms. Index shifts give total degree p+q+1 for every s.

The unit record has no realized statement or steps bypassed by this argument.
Blueprint searches for 'filtered cycles' and 'representative differential' found
no duplicate blueprint statement. blueprint_refs.py ancestor returns None for the
existing parent; the new nodes preserve its recorded thm-sp-spectral-object-yields
ancestry and extend its via chain rather than inventing another unit association.

## New nodes

lem-sp-filtered-homology-tower-quotients: normalized maps from filtered graded
cycles to the canonical tower cycles, with epic projection composite and precisely
the boundary kernel. Its induction uses the representative differential calculation
and existing successor-cycle cover and boundary-image statements.

lem-sp-filtered-homology-tower-differential: the exact-couple differential applied
to simultaneous filtered representatives, for every normalized family of maps.
Its plan uses the concrete connecting map and the derived-map restriction equations;
it does not depend on the new quotient-existence theorem. The two new nodes inherit
the parent's chapter, unit, source, and blueprint ancestry. No change record is
needed because all existing statements and definitions are unchanged.

## Second reading by V2

1. Compared the existing Lean module and node against the repository with diff.
   The existing theorem signature and docstring are byte-for-byte unchanged;
   only its proof, proof-only imports, and a local unused-variable linter option
   changed. No existing definition, interface, or other module was altered.
   Verdict: pass.
2. Independently compiled all three delivered modules via lcompile.py --all.
   The main reduction contains no sorry; exactly the two named component
   theorems remain sorry. There are no definitions in the new modules and no
   forbidden axiom, unsafe, opaque, implemented_by, or extern declarations.
   The reduction constructs comparisons by cokernel uniqueness, proves the
   initial normalization by epic cancellation, and proves the differential
   comparison by an epic representative cover. Axiom probes are recorded below.
   Verdict: pass as a decomposition, not an unconditional proof.
3. Checked both component statements against the concrete graded cycle and
   boundary definitions, initial connecting map, derived f/g restriction
   equations, and tower recurrences. The monic normalizations determine j and t
   uniquely. The statements are separate parts: quotient presentation and a
   representative differential equation; neither repeats the main theorem.
   Checked zero complexes, zero differential, s=0, negative indices, and a
   two-term vector-space complex with dx=y, x at filtration 0 and y at
   filtration 2. In that example d1 is zero, d2 is an isomorphism, and the next
   page vanishes, matching r=s+1 and the claimed kernels. Arbitrary A requires
   only epic pullbacks, never projectivity. Repeated leanfinder, loogle, and grep
   searches with connecting-morphism/cocycle-lift and colimit-uniqueness queries;
   results provide general tools but no existing full comparison. Also searched
   lean/ and read finiteCycle_formula, which shortens the family-existence plan.
   Both remaining holes require substantial representative/derived-couple work;
   neither can be closed by a brief application of an existing lemma.
   Verdict: pass after the proof-plan repair below.
4. Read the main proof from its conclusion downward and checked all imported
   helper uses. The Mathlib cokernel universal property is already used directly;
   no extra quotient-comparison hole is introduced. All three added main imports
   are proof-only and used; the new modules' public imports supply their types.
   Completed No longer needed with the two replaced old direct dependencies.
   The recorded unit sk-prop-av-pqf-finite has empty realized statement and step
   lists; this delivery changes no unit record or realized route.
   Verdict: pass; no module is pruned from the import closure.
5. Compared every node statement with its Lean signature, checked each proof_deps
   against the union of its proof-step uses, and checked sources, chapter/unit,
   blueprint ancestry, created fields, and Lean records of the new nodes.
   The existing node changes only proof, proof_deps, and proof_origin.
   Verdict: pass after updating the quotient helper's construction plan.

Changes made by this reading: clarified direct-dependency replacement in
No longer needed. Repaired a logical ordering gap in the quotient helper's
natural-language proof and DAG plan: its induction previously called the
representative differential lemma with a complete family while still
constructing that family. The revised proof constructs j and t at every stage
first, using the existing finiteCycle_formula and the initial connecting class
of da in F^(p+s+1), and only then inducts on epimorphy and boundary kernels.
Added lem-sp-finite-cycle-formula and def-sp-filtered-homology-couple-data to
that plan's dependencies. No Lean statement or executable proof was changed;
no additional hole was introduced. Counts remain one original hole closed,
two holes added (net minus one), with no closure pruning.

Independent #print axioms probes (lcompile.run temporary scratch copies):
CategoryTheory.filteredHomologyCouple_quotient_pages,
CategoryTheory.filteredHomology_tower_quotients, and
CategoryTheory.filteredHomology_tower_differential each report exactly
propext, Classical.choice, Quot.sound, and sorryAx. The last is expected from
the two listed component holes and existing open upstream statements; no
additional axiom occurs. All probes compiled and their temporary files were
removed. Automated comparisons also confirmed exact new-node Lean statement
text, existing signature/docstring identity, dependency-step unions, dependency
node existence, and 100-character line limits.
