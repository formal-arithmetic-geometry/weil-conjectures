## What changed

Replaced the sorry in AlgebraicGeometry.perfect_hom_open_comparison_mate_isIso
by a complete Lean proof from a strictly smaller normalization equation on
K-injective complexes. The existing statement and public imports are unchanged.
Added a proof-only import of PerfectHomOpenMateResolutionNormalization.

PerfectHomOpenModuleMate constructs the cartesian square, proves the induced map
is an open immersion, constructs the ordinary direct-image composition comparison,
and proves its inverse mate is invertible. Its component at W is explicitly
restriction along the equality b image pi-prime inverse W = pi inverse B image W.
This is proved using the ordinary adjunction formulas and functoriality of sections,
then reflected back through both forgetful functors.

PerfectHomOpenMateResolutionNormalization constructs the derived comparison by
right derivation of this proved ordinary isomorphism, exact open restriction,
and left-adjoint uniqueness. It also explicitly constructs the comparison for
arbitrary supplied adjunctions. One named counit equation on K-injective
representatives with canonical adjunctions remains. The main module proves
transport to all supplied adjunctions via conjugateEquiv_counit, naturality,
and cancellation of the open adjunction uniqueness isomorphism and its inverse.
The main proof identifies mate components with these
comparison components using the adjunction Hom equivalence, extends the equation
along the fixed K-injective resolution isomorphism by naturality, and applies
NatIso.isIso_of_isIso_app. No objects are selected from bare existence assertions.

The source tags 08FE, 08BS and 0D5S were read on the Stacks website; their local
literature filenames are listed in the DAG but the source texts are absent here.
Searches used the required msearch services and local rg in Mathlib and both
library roots. LeanSearch reported Internal Server Error (unavailable); Loogle
and LeanFinder supplied categorical and ordinary restriction APIs, not a theorem
for the normalized derived comparison. Search logs are in searches.jsonl.

## Proved and sorry left

Closed: AlgebraicGeometry.perfect_hom_open_comparison_mate_isIso (one original hole).
Added and left: AlgebraicGeometry.perfectHomOpenComparison_counit_resolution
(node lem-pc-perfect-hom-open-mate-resolution-normalization), whose proof is
exactly by sorry in its own module. This is a decomposition: one upper hole
closed and one lower hole added, net zero holes. The lower theorem is only the
canonical counit equation on K-injective representatives, with no arbitrary
adjunction parameters, not invertibility of the mate
on all derived objects. The independent ordinary isomorphism and the passage
from representatives to arbitrary objects and transport to arbitrary adjunctions
are fully proved.

Also proved: AlgebraicGeometry.perfectHomOpenSquare,
AlgebraicGeometry.perfectHomOpenMap_isOpenImmersion, and
AlgebraicGeometry.perfectHomOpenModuleMate_isIso. No other holes occur in the
delivered modules and no sorry occurs inside a definition.

The three ordinary proofs have only propext, Classical.choice and Quot.sound
under #print axioms. The main theorem still reaches sorryAx through the named
normalization obligation (and pre-existing dependencies); this delivery is not
a claim that the target import closure is sorry-free.

## No longer needed

The old route's separate use of lem-pc-restrict-derived-direct-image-open
(module Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction) is unnecessary:
its bare Nonempty comparison does not specify the mate. We construct and derive
the sectionwise comparison in the actual cartesian presentation instead.
This node is removed from the item's proof_deps; there was no direct import to
remove. The other removed old proof_deps are def-pc-derived-base-change-map,
lem-pc-ringed-spaces-derived-adjoint,
lem-pc-ringed-spaces-derived-pullback-composition, and
lem-sc-derived-k-injective-restrict-open. They are now used through the
normalization node or the retained public imports, rather than directly by
the main proof. This removes DAG edges, not their modules from the import closure.

No original public import was removed. The new ordinary module replaces
Mathlib.AlgebraicGeometry.PullbackCarrier with the smaller public import
Mathlib.AlgebraicGeometry.Pullbacks for the scheme pullback instances used
in its signatures and constructions. The carrier description is unused. OpenImmersionRestrictionDerivedProperties remains public because its
instances and properties are required to construct the public derived
comparison definition. A plain import was tested and Lean rejected it. PerfectHomOpenModuleMate uses only
KInjectiveMayerVietorisData and Mathlib.AlgebraicGeometry.Pullbacks;
it does not import the much larger DerivedMayerVietorisCanonicalData module.
No whole module is asserted globally unreachable: other consumers may need it.
The unit record has no realized statement or step nodes, and its route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The existing open-restriction theorem only gives Nonempty of an isomorphism;
it does not supply the required normalization equation or the pullback
presentation transport. The previous DAG's prose treated those as available
steps. This delivery writes the actual cartesian and ordinary-mate arguments
in Lean and isolates the missing derived normalization equation explicitly.
The target statement is neither disputed nor modified. No forced adaptation.
Empty/full opens and the zero complex are included: the sectionwise equality
and resolution transport use no nonemptiness or finiteness hypothesis.

## New nodes

lem-pc-perfect-hom-open-module-mate: ordinary module mate with cartesian-square
and open-immersion constructions; its isomorphism theorem is fully proved.

lem-pc-perfect-hom-open-mate-resolution-normalization: explicit derived and
supplied-adjunction comparisons and the remaining counit equation on K-injective
complexes. Its docstring gives the source proof and normalization details.
No change record is required; no existing signature, definition or visibility changes.

## Second reading by F3

1. Compared the only existing delivered module with the repository using diff,
and checked its declaration table. Verdict: the original theorem signature,
docstring, public imports and visibility are byte-for-byte unchanged. The two
other delivered modules are new; no adaptation or interface change is present.

2. Read all three modules and compiled them in import order through lcompile.py.
Verdict: the proof compiles. The sole remaining sorry is the named theorem
AlgebraicGeometry.perfectHomOpenComparison_counit_resolution. There is no sorry
in data, no forbidden declaration or kernel bypass, and no arbitrary existence
witness in the new definitions. Explicit #print axioms checks show only propext,
Classical.choice and Quot.sound for the ordinary square, open-immersion instance,
ordinary mate, and both constructed derived comparisons. The normalization and
main theorem additionally use sorryAx, as reported.

3. Read the normalization equation and its docstring against the actual choices
of composition counits and canonicalPullbackAdjunction. Verdict: it is the
canonical comparison counit equation on K-injective representatives, strictly
one part of the argument. The main proof separately establishes adjunction
transport and extension by resolution/naturality. Empty/full opens and zero
complexes introduce no exceptions to the sectionwise equations. Read Stacks
[08FE](https://stacks.math.columbia.edu/tag/08FE),
[08BS](https://stacks.math.columbia.edu/tag/08BS),
[079W](https://stacks.math.columbia.edu/tag/079W), and
[0D5S](https://stacks.math.columbia.edu/tag/0D5S).
Independent msearch queries used the phrases right-derived adjunction counit,
ordinary natural transformation, and cartesian restriction square; LeanFinder,
Loogle and grep found the derived adjunction factorization APIs, not this
normalization equation. Local searches also found DerivedDirectImageSquareMate
and DerivedPullbackCompositionMateUnit: these concern conjugation under both
projection and open adjunctions, and the latter still contains sorry; neither
identifies this mixed exact-restriction mate. MapDerivedCategoryMate requires
exact functors, and PlusAdjunction concerns bounded-below categories, so neither
applies to arbitrary unbounded projection pullbacks. No duplicate found. The
remaining equation is not a short closure by these APIs.

4. Read the main proof downward: mateEquiv_counit and Hom-equivalence injectivity,
then the normalized representative equation, then naturality along the fixed
resolution isomorphism. Verdict: the ordinary comparison is independently
constructed and proved, and the combination is a real reduction. This is a
one-for-one decomposition, net zero holes, not a completed import closure.
Checked every old proof_deps edge against the new list and corrected the
No longer needed section to enumerate all five removed edges. Checked
dag/units/sk-thm-picard-semicon.json: its realized statement and step lists
are empty, and no unit route is bypassed or changed.

5. Checked the three node files against the declarations, construction and
proof steps, including dependency unions, source, origin, creation, blueprint,
chapter/unit and Lean records. Verdict: they agree. Replaced the two new nodes'
condensed lean.statement strings with the verbatim theorem signatures. Existing
node statements and non-owned fields are unchanged.

Changes by this reading: replaced the unused carrier import with the smaller
public Pullbacks import, completed the removed-dependency list, and made the two new Lean signature
records verbatim. No proof or mathematical statement was changed.
