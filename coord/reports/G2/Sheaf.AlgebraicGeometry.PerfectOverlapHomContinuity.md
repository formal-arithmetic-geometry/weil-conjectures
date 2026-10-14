## What changed

Completed the earlier attempt's reduction of
`AlgebraicGeometry.perfect_overlap_hom_continuity`. The original theorem keeps its
signature. It obtains comparison data and a geometric presentation, applies the
proved `AlgebraicGeometry.PerfectHomPresentation.toSystem`, and packages the same
data with the resulting directed Hom system.

The new `PerfectHomPresentation` module proves the transfer theorem. Its transport
is the stage equivalence, canonical pullback transport, and inverse stage equivalence.
Its five laws use functoriality, the pin equation, `perfectLimitMap_stage`, and the two
clauses of `perfect_hom_continuity`. The presentation statement contains no lifting,
eventual equality, or stage transport, so this is a proper geometric part of the
argument rather than a renamed continuity theorem.

The three unchanged type definitions move to `PerfectOverlapHomContinuityData` to
avoid a cycle between the item and the geometric presentation module. Their names,
bodies, signatures, universes and public visibility remain unchanged, with a public
import from the original module. See
`coord/changes/perfect-overlap-hom-continuity-data.md`. No other module is adapted.

The earlier main proof timed out at reduction of the geometric presentation statement
and inference of the system's dependent category instances. Explicitly unfolding the
presentation proposition, applying it separately, and applying `toSystem` to the
expected system goal fixed this. The final file needs no irreducibility attributes,
profiler settings, or diagnostic traces; it compiles in approximately seven seconds.
The helper files compile individually within the 60-second limit.

## Proved and sorry left

Closed the item's sole hole:
`AlgebraicGeometry.perfect_overlap_hom_continuity`
(`lem-pc-perfect-overlap-hom-continuity`).

Also completely proved `AlgebraicGeometry.PerfectHomPresentation.toSystem`
(`lem-pc-perfect-hom-presentation`), including preservation of identities,
composition, and limit images, lifting, and equality on every later stage.

Added exactly one hole:
`AlgebraicGeometry.perfect_overlap_hom_presentation`
(`lem-pc-perfect-overlap-hom-presentation`), whose body is exactly `:= by sorry`.
Its docstring and node give the full geometric construction and the pinning argument.
No other delivered declaration contains sorry. This is a decomposition with one hole
closed and one added, not a net reduction in holes or an axiom-free proof of continuity.
The proved transfer theorem uses the existing continuity and composition interfaces;
remaining dependencies of those declarations are not claimed closed.

Edge cases checked in the argument: empty and coincident opens use the same cartesian
and site comparisons; zero perfect objects require no changes; the stage j itself
inhabits the tail, and preorder antisymmetry is never needed. All four ordered pairs
of Bool objects are covered. The apex equivalence identifies RW(E) with the direct
limit pullbacks via the prescribed phiU and phiV, rather than presuming E perfect.
The construction never selects data from the new holed theorem in a definition:
its existential data is eliminated only inside a proposition proof.

## No longer needed

No mathematical dependency module or DAG node is pruned: the geometric comparison
work and existing perfect Hom continuity are still needed through the two presentation
modules. The main module replaces its direct proof imports
`Sheaf.AlgebraicGeometry.PerfectHomContinuity`,
`Sheaf.AlgebraicGeometry.DerivedPullbackComposition`,
`Sheaf.AlgebraicGeometry.DerivedPullbackPerfect`, and
`Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses`
with `Sheaf.AlgebraicGeometry.PerfectOverlapHomPresentation`. Their work remains
transitively required. The original public imports for the three relocated definitions
are preserved transitively through `PerfectOverlapHomContinuityData`.
No inverse lifting or overlap-isomorphism descent is introduced here.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt left a main proof that exceeded the compiler budget, and no
report or node files for its new modules. This attempt repairs the elaboration and
supplies those records. No mathematical error in the original statement was found.
The existing proof-dependency declarations do not directly supply the simultaneous
coherent comparison diagram and its pinned Hom equivalences. That geometric part
is the one remaining theorem, rather than an unsupported application of continuity.

The new nodes serve the same Tag 09RF two-open descent step below
`lem-pc-rf-perfect-base-change`. The unit record's realized statement and steps are
empty; no unit-level statement or step is bypassed. Blueprint searches for
`Hom presentation`, `two-open`, `09RE` and `0D5S`, and library/node searches found no
existing exact pinned presentation. LeanFinder, Loogle and Mathlib grep returned
restriction or equivalence tools rather than this statement. LeanSearch returned
Internal Server Error and is recorded as unavailable, not as no match.
Read sources online: Tag 09RE, lemma-descend-homomorphisms and its open-local proof;
Tag 08DW, restriction compatibility in its proof; Tag 0D5S, K-flat composition proof.

## New nodes

`def-pc-perfect-overlap-hom-continuity-data` records the relocated existing types;
there are no choices of inhabitants and no holes in their definitions.

`lem-pc-perfect-hom-presentation` records the pinned geometric presentation interface
and the proved categorical transfer theorem. It retains the actual functors and
comparisons through its pin equation.

`lem-pc-perfect-overlap-hom-presentation` records the geometric restriction and
base-change comparison part still to prove. It supplies perfect overlap objects and
Hom equivalences, not any continuity conclusion.

Change record: `coord/changes/perfect-overlap-hom-continuity-data.md`.

## Second reading by G2

1. Compared the delivered main module with the repository and compared each of
   the three relocated declarations with its original text. Verdict: the main
   theorem's signature is byte for byte unchanged; all relocated signatures,
   fields and definition bodies are unchanged. The declared relocation and public
   re-export are covered by the change record; no target statement changes.
2. Compiled all four delivered modules in import order using lcompile.py: all
   pass without warnings. A scratch import printed axioms for all eight primary
   declarations. The five types/structures use only propext, Classical.choice and
   Quot.sound. The transfer theorem and two proposition proofs additionally use
   sorryAx, through still-open dependencies and the single reported new theorem.
   Inspected all delivered sources: one named theorem has sorry; no definition
   does, and there are no forbidden trust escapes. The existential geometric
   witnesses are eliminated inside the main proposition proof, never chosen in a
   definition. Verdict: valid conditional proof, explicitly a decomposition.
3. Read the remaining geometric theorem and its entire presentation structure.
   Its content is only cartesian/open-site comparisons, two perfect restrictions,
   Hom equivalences and their pin equation; it does not assume lifting, eventual
   equality or transport. This is strictly the geometric part of the original
   argument, while toSystem proves the continuity transfer. Empty overlap, equal
   opens and zero objects require no nonempty-space assumption; j itself is in
   the tail, so no antisymmetry is needed. The apex identifications use the given
   phiU and phiV, not an assumption that E is perfect. The docstring and node
   describe the full construction, including coherence and pinning. Independently
   read Stacks 09RE, 08DW and 0D5S and searched the library for pinned restriction
   presentations. New LeanFinder query about transferring filtered-colimit Hom
   continuity returned AB5 and ring coyoneda results; Loogle homEquiv search did
   not identify a matching declaration. Mathlib grep and local searches expose
   component tools, including existing single-open presentations, but none supply
   the simultaneous prescribed comparison diagram. Verdict: no duplicate or
   short missing application found; closing the geometric construction is beyond
   a short repair.
4. Reviewed the proof from the original theorem down through toSystem. Its five
   fields follow from stage/apex injectivity, the pin equation, perfectStageMap
   functoriality, perfectLimitMap_stage and both clauses of existing Hom
   continuity. The later-stage quantifier is preserved. Public imports provide
   symbols in statements/definitions; proof-only continuity is a plain import.
   The geometric module retains the proof-plan imports for its open theorem.
   All seven original proof dependencies remain needed transitively: perfectness,
   exact open restrictions, simultaneous diagrams, restriction comparisons,
   pullback composition, Hom continuity, and the directed-system interface.
   None is pruned. The unit sk-thm-picard-semicon has empty realized statement
   and step records; the same Tag 09RF two-open route remains. Verdict: route
   retained; no genuine unused mathematical dependency identified.
5. Opened all four node files and checked their statements against Lean, their
   sources, creation metadata, module mappings, proof steps and proof origins.
   Every proof_deps list equals the union of its steps' uses. The main node uses
   the geometric presentation and the proved transfer theorem; the latter uses
   the actual transport and continuity interfaces. Verdict: the DAG agrees with
   the conditional proof and its single geometric hole.

Second-reading changes: replaced whitespace-collapsed Lean signatures in the
three new node records with the literal multiline signatures from the modules,
and added this independent review and its axiom/edge-case evidence. No Lean
proof, declaration, definition or import required repair. The axiom scratch file
was removed before delivery. One original hole is closed and one geometric hole
is added, for net zero; toSystem is proved relative to its existing dependencies.
