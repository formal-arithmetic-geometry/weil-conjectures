## What changed

Reduced CategoryTheory.Functor.leftDerived_exact_when_defined to coherent Kan-extension
shifts and preservation of distinguished source triangles. Its remaining assembly is complete:
construct the source-composite IsTriangulated instance, represent every localized distinguished
triangle by Q of a source triangle via distTriang_iff, map the representation by LF, and use
closure under isomorphism. The coherent-shift construction is fully proved in its own module.
The source-triangle
assembly is also proved from the existing 05SC statement, the pointwise Kan bridge, and
one new comparison lemma, now fully proved.

Corrected the localization interface by adding [Q.IsLocalization S], the localization
assumption already required by the paper and the DAG. The original strict-property binder
is retained as _hQ. The original sole caller, LeftDerivedExactOfLocalization, compiles unchanged;
its constructed-localization instance supplies the new binder. See
coord/changes/leftDerived_exact_when_defined-localization.md. No target statements change.

Validation: all four delivery modules compile cleanly. The coherent-shift and triangle-value
comparison theorems each pass #print axioms with only propext, Classical.choice and Quot.sound.
The upper exactness theorem still uses the existing 05SC statement, whose proof is the next
needed item; this is the stage-3 proof from named dependencies, not a claim that the entire
import closure is already sorry-free.

## Proved and sorry left

Closed the body hole of CategoryTheory.Functor.leftDerived_exact_when_defined after the
explicit localization-interface correction. The corrected interface has a proved body and no new holes remain. This does not
claim a proof of the old fixed-universe signature; it is a recorded statement correction
with one body hole removed. The maintainer's pinned-baseline ledger determines net progress. These new declarations are
fully proved:

- CategoryTheory.Functor.rightKanExtension_coherentShift: canonical comparison isomorphisms
  by equivalence invariance of Kan extensions, with explicit zero and addition coherence.
- CategoryTheory.Functor.leftDerived_kan_map_source_distinguished: pointwise existence from
  the bridge and essential surjectivity; 05SC; comparison; closure under triangle isomorphism.

The comparison theorem CategoryTheory.Functor.leftDerived_kan_triangle_value_comparison is
now fully proved in its own module. It has no distinguishedness assumption or conclusion and
no everywhere-definedness hypothesis; it is a strictly smaller value-identification problem,
not a renamed exactness statement.
There are no delivery sorries left. No holes occur in definitions or in the original assembly,
the shift proof, or source-triangle assembly. The source-triangle theorem no longer needs a triangulation on L or exactness of Q;
those are used only in the proved descent in the item.

## No longer needed

Removed direct proof imports Sheaf.CategoryTheory.DerivedFunctorInverts,
Sheaf.CategoryTheory.DerivedFunctorShift, Sheaf.CategoryTheory.DerivedFunctorTriangles,
and Sheaf.CategoryTheory.LeftDerivedValueMorphism from the item.

The node lem-pur-derived-functor-inverts-05sb and module DerivedFunctorInverts are no longer
needed on this proof route: Q already inverts S, and LF sends those isomorphisms to
isomorphisms. No independent construction of a value functor or subsequent factorization is
needed, because the universal pair (LF, alpha) is supplied. The other three removed direct
imports are still needed below the source-triangle statement, through its dependencies;
they are not claimed as globally pruned. The 05R6 localization-triangle node stays needed
and is realized through the already-public Mathlib import. The unit has no realized proof
steps that this route bypasses. The old proof dependency
lem-pur-derived-functor-morphisms-05sa also disappears from the item's direct dependency
list but remains below DerivedFunctorTriangles / LeftDerivedValueMorphism; it is not globally
pruned. The new comparison node no longer lists lem-pur-total-left-derived-localization:
its proof uses the general Mathlib pointwise Kan API, not that derived-functor construction.

## Where the brief, the DAG or earlier work was wrong

The Lean strict-localization hypothesis did not expose the actual localization instance:
its test-target universes are fixed, not internally quantified over universes. This prevents
using the localization triangle and pointwise Kan APIs in the written plan. The change record
states the exact interface correction; the DAG already assumed abstract localization.
The supplied universal LF makes the original functor-construction and inversion steps
unnecessary. The Stacks source was read in /home/ubuntu/c1-stacks-review/derived.tex,
labels lemma-derived-shift, lemma-2-out-of-3-defined, and proposition-derived-functor.

Edge cases checked: Q the identity gives ordinary F and its shift structure; S all identities
also gives this case. The zero functor and zero triangles give zero derived triangles.
A general arbitrary CommShift on LF would not suffice for the source-triangle statement:
the explicit NatTrans.CommShift alpha hypothesis is essential and is supplied by the first
intermediate theorem. Generic coherent shifts do not require selecting an arbitrary witness
of essential constancy. Pointwise cones in the triangle comparison are used only through
their uniquely determined limit identifications.

## New nodes

lem-pur-right-kan-extension-coherent-shift (proved): the coherent action of integer shifts on a
right Kan extension, obtained by equivalence invariance and Kan uniqueness. Its source is
the shift-comparison assembly in 05SU/05SE; its statement is independent of triangulations.

lem-pur-left-derived-kan-source-triangles (proved): identification of the supplied Kan extension
with the 05SC triangle of values, using the bridge and 05SA uniqueness. It stops at source
triangles. The comparison uses split-mono cancellation rather than importing the 05SA uniqueness
and 05SU shift lemmas; both direct imports were removed from that new module.
All new nodes belong to sec-smooth-purity and sk-def-sf-operations. The whole-blueprint
searches found no duplicate generic Kan-shift or Kan-source-triangle statement.

lem-pur-left-derived-kan-triangle-value-comparison: fully proved, identifying
arbitrary compatible denominator-value triangles with Kan-extension image triangles. It
uses the bridge, fraction squares, split-mono cancellation, and shifted naturality. It does not
assert exactness or preservation of distinguished triangles.

Change record: coord/changes/leftDerived_exact_when_defined-localization.md.

## Second reading by V2

1. Compared all four delivered modules with the repository. Three are new; the sole existing
signature change is the declared addition of `[Q.IsLocalization S]` and renaming `hQ` to
`_hQ`. This adds a Lean hypothesis: it is a correction to the localization interface, not a
proof of the old fixed-universe signature. The mathematical node already assumes abstract
localization. The change record contains old/new signatures and the sole external caller;
I compiled that caller unchanged against the delivered modules. No definitions or target
statements change. Verdict: accept the documented correction for independent CODEX review.

2. Compiled all four modules locally with `lcompile.py --all`: no errors or warnings.
No delivery source contains `sorry`, forbidden axioms, unsafe/opaque declarations, or hollow
definitions. Scratch `#print axioms` checks give exactly propext, Classical.choice and
Quot.sound for the coherent-shift and triangle-value comparison theorems. The source-triangle
and upper theorem additionally have sorryAx from the existing 05SC dependency; this remains
an open import-closure obligation, not a new delivery hole. The private shift isomorphism is
chosen by a proved uniqueness API, and each value comparison is a unique limit identification.

3. Read all three new statements, proof bodies, docstrings and nodes. There are no remaining
split-off holes. Each is a strictly smaller problem: generic coherent shifts, distinguished
source triangles, or comparison with arbitrary compatible value triangles. Checked identity
localization and zero-triangle cases, and the need for counit shift compatibility in the last
triangle square. Independent LeanFinder searches for equivariant Kan extensions and localized
limit-value triangles, fully qualified Loogle IsRightKanExtension search, and grep of Sheaf,
upstream and Mathlib found generic uniqueness APIs but no duplicate of these statements.

4. Read the unit record sk-def-sf-operations: its steps and realized statement/steps lists are
empty, so this change bypasses no realized unit step. The 05SC source-triangle step and 05R6
localization descent remain. All six old proof dependencies are accounted for above: inversion
is bypassed, morphisms/shift/triangles remain below the source-triangle proof, and localization
triangles and the saturated-system definition remain direct. Corrected a proof-only public
Pointwise import in the new source-triangle module to a plain import, while publicly importing
Basic for the Kan hypothesis. The comparison module still needs Pointwise publicly for its
HasPointwiseRightKanExtension hypothesis.

5. Compared node Lean records and proof/dependency lists with the code. Removed the unused
lem-pur-total-left-derived-localization dependency from the new comparison node: the proof
uses Mathlib's general pointwise Kan theorem instead. Other records match the proof route;
the new nodes have source, searches, creation metadata, blueprint, unit and Lean records.

Second-reading changes: corrected import visibility, corrected the source-triangle docstring
and the item docstring to describe the actual Kan comparison and split-mono cancellation,
removed the spurious
comparison-node dependency, completed the old-dependency accounting, clarified the statement
correction and inherited sorryAx, and added this review. No proof body needed repair.
