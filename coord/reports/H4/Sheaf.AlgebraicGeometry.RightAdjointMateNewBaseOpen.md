## What changed

Replaced the sorry in `AlgebraicGeometry.rightAdjoint_mate_newBase_open` with a compiling
reduction to two strictly separate steps: horizontal factorization through the actual
canonical open-square mate, and invertibility of that open-square mate. The original
statement, universes, hypotheses, visibility and definitions are unchanged.

The proof constructs the iterated pullback's canonical lifted direct image, obtains its
right adjoint using `schemeDerivedDirectImage_qcqs_hasRightAdjoint`, and obtains ordinary
base change using `proper_flat_rightAdjoint_baseChange_hβ`. It constructs q from
`isPullback_morphismRestrict`, verifies both projections, and constructs the natural
comparison δ from exact open restriction, the first projection equation and derived
pullback composition. A proved private helper `open_pullback_restriction_iso` supplies
exact restriction versus derived pullback, using the tensor/restriction adjunctions and
uniqueness of left derived functors as right Kan extensions. No object is defined from
an arbitrary existence witness; the selected right adjoint and derived-functor
comparisons have universal properties determining them up to natural isomorphism.

The factorization theorem gives an arrow isomorphism for the composite with a genuine
second mate. The other theorem makes only that second mate invertible. The final Lean
argument constructs an arrow isomorphism by `Arrow.isoMk (Iso.refl _) (asIso t)` and
composes it with the factorization. It never assumes either of the original two mates
invertible. This is a decomposition, not an independent proof of all its dependencies.

Added proof-only imports of `ProperFlatOpenSquareMateIso`, `NewBaseOpenMateFactorization`,
`ProperFlatRightAdjointBaseChangeHbeta` and Mathlib's `PointwiseLeftDerived`. The public
imports of the original module stay unchanged. The declaration-scoped heartbeat limit
is 800000 because checking the two QCoh lifts and iterated pullback comparisons needs
additional definitional-equality work; the full module compiles in approximately
30 seconds, within the single-file limit. No linter is disabled.

New obligation modules also import the recorded direct-image composition and restriction
proof dependencies so the DAG plan is available to their future workers. Removed the
unused Arrow and DerivedOpenRestrictionMaps public imports from the new open-invertibility
module: its statement needs neither. These were never existing library imports.

The new factorization statement assumes only qcqs f. It neither imports nor uses the
proper-flat open invertibility theorem, so that the two remaining obligations can be
proved independently. Its δ is supplied, rather than hidden in an existence assertion.
The main proof constructs δ itself.

Sources read: official Stacks pages [0ATR](https://stacks.math.columbia.edu/tag/0ATR),
[0E9S](https://stacks.math.columbia.edu/tag/0E9S),
[0E4J](https://stacks.math.columbia.edu/tag/0E4J),
[0A9L](https://stacks.math.columbia.edu/tag/0A9L) and
[0ATM](https://stacks.math.columbia.edu/tag/0ATM).
The local checkout does not contain the downloaded Stacks tex files. The corresponding
source tags were read on the official website. The unit record
`sk-thm-picard-duality` is unchanged; this is a below-unit refinement of the same route.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.rightAdjoint_mate_newBase_open`
(node `lem-sc-right-adjoint-mate-new-base-open`). Its proof is complete from the named
intermediate statements. Also proved the private helper
`AlgebraicGeometry.open_pullback_restriction_iso`; it contains no sorry.

Added exactly two holes, each a public theorem with proof exactly `:= by sorry`:

- `AlgebraicGeometry.proper_flat_openSquare_mate_isIso`
  (`lem-sc-proper-flat-open-square-mate-isiso`, module
  `Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso`): only the canonical mate for an
  affine open immersion is invertible, independently of any ambient g or outer mate.
- `AlgebraicGeometry.newBase_open_mate_factorization`
  (`lem-sc-new-base-open-mate-factorization`, module
  `Sheaf.AlgebraicGeometry.NewBaseOpenMateFactorization`): the composite with the actual
  second mate agrees with the outer mate under endpoint comparisons, without assuming
  the second mate invertible, and under only qcqs hypotheses on f.

No sorry remains in the original module. One hole closed and two added is a decomposition
(net minus one before any downstream pruning), not a net decrease in holes. Neither new
statement is the original theorem renamed or with its conclusion supplied as a premise.
Factorization alone does not yield the desired arrow isomorphism: cancelling its actual
second mate requires the separate proper-flat invertibility step and the Lean cancellation
argument in the original module.

## No longer needed

Removed the direct proof import of
`Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen` from the original module.
That module and its node `lem-sc-proper-flat-right-adjoint-restriction-open` remain needed
through `ProperFlatOpenSquareMateIso`; they are not globally pruned.

No original dependency node or module is claimed globally pruned. Of the old direct proof dependencies, `def-pc-derived-base-change-map` and
`lem-sc-proper-flat-right-adjoint-restriction-open` are now needed transitively through
the two new obligations rather than as direct steps. The other three remain direct
steps: restriction, pullback composition and the canonical mate definition. All five
remain in the target import closure. Factorization's module needs no properness, flatness or finite
presentation imports; its public statement uses only qcqs f. No bypass of a blueprint
unit's statement or proof step was made.

## Where the brief, the DAG or earlier work was wrong

The existing restriction-open theorem states invertibility of restriction of the
right-adjoint image of the open unit, rather than the full canonical open-square mate.
Its application alone does not produce the target comparison required here. The bridge
through the inverse conjugate and open counit is now explicitly isolated in
`proper_flat_openSquare_mate_isIso`, with its complete proof in words.

The horizontal pasting step also has no existing scheme-derived Lean declaration with
the needed transported endpoint comparisons. Mathlib has `mateEquiv_hcomp` and
`conjugateEquiv_comp`, but these do not by themselves identify the chosen derived
pullbacks, adjunctions, ordinary base-change maps and the supplied right adjoints.
`newBase_open_mate_factorization` states this separate computation precisely.

LeanSearch returned HTTP Internal Server Error and is recorded as unavailable, not as a
negative search. LeanFinder and grep located underived open adjunctions and generic
mate/conjugation composition, but no exact replacement. Blueprint searches for `0E4J`
and `base change compose` found no duplicate blueprint nodes; DAG and library searches
also found no existing versions of the new declarations. The support criterion and
existing restriction theorem were read, and remain dependencies of the open step.

Edge cases checked against the statements: W may be empty or all of Y′ (when affine),
K may be zero or unbounded, r and q can be any isomorphisms satisfying the projection
identities, and neither the global nor outer mate need be invertible. For a different
supplied natural δ, its difference from the canonical comparison is a natural
automorphism of restriction; naturality at the first mate changes the source endpoint
isomorphism, so factorization remains valid. Changing the supplied right adjoints or
their adjunctions is handled by uniqueness of right adjoints. The factorization statement
does not infer open invertibility from qcqs assumptions.

## New nodes

`lem-sc-proper-flat-open-square-mate-isiso`, in
`dag/nodes/sec-picard-framework/`, records the full canonical open-square mate
invertibility from Stacks 0E4J and equation 0A9L. Its module contains only this named
public theorem with source and complete proof in words.

`lem-sc-new-base-open-mate-factorization`, in the same chapter, records the horizontal
composition formula from Stacks 0ATR and 0ATM with the projection and right-adjoint
transport required by the original item. Its module contains only this named public
theorem with source and complete proof in words. It has no dependency on the new
open-square invertibility node. Both nodes inherit the original chapter and unit,
record actual searches, and attach verbatim Lean signatures.

The original node's proof, proof_deps and proof_origin now describe the compiled
reduction. No definition or statement was changed, and there are no forced adaptations
or change records.


## Second reading by H4

1. Compared the delivered original module with the repository using diff and compared
   the theorem signature as text: byte for byte identical. Public imports and existing
   visibility are unchanged; only private proof support and proof-only imports were added.
   The original node changes only proof, proof_deps and proof_origin. No change record is
   required. Verdict: pass.
2. Compiled all three modules in import order with lcompile.py (10–27 seconds per file).
   The main theorem and its private helper contain no sorry. The only two added sorries
   are the named public obligations listed above. Checked for all forbidden constructs;
   none occur. A temporary appended #print axioms of the main theorem reports exactly
   propext, Classical.choice, Quot.sound and sorryAx. Right-adjoint choices are determined
   by adjunction universal properties, and comparison choices are functor isomorphisms;
   no arbitrary object is manufactured from mere existence. Verdict: pass as a decomposition.
3. Read both obligations, their docstring proofs, the original dependencies and the
   canonical mate definition. Checked Stacks 0ATR, 0ATM, 0E9S and 0E4J directly. The open
   obligation is a special case independent of g; factorization is horizontal pasting
   under qcqs hypotheses, independent of proper-flat open invertibility. Neither merely
   renames the target. For arbitrary supplied delta, write delta = alpha followed by the
   canonical comparison; naturality R(mu) ≫ alpha(target) = alpha(source) ≫ R(mu) adjusts
   the source endpoint iso. Empty W, zero K, identity squares and changed right-adjoint
   choices introduce no extra assumptions. Independent LeanFinder search for Beck-Chevalley
   transformation pasting found underived open restriction/composition only; Loogle and
   grep found generic adjunction/mate ingredients, not an exact replacement. Also read
   the private objectwise comparison in TorAmplitudeOpenLocal: it cannot replace the
   natural functor comparison used here. Neither obligation can be closed by a short
   application of existing declarations. Verdict: true, needed, strictly separate steps.
4. Read top-down construction and cancellation: q and its projections are constructed,
   delta comes from derived universal properties and pullback composition, and only the
   open-square mate is inverted. Imports of the new obligation modules retain their
   recorded proof plans; public imports are needed by their signatures. The old direct
   restriction-open import is removed, but remains transitively required. Clarified the
   two old dependencies now used transitively under No longer needed. No module is
   globally pruned; the unit record and its realized route are untouched. Verdict: pass.
5. Checked all three node signatures against Lean and their proof step dependency unions.
   New nodes have source, full informal proofs, searches, creation, blueprint, unit and
   Lean records. Added the canonical mate definition to the original node's final step
   and proof_deps, since that step constructs its arrow explicitly. Verdict: pass after
   this metadata correction.

Second reading changed only dependency metadata and this report (including the explicit
old-dependency accounting); the compiling Lean proofs needed no repair. One original hole
closed, two holes added: net minus one, a decomposition rather than a net proof gain.
