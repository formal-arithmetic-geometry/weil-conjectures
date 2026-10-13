## What changed

Proved `AlgebraicGeometry.Scheme.exists_completed_cover_with_quotient_iso` in
`Sheaf.AlgebraicGeometry.Morphisms.CompletedQuotientCoverLift`, with its entire original
signature and visibility preserved. Added four proof-only imports:
`Mathlib.RingTheory.AdicCompletion.LocalRing`,
`Mathlib.RingTheory.AdicCompletion.Noetherian`,
`Sheaf.RingTheory.AdicCompletionNoetherian`, and
`Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete`.

Three proved private helpers supply completeness for subideals of the maximal ideal,
restriction/pullback comparison, and base change of an isomorphism over its base.
The first proves the closedness step using Hausdorffness of each finite quotient module.
The main proof constructs the quotient ring map, lifts the whole quotient cover using
`exists_finiteEtale_lift_of_isAdicComplete` with the proper identity of Spec C, and
composes the explicit pullback isomorphisms. Every projection equality is proved.
No definition, public statement, target, or other module changed. Updated only the
proof, proof_deps and proof_origin of lem-sbc-completed-quotient-cover-lift.

The source was read at https://stacks.math.columbia.edu/tag/0BLS,
https://stacks.math.columbia.edu/tag/09ZL,
https://stacks.math.columbia.edu/tag/0ALJ and
https://stacks.math.columbia.edu/tag/0GS2. The last supplies the existing complete-base
lifting declaration used here. The unit sk-prop-input-spreading has no populated
realized entries; its route is preserved. This work implements the quotient-cover
lifting input without changing any unit statement or step.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.exists_completed_cover_with_quotient_iso`
(lem-sbc-completed-quotient-cover-lift).

The item contains zero sorries. Added zero holes and split off zero statements.
The private helpers `complete_subideal`, `restrict_pullback_iso`, and `base_change_iso`
are fully proved. This is a proof from existing library inputs, not a new decomposition.
The imported lifting and Noetherian-completion inputs retain their existing downstream
proof dependencies; this report makes no claim that their whole axiom closures are closed.

Checked edge cases in the construction: f=0 gives J=0 and the same Cauchy-sequence
argument; U empty and an empty supplied cover require no changes to the pullback proof.
No regularity, depth, reducedness, or nonemptiness hypothesis was introduced.
The file compiles through lcompile.py with no errors or warnings and no textual sorry.

## No longer needed

Removed from this node's proof_deps: def-weil-pbc-henselian-terminology.
The proof applies the complete Noetherian lifting input directly, so it does not need
henselianity, the full equivalence of finite etale categories, or full faithfulness.
`WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale` was considered but is not
imported; neither its H1-comparison nor general henselian lifting dependencies are
introduced by this delivery. No pre-existing public import was removed, and no
pre-existing library module is claimed to have left the global targets' closure.
All other original proof-dependency definition nodes are still used. The required
Noetherianity, Krull intersection and complete-base lifting nodes are now explicit.

## Where the brief, the DAG or earlier work was wrong

The original plan supplied definitions for its two substantive algebraic steps,
without naming the existing Noetherian completion and finite etale lifting theorems.
Those existing declarations suffice. The closedness argument hidden in step 1 is
now proved directly in Lean using separated finite quotient modules.

The existing declaration docstring describes the henselian-equivalence proof; it
was preserved. The delivered proof and updated DAG use only the complete-base
essential-surjectivity theorem, a source-supported special case of that route.
No statement was disputed or changed. No tools were bypassed or edited.

Searches before implementing: leanfinder for finite etale quotient lifting over a
complete Noetherian local ring returned standard-etale/formal-smooth lifting facts,
not the scheme-cover statement; loogle for IsAdicComplete with an ideal inclusion
returned completion universal-property results, not smaller-ideal completeness;
grep for completion/henselianity found no direct match. Repository search found
AdicCompletion.isNoetherianRing and the complete-base lifting declaration, which
are the two non-Mathlib theorem inputs used. No new nodes or change records.


## Second reading by A2

1. PASS: Read the full module and diff against the repository. Compared the original
   theorem signature byte for byte through its proof delimiter: identical. Original
   imports, visibility, docstring, universes and definitions are unchanged. No other
   module is delivered and no interface change record is needed.
2. PASS: Independently compiled the delivered file using lcompile.py (4.9 seconds,
   zero errors or warnings). A scratch copy printed axioms of the three private
   helpers and the public theorem. Every helper uses only propext, Classical.choice
   and Quot.sound. The public theorem additionally uses sorryAx through existing
   imported inputs; its own proof contains no sorry. No axiom, unsafe, opaque,
   implemented_by, extern or data definition was added. Existential lifting is
   eliminated only inside a theorem proof, not used to define arbitrary data.
3. PASS: No statements or holes were split off, so no new-node search is required.
   Independently read all private helper proofs. The quotient R/J^n is a finite
   R-module, hence maximal-ideal-adically separated by the Mathlib Noetherian
   instance; the max(n,k) comparison proves the required congruence. This works
   for J=0, n=0, empty opens and empty covers without additional hypotheses.
   The restriction and base-change helpers are standard pullback transport with
   explicit projection equations. The main construction has no regularity or
   depth assumption and preserves the exact conclusion.
4. PASS: Searched the repository under completion and finite-etale lifting names,
   inspected pinned Mathlib AdicCompletion/Noetherian and LocalRing, and ran an
   independent Loogle search `IsAdicComplete, IsLocalRing`. No shorter smaller-ideal
   completeness result was found. The existing complete-base essential-surjectivity
   theorem is the needed input; a general henselian equivalence is unnecessary.
   All four new imports are proof-only and used. The report names the sole old
   proof dependency removed, def-weil-pbc-henselian-terminology. Read the unit
   sk-prop-input-spreading, including its realized fields (all empty); this changes
   only the quotient-lifting input below its steps, and bypasses no unit step.
5. PASS: Compared node JSON with the repository: only proof, proof_deps and
   proof_origin changed. Checked the three substantive input nodes against their
   Lean declarations or Mathlib match. The union of proof-step uses equals
   proof_deps; Krull intersection is supplied by Mathlib's IsHausdorff instance.
   The detailed pullback route and source attribution agree with the Lean proof.
   Re-read Stacks [0BLS](https://stacks.math.columbia.edu/tag/0BLS) complete-case
   paragraph and [0GS2](https://stacks.math.columbia.edu/tag/0GS2) complete Noetherian
   essential-surjectivity paragraph: the route is supported by both.

Changes by the second reader: appended this independent review and recorded the
actual axiom audit and additional search. No repair of Lean or DAG was needed.
One original hole closed, zero holes added, zero statements split off; this does
not claim the imported inputs' remaining holes have been proved.
