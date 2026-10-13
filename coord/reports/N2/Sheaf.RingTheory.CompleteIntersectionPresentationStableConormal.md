## What changed

Proved `Ideal.stable_conormal_of_completeIntersection_presentation` with its signature
unchanged. The global dimension identity gives regularity at every containing polynomial
prime. Local conormal bases detect coefficients of relations; maximal-localization ideal
membership then gives a global basis for J/J². Base change that basis and compose with
the localized stable comparison, joining the two finite free factors.

Added `Sheaf.RingTheory.PrincipalLocalizationConormalAtPrimeBaseChange`, a fully proved
comparison theorem without complete-intersection, equation-count or dimension assumptions.
It uses the existing `Algebra.Extension.conormalModule_principalLocalization` and Mathlib
quotient tensors, tensor cancellation, product and finite-power base change, and the
module-localization universal property. No new definition or existing interface changed.
All new helper lemmas are private and proved. Their coefficient-detection argument follows
Tag 00SV (3), using the existing regular-sequence conormal theorem, and was adapted from
the proved private helpers of RelativeGlobalCompleteIntersectionConormalFree.

Both delivered modules compile without warnings via lcompile.py. Sources read: Stacks
Tags 00SC (last paragraph), 00S6, and 00SV (3). Checked empty equation and variable
families: finite products, sums and basis constructors cover these uniformly. J=top is
excluded by the actual prime q and the map Q/J → S_q; no nontriviality hypothesis was added.
The localization lift uses exactly hg, and the additive dimension calculation uses htm.

## Proved and sorry left

Closed the sole original hole:
`Ideal.stable_conormal_of_completeIntersection_presentation`
(node `lem-weil-pbc-complete-intersection-presentation-stable-conormal`).

Also proved the new theorem `Ideal.principalLocalization_conormal_atPrime_baseChange`
(node `lem-weil-pbc-principal-localization-conormal-at-prime-base-change`).
No sorry remains in either delivered module. Holes closed: 1; holes added: 0;
holes split off: 0. The proof still depends on the existing named theorem
`Algebra.Extension.conormalModule_principalLocalization`, which has sorry in the baseline;
that dependency is not claimed to be closed by this delivery.

## No longer needed

Removed proof import `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso` and the dependency
`lem-weil-pbc-localization-prime-residue-field-iso`: the constructed localization lift and
tensor cancellation replace the explicit prime correspondence and iterated-local-ring maps.
Removed `Mathlib.Algebra.Module.LocalizedModule.Exact` and the dependency
`lem-weil-pbc-localization-module-exact`: quotient tensors replace localization of exact
sequences. These nodes are no longer used by this proof; other library users may retain them.

`Sheaf.RingTheory.ConormalModulePrincipalLocalization` is now imported by the new comparison
module rather than directly by the assigned module; it remains needed, not pruned.
`Sheaf.RingTheory.GlobalCompleteIntersectionLocalRegularSequence` and
`Sheaf.RingTheory.RegularSequenceConormal` remain needed. No public import was removed.
The old proof-only definition dependencies def-weil-affine-spectrum,
def-kun-topological-krull-dimension, def-weil-pbc-regular-sequence,
def-weil-pbc-module-localization, def-weil-pbc-localization-at-prime, and
def-weil-pbc-module-localization-away need no separate direct proof dependency: they remain
in statement dependencies or are provided by the retained lemmas and the new comparison.

## Where the brief, the DAG or earlier work was wrong

No statement or source error found. The original plan asked for explicit localization of
ideal squares and a prime-correspondence transport, but these are unnecessary here.
Global coefficient detection produces a global conormal basis from the specified local
regularity theorem, allowing the remainder to use tensor base change directly.
The fixed unit sk-thm-p1 and every node realizing its statement or steps are unaffected.
The local checkout lacks the cited Stacks .tex files; the exact tags were read online.
LeanSearch returned Internal Server Error and is recorded as unavailable, not as no match.
Lean Finder, Loogle and grep found useful component equivalences but no assembled comparison.

## New nodes

`lem-weil-pbc-principal-localization-conormal-at-prime-base-change`: fully proved local
base change of the stable comparison of two polynomial presentations. It removes all
complete-intersection hypotheses from this part of the argument and has no new holes.
Its own dependency is the existing principal-localization conormal comparison; all
remaining operations are compositions of Mathlib equivalences. Blueprint searches for
conormal localization and conormal module found no matching blueprint nodes.
No change record is necessary: no existing signature, definition or visibility changed.

## Second reading by N2

1. Compared both delivered modules with the repository: the comparison module is new;
   the original theorem's signature is byte-for-byte unchanged (also verified with
   stage3_delivery.diff_module: statement_changed = []). There are no existing definitions
   changed and no public imports removed or visibility changes. No change record is needed.
   The revised proof docstring accurately describes the new argument.
2. Independently compiled both modules in import order with lcompile.py: clean, 15.4 s
   and 6.5 s. Inspected every helper and both public proofs: no sorry, axiom, unsafe,
   opaque, implemented_by, extern or hollow definition. A scratch #print axioms check
   of both public theorems gives only propext, Classical.choice, Quot.sound and sorryAx.
   The existing Algebra.Extension.conormalModule_principalLocalization has that same
   axiom list; the regularSequence_conormal_free and
   isRegular_localizationAtPrime_of_quotient_dimension dependencies use only the three
   allowed axioms. Thus the one original hole is closed, conditional on the explicitly
   reported existing comparison hole; this is not a claim that the import closure is closed.
3. There are no split-off holes. Read the new comparison theorem and its node against
   https://stacks.math.columbia.edu/tag/00S6 and the final paragraph of
   https://stacks.math.columbia.edu/tag/00SC. Its hypotheses match the two quotient
   presentations, g outside q and the k-algebra isomorphism. It correctly needs neither
   a complete-intersection hypothesis nor a dimension identity: it only base changes
   the stable comparison. The T-action on R is precisely the localization lift composed
   with e, and the Q/B/R and Q/T/R towers use that same map. The quotient tensor
   equivalence quotients J by J times J, hence gives J/J², not a different quotient.
   Checked n = 0, m = 0, J = 0 and empty finite powers; all displayed equivalences still
   have the stated types. J = top cannot satisfy the presentation into the nonzero local
   ring supplied by q. Independent msearch queries used Lean Finder (tensor scalar
   extension of localized ideal cotangent module stable polynomial presentation), Loogle
   (IsLocalizedModule.linearEquiv), and grep (cotangent.*[Ll]ocal|[Ll]ocal.*cotangent).
   They found component equivalences, not this assembled statement. Also searched the
   repository and upstream WeilConjectures/Comparator for the theorem names, blueprint id
   and conormal/localization keywords. No reusable exact comparison was found.
4. Read the proof from its conclusion back to its assumptions and read Tag 00SV (3),
   https://stacks.math.columbia.edu/tag/00SV. The local basis detects coefficients of a
   relation in the square; maximal-localization membership promotes this to membership
   in J. At maximal ideals not containing J the localized ideal is top, so no prime is
   omitted. Quotient coefficient lifts and span induction then construct the global basis.
   This uses the actual regular-sequence declarations, not their informal proof plans.
   Nontriviality of Q/J follows from its map to S_q; htm is used in Nat.sub_add_cancel.
   For t = 0 the conormal of the zero ideal has the empty basis. No arbitrary witness
   from an unproved existence theorem is used to define data. The private global-basis
   helpers in RelativeGlobalCompleteIntersectionConormalFree are inaccessible, and its
   public theorem requires relative-complete-intersection input, so it is not a shorter
   direct replacement. The new proof imports serve tensor base change and local ideal
   membership; the new comparison imports serve the tensor/quotient/localization maps.
   The No longer needed section accounts for every removed old proof dependency and
   distinguishes the retained transitive principal-localization comparison. Opened
   dag/units/sk-thm-p1.json: neither the item nor either removed lemma realizes one of
   its statement/steps; its realized route is retained unchanged.
5. Compared the old and new item nodes and read the entire new node. The item statement
   and statement dependencies are unchanged. Its four proof steps match nontriviality
   and dimension transfer, regularity, global coefficient detection, and base change.
   The homeomorphism dimension dependency is the recorded Mathlib match actually used.
   Its proof_deps is the union of those steps. The new node's statement and verbatim Lean
   signature match the scalar action and stable factors; its five proof steps match the
   kernel identities, conormal identifications, lift, tensor cancellation and product
   maps in Lean. Source, proof_origin, searches, creation, blueprint, chapter/unit and
   Lean records are present. No cycle or restatement of the assigned theorem is introduced:
   the new statement proves only the comparison, leaving the dimension/regularity and
   freeness argument in the assigned module.

Verdict: all five checks pass. Second reading changed only this report; no Lean or node
repair was necessary. Removed the temporary axiom-check scratch file before delivery.
