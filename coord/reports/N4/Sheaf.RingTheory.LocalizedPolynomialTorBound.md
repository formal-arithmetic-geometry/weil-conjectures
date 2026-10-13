## What changed

Proved `ModuleCat.localizedPolynomial_tor_bound_of_base_tor_bound` from the polynomial
extension bound and the existing proved localization comparison
`ModuleCat.isZero_tor_of_restrictScalars_localization`. The composite scalar restriction
in the hypothesis is definitionally the successive scalar restriction used by the proof.
The original signature is unchanged. The second reader updated the docstring to describe
the polynomial-bound and localization proof now used. Added two proof-only imports:
`Sheaf.RingTheory.PolynomialTorBound` and `Sheaf.RingTheory.TorVanishingLocalizedBase`.
Updated the parent DAG route to agree with these imports.

## Proved and sorry left

Closed the original hole `ModuleCat.localizedPolynomial_tor_bound_of_base_tor_bound`
(node `lem-pc-localized-polynomial-tor-bound`). Added one hole:
`ModuleCat.polynomial_tor_bound_of_base_tor_bound` in `Sheaf.RingTheory.PolynomialTorBound`
(node `lem-pc-polynomial-tor-bound`). This is a decomposition, not a net reduction in
holes: the polynomial step remains and the localization step is now actual Lean.
There are no sorries in the item's module and no other new holes.

The new theorem is a genuine polynomial step, with no prime or localization in its
statement. It is not the original statement with its hypotheses repackaged. Unlike the
parent, it applies to arbitrary polynomial modules; this is necessary because the
restriction of the finite localized module need not be finite over the polynomial ring.
Its docstring gives the one-variable relative-resolution construction and its induction.
Edge cases checked mathematically: no variables gives restriction across the canonical
ring equivalence; d=0 uses the same long exact sequence; zero rings and zero modules
make the argument trivial. The exact-sequence argument requires no Noetherian assumption.

## No longer needed

No original imports or existing dependency nodes removed: the original proof_deps were
empty, and its public imports supply the unchanged statement. The revised route does
not require pseudo-coherent degree-zero models, residue-field fibres, fibre global
dimension, or the general perfect-complex recognition theorem of Tag 068X. These were
unnamed steps in the old plan, so there are no corresponding modules to remove here.
The new module imports no spectrum, localization or Noetherian module.

## Where the brief, the DAG or earlier work was wrong

The old node had no proof dependencies despite its non-elementary Tag 068X argument.
No usable statement in the library realizes that general argument. A simpler polynomial
relative-resolution argument plus the existing localization comparison avoids building
it. No statement or definition was changed. The unit's realized statement and steps
remain untouched (this node is below the unit).

The initial scratch projective-resolution reformulation was discarded because it merely
repackaged the whole argument. The delivery contains no such reformulation.
The new source is Weibel Theorem 4.3.7, pp. 101–102, read in the chapter PDF hosted by MIT:
https://math.mit.edu/~hrm/palestine/weibel/04-homological_dimension.pdf.
Weibel is already in literature/LIST.md's Wanted table; its exact sequence extends to the
stated Tor bound by scalar-extension comparison and the Tor long exact sequence.

## New nodes

`lem-pc-polynomial-tor-bound`, `dag/nodes/sec-picard-framework/lem-pc-polynomial-tor-bound.json`,
states only the polynomial extension part of the argument in
`lean/Sheaf/RingTheory/PolynomialTorBound.lean`. The source is Weibel Theorem 4.3.7, with its
explicit relative-resolution argument applied to Tor. LeanFinder, Loogle and local grep
found no exact library result; LeanSearch was unavailable (Internal Server Error). No change records or forced adaptations are needed.

## Second reading by N4

1. Compared both delivered modules with the repository. The only existing declaration,
   `ModuleCat.localizedPolynomial_tor_bound_of_base_tor_bound`, retains its signature byte
   for byte: commutative Noetherian A, n, prime p, finite localized M, d, universal base
   Tor vanishing, and the same universal localized vanishing above d+n. No definition,
   visibility, target, or public import changed. PolynomialTorBound is a new module.
   Verdict: pass; no change record is needed.
2. Compiled both modules in import order through lcompile.py, without errors or warnings.
   Inspected the whole code: exactly one sorry remains, in the named new polynomial
   theorem; no data definitions or forbidden declarations were added. Scratch
   `#print axioms` checks for both delivered declarations show only propext,
   Classical.choice, Quot.sound and sorryAx, as expected from the polynomial hole.
   The existing localization comparison separately prints only the three permitted
   axioms, confirming that the polynomial theorem is the remaining dependency hole.
   Verdict: pass as a decomposition, not a complete axiom-free proof.
3. Read the polynomial node and theorem hypothesis by hypothesis. It concerns arbitrary
   polynomial modules and has no localization assumption, so it supplies precisely the
   intermediate bound on the restriction of M. It is not a renamed parent statement.
   Read Weibel 4.3.7, pp. 101–102: its relative exact sequence is the stated construction.
   For i>d+1 the long exact sequence uses induced-module degrees i and i-1, both >d;
   induction applies the n-variable bound to restriction before adding one variable.
   With n=0 the coefficient ring equivalence gives the bound; with d=0 the argument
   uses degrees >=1; for the zero ring or zero module the modules vanish. These are
   mathematical edge-case checks. Fresh LeanFinder, Loogle, and grep searches with
   endomorphism/induced-module/leftDerived/flatDimension terms, and rg of both local
   library roots, found no usable replacement. Recorded the new searches in the node.
   The remaining exact-sequence and derived comparison constructions cannot be closed
   in a few minutes with the available lemmas. Verdict: true, needed, strictly a part
   of the argument, with a source and complete proof docstring.
4. Read the proof top downward: the existing proved localization comparison reduces
   the conclusion to polynomial Tor vanishing; the base hypothesis matches successive
   restriction definitionally. Both new imports are proof-only and used. The public
   imports supply statement types and Tor instances. The old proof_deps were empty,
   so there are no omitted dependencies to list as pruned. Read
   dag/units/sk-thm-picard-duality.json: this auxiliary node is not a realized unit
   statement or step; its realized fields are unchanged. Verdict: route preserved.
5. Compared the parent node with the repository: only proof, proof_deps and proof_origin
   changed. Its dependencies are exactly the polynomial and localization nodes used
   in Lean. The new node's statement and verbatim Lean signature agree; its source,
   proof, search records, creation, blueprint ancestry, chapter/unit and Lean fields
   are present. Verdict: pass.

Second-reading changes: replaced the parent's obsolete fibre/perfect-complex proof
sketch in its docstring with the actual polynomial/localization reduction; added fresh
search evidence to the polynomial node and this review. The Lean proof and all
signatures are unchanged. Closed one original hole, added one strictly intermediate
hole; net holes closed minus added is zero. No modules or dependency nodes are pruned.
