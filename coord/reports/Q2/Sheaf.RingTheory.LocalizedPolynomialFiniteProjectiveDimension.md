## What changed

Proved `ModuleCat.localizedPolynomial_finiteProjectiveDimension_of_finiteTor`, with its
signature unchanged, by taking the explicit bound `d + n`. Added two proof-only imports:
`Sheaf.RingTheory.LocalizedPolynomialTorBound` transfers the base Tor bound to the localized
polynomial ring, and `Sheaf.RingTheory.FiniteProjectiveDimensionOfTorBound` proves the
finite-Noetherian Tor-to-projective conversion by induction. The original module also imports
Mathlib's polynomial Noetherianity and localization Noetherianity for instance synthesis.

The generic conversion is proved in Lean, with no new holes: at zero it applies the existing
flat Tor ideal criterion, then Mathlib's finite-presentation projectivity theorem; at a successor
it chooses a finite free presentation, shifts Tor to the finite kernel using the existing
free-presentation Tor shift, applies induction, and uses Mathlib's short-exact Ext bound.

## Proved and sorry left

Closed one original hole:
`ModuleCat.localizedPolynomial_finiteProjectiveDimension_of_finiteTor`.
Also proved the new generic theorem
`ModuleCat.finite_hasProjectiveDimensionLE_of_tor_bound`
(node `lem-pc-finite-projective-dimension-of-tor-bound`).

Added one hole:
`ModuleCat.localizedPolynomial_tor_bound_of_base_tor_bound`
(node `lem-pc-localized-polynomial-tor-bound`). Its conclusion is the Tor vanishing bound over
the localized ring, without any projective-dimension conclusion. Thus the delivery is a
one-for-one decomposition of the original hole, with its syzygy/Ext conversion proved.
Existing open dependencies of the flat Tor criterion remain as before.

Checked edge cases: d=0 uses flatness; the induction has no nonzero-module assumption;
n=0 keeps the bound d. The base zero ring has no prime p, so that case is vacuous. Stacks
Tag 068X was read online and includes zero fibres; its amplitude [-d-n,0] has the displayed
Tor indexing. Stacks Tag 058R was read for the finitely presented flat/projective equivalence.

## No longer needed

No original imports or modules are pruned. The old proof dependencies
`def-weil-pbc-tor-modules`, `def-pc-ext`, and
`def-weil-pbc-finite-global-dimension` are no longer proof dependencies of the item;
they remain statement dependencies. Replaced the overly broad
`Mathlib.RingTheory.LocalProperties.ProjectiveDimension` import in the new Tor-bound module
with the signature imports `Mathlib.RingTheory.Noetherian.Defs`,
`Mathlib.RingTheory.Spectrum.Prime.Defs`, `Mathlib.RingTheory.Localization.AtPrime.Basic`
`Mathlib.Algebra.Category.ModuleCat.Abelian` and
`Mathlib.Algebra.Category.ModuleCat.Projective`. The route retains both the transfer of Tor amplitude
and the finite-projective shortening in the original plan. The new generic lemma uses the
existing tool modules `Sheaf.Algebra.FlatTorIdealCriterion` and
`Sheaf.Algebra.TorDimensionShiftFree` (nodes
`lem-weil-pbc-flat-tor-ideal-criterion` and `lem-weil-pbc-tor-dimension-shift-free`).

## Where the brief, the DAG or earlier work was wrong

The original proof's listed dependencies only define Tor, Ext and projective dimension;
they do not state the substantive amplitude-transfer step. The new transfer theorem isolates
exactly that step. The generic finite-Noetherian conversion is implemented using existing
library tool lemmas and Mathlib. The unit route is unchanged.

An initial experimental auxiliary statement `projectiveDimension M ≠ ⊤` was equivalent to
the original conclusion and was discarded before delivery; neither its module nor its node
is included.

## New nodes

`lem-pc-localized-polynomial-tor-bound`: base Tor vanishing above d gives localized-ring Tor
vanishing above d+n, the amplitude-transfer part of Stacks Tag 068X. Module:
`Sheaf.RingTheory.LocalizedPolynomialTorBound`.

`lem-pc-finite-projective-dimension-of-tor-bound`: a finite module over a Noetherian ring
has projective dimension at most its Tor bound. Its proof is complete from existing tool
lemmas. Module: `Sheaf.RingTheory.FiniteProjectiveDimensionOfTorBound`.

## Second reading by Q2

1. Compared every delivered existing module and node with the repository using diff.
   The existing theorem signature, visibility, universe and docstring are byte-identical;
   only its proof and four proof-only imports change. No definitions or target statements
   change, and no change record is required. The two other modules are new.
2. Compiled all three modules in import order with lcompile.py. Reviewed the induction:
   the zero case specializes the hypothesis to ideal quotients at degree one, uses
   finite presentation over a Noetherian ring, and applies flat-to-projective. The successor
   uses an actual finite free presentation, its finite kernel, the Tor shift only at
   positive degrees, and the short-exact projective-dimension equivalence. No object is
   defined using an unproved existence theorem. The only new sorry is the named transfer
   theorem. No forbidden declarations or proof bypasses occur. A scratch axiom probe
   checks all three delivered declarations: the generic conversion uses only propext,
   Classical.choice and Quot.sound; the transfer and original item additionally use
   sorryAx from the named transfer hole. No inherited hole is needed by the conversion.
3. Read Stacks Tag 068X directly: its flat-map, bounded-fibre-global-dimension,
   pseudo-coherence and base-amplitude hypotheses yield amplitude [a-n,b]. Here
   a=-d and b=0, so the claimed d+n bound has the correct indexing. The fibres are
   localizations of polynomial rings over residue fields, including zero fibres.
   For n=0 this is localization, for d=0 it bounds relative dimension by n, and for
   the zero module all Tor groups vanish. The remaining hole is just amplitude transfer;
   the finite-Noetherian Tor-to-Ext conversion is separately proved by induction and is
   not a renamed existential projective-dimension conclusion. Its full proof and node
   are present. Fresh searches with leanfinder (relative weak dimension), loogle
   (flat-to-projective), grep (Tor/projective dimension/change of rings), and rg in
   Sheaf and the upstream Algebra and RingTheory sources found no existing transfer
   theorem or generic conversion to replace these declarations.
4. The proof uses the shortest available conversion via existing flatness and Tor-shift
   lemmas and Mathlib's finite-presentation and short-exact results. Polynomial.Basic
   and Localization.Submodule supply the required Noetherian instances. New proof-only
   imports are plain imports. Replaced the public projective-dimension import
   in the new transfer module with the narrower Noetherian, prime-spectrum and localization signature imports. No original module is pruned; listed all old proof_deps
   replaced by the two new lemmas above. Read sk-thm-picard-duality.json: this auxiliary
   item realizes none of its statement or steps, and its realized route is unchanged.
5. Checked new node fields, verbatim Lean statements, sources, blueprint ancestry and
   proof_deps. The main node names precisely the transfer and conversion it applies.
   Corrected the conversion node's per-step uses: flatness belongs to the zero step,
   Tor shifting to the successor step. The union of proof_deps remains unchanged.

Second reading changes: narrowed one import in the new transfer module, corrected
its author credit to Q2, corrected per-step DAG citations, and completed the pruning report.
No mathematical statement or proof required repair. This is a one-for-one decomposition,
not a net hole reduction; the generic conversion has no local holes.
