## What changed

Corrected Algebra.exists_smoothAtPrime_differential_data to allow the further
principal shrink required by Tag 07C6, carrying smoothness and the prescribed
conormal basis onto the new open. Proved its combining argument from the existing
smooth_localization_conormal_split and two new, fully proved generic lemmas.
Adapted only the final proof lines of SmoothAtPrimeFreeConormalBasis to use the
new witness; its signature and visibility are unchanged.

## Proved and sorry left

Closed the corrected item's sole hole:
Algebra.exists_smoothAtPrime_differential_data
(lem-weil-pbc-smooth-at-prime-free-conormal-basis-differential-data).
This is a correction of a false intermediate statement, not a proof of its old
fixed-open assertion. No sorry remains in any delivered module; no hole was added
or split off. Both new lemmas are proved:
Algebra.exists_smooth_split_complement_shrink and
Module.Basis.exists_prescribed_basis_away_mul.
The unchanged parent remains proved from named dependencies.

The proof still uses the existing holed theorem
Algebra.smooth_localization_conormal_split
(lem-weil-pbc-smooth-localization-conormal-split), which is not delivered here.
The parent still uses Algebra.exists_smoothAtPrime_conormal_data
(lem-weil-pbc-smooth-at-prime-free-conormal-basis-conormal-data), also unchanged.
These imported holes remain future items; this delivery does not claim an
axiom-free completion of the entire target closure.

## No longer needed

Removed the item's proof import Sheaf.RingTheory.SmoothAtPrimeConormalData and
its dependency node lem-weil-pbc-smooth-at-prime-free-conormal-basis-conormal-data
from this item's proof_deps. That module remains needed by the parent, so this
is an import-edge pruning, not a claim of global module pruning.
All other original public imports remain needed by the statement or its public
interface. The new helpers use only Mathlib; no extra Sheaf dependency is needed
for finite projectivity, rank additivity, local freeness, spreading, or localization
of differentials. No blueprint unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous decomposition omitted the further shrink, incorrectly replacing
stable freeness by freeness on the original open. Its docstring said to take a
common shrink, but its conclusion fixed a. The smooth real two-sphere hypersurface
is a counterexample, detailed in the change record. The parent source plan was
correct and its unchanged statement is recovered by the forced adaptation.
The node's old dependency on conormal-data did not help prove the fixed-open
conclusion; the actual needed input is the split conormal sequence.

LeanSearch was unavailable with an Internal Server Error. Lean Finder, Loogle,
and local Mathlib/source searches were used; the service failure is recorded
without claiming a no-match verdict. The cited literature file is not present on
this machine, so the exact Stacks Tag 07C6 and Tag 0GWM pages were read online.

## New nodes

lem-weil-pbc-smooth-split-complement-shrink:
Sheaf.RingTheory.SmoothSplitComplementShrink. This proved generic lemma computes
the complementary rank over the local ring, spreads a basis using Mathlib, clears
the denominator, and identifies the resulting differential module on D(a*t).

lem-weil-pbc-prescribed-basis-further-localization:
Sheaf.RingTheory.PrescribedBasisFurtherLocalization. This proved generic lemma
base changes any prescribed basis from D(a) to D(a*t), including the exact
basis-vector equalities. No finite or projective hypotheses are needed.

Change record: coord/changes/smoothAtPrimeDifferentialData-common-shrink.md.

## Forced adaptations

Sheaf.RingTheory.SmoothAtPrimeFreeConormalBasis (unclaimed): the original final
exact expects a basis on the initial open, whereas the corrected theorem now
returns an existential new open with smoothness, conormal basis and differential
basis. Replace original lines 90-91 (refine/exact) by destructuring this existential
and assembling the same parent statement with a'. No other lines are adapted.
The delivery dry-run supplies the exact counterfactual compiler error below.

## Second reading by S3

1. Compared each delivered module with the repository version. Existing declaration
signatures are unchanged except for the explicitly recorded correction of
`Algebra.exists_smoothAtPrime_differential_data`; the adapted parent keeps its
signature and changes only the forced proof lines. Verdict: pass.

2. Compiled all four sandbox modules with `lcompile.py --all`; compilation succeeds.
Searched for `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, and `implemented_by`;
none occur in delivered declarations. The existing upstream sorry theorem is
outside this delivery. Verdict: pass.

3. Checked the two new helper statements against their proofs and source notes.
Both are genuine generic reductions: one spreads a complementary basis after a
principal shrink, and the other transports a prescribed localized basis. Neither
restates the item, and both are needed by the item proof. Verdict: pass.

4. Read the proof from the target downward. The corrected theorem uses the split
conormal theorem, the complementary-shrink helper, and prescribed-basis
localization; the parent uses the resulting common shrink. The removed conormal
data import is no longer used by the item. Verdict: pass; the unit route remains
through the split conormal step.

5. Checked the DAG nodes, proof dependencies, proof origins, and the change record
against the Lean declarations. The item node records the statement correction and
the helper nodes record their exact declarations and proofs. Verdict: pass.

Changed after this reading: added this review section only; no proof or statement
changes were required.

## Forced adaptations

### Sheaf.RingTheory.SmoothAtPrimeFreeConormalBasis
Original against changed dependencies failed:
```
/tmp/forced-adaptation-i7s1s2zb/lean/Sheaf/RingTheory/SmoothAtPrimeFreeConormalBasis.lean:91:2: error: Type mismatch
  exists_smoothAtPrime_differential_data R n m f a V c q ha hcard hbound hsm hb
has type
  ∃ a',
    (Ideal.Quotient.mk (Ideal.span (Set.range f))) a' ∉ q.asIdeal ∧
      Smooth R (Localization.Away ((Ideal.Quotient.mk (Ideal.span (Set.range f))) a')) ∧
        (∃ e b,
            ∀ (j : Fin c),
              b j =
                (LocalizedModule.mkLinearMap (Submonoid.powers ((Ideal.Quotient.mk (Ideal.span (Set.range f))) a'))
                    (Ideal.span (Set.range f)).Cotangent)
                  ((Ideal.span (Set.range f)).toCotangent ⟨f ↑(e j), ⋯⟩)) ∧
          Nonempty
            (Module.Basis (Fin (n - c)) (Localization.Away ((Ideal.Quotient.mk (Ideal.span (Set.range f))) a'))
              Ω[Localization.Away ((Ideal.Quotient.mk (Ideal.span (Set.range f))) a')⁄R])
but is expected to have type
  Nonempty
    (Module.Basis (Fin (n - c)) (Localization.Away ((Ideal.Quotient.mk (Ideal.span (Set.range f))) a))
      Ω[Localization.Away ((Ideal.Quotient.mk (Ideal.span (Set.range f))) a)⁄R])

(with the modules compiled into /tmp/forced-adaptation-i7s1s2zb/.lbuild) [1.9 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
