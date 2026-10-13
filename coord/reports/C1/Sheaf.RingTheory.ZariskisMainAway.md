## What changed

Replaced the obsolete duplicate Ideal-argument wrapper with a point-based conversion theorem
whose conclusion is Mathlib's `Algebra.ZariskisMainProperty R q.asIdeal`. The proof transports
the open singleton through `PrimeSpectrum.preimageHomeomorphFiber`, obtains `QuasiFiniteAt`,
and applies Mathlib's theorem. Three callers were forced to perform this conversion directly;
their public signatures are unchanged. The change record is
`coord/changes/zariskisMainProperty-duplicate.md`.

## Proved and sorry left

`Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime` is proved with no `sorry`.
No new declarations with `sorry` were added.

## No longer needed

The three callers still import the target module and now pass their `PrimeSpectrum` arguments
directly to the replacement wrapper; no public imports changed.

## Where the brief, the DAG or earlier work was wrong

The earlier wrapper duplicated Mathlib's Zariski-main property after unfolding. The point-based
interface is a shorter canonical conversion, but changing it requires the coordinated forced
adaptations recorded above.

## Second reading by C1

1. Compared the changed target module with the repository version. The old declaration is
   intentionally replaced under the explicit change record; all three adapted callers retain
   their public signatures byte-for-byte.
2. Compiled all four sandbox modules successfully with `lcompile.py --all`; no `sorry`, axioms,
   unsafe/opaque/extern declarations, or hollow definitions were added. The target theorem's
   axioms are limited to `propext`, `Classical.choice`, and `Quot.sound`.
3. The point-based statement is true: fibre-homeomorphism transport gives Mathlib's
   `QuasiFiniteAt`, and `ZariskisMainProperty.of_finiteType` gives exactly the integral-closure
   element and bijective awayMap after unfolding. It is strictly more canonical than the old
   duplicate wrapper; the semantic conclusion is unchanged.
4. The direct Mathlib route is shortest. The unit route is preserved: the same Mathlib theorem
   and fibre-homeomorphism step remain in the node proof; callers only inline the conversion.
5. DAG proof text, dependencies, origin, and Lean records agree with the implementation. The
   change record lists every downstream user and the forced adaptation lines.

Changed in this second reading: verified the interface change and forced adaptations, corrected
the node's Mathlib lemma reference and Lean record, and documented the coordinated change.

## New nodes

None.

## Forced adaptations

### Sheaf.Paper.IntegralClosureFiniteFibrePartLocalization
Original against changed dependencies failed:
```
/tmp/forced-adaptation-yx74k4cy/lean/Sheaf/Paper/IntegralClosureFiniteFibrePartLocalization.lean:128:67: error: Application type mismatch: The argument
  p.asIdeal
has type
  Ideal B
but is expected to have type
  PrimeSpectrum B
in the application
  Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime A B p.asIdeal

(with the modules compiled into /tmp/forced-adaptation-yx74k4cy/.lbuild) [6.9 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.RingTheory.QuasiFiniteAtFiniteSubalgebraAway
Original against changed dependencies failed:
```
/tmp/forced-adaptation-mdptrdc2/lean/Sheaf/RingTheory/QuasiFiniteAtFiniteSubalgebraAway.lean:56:53: error: Application type mismatch: The argument
  q.asIdeal
has type
  Ideal S
but is expected to have type
  PrimeSpectrum S
in the application
  zariskisMainProperty_of_isQuasiFiniteAtPrime R S q.asIdeal

(with the modules compiled into /tmp/forced-adaptation-mdptrdc2/.lbuild) [2.4 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.RingTheory.QuasiFiniteLocalDimension
Original against changed dependencies failed:
```
/tmp/forced-adaptation-tb0z8c7s/lean/Sheaf/RingTheory/QuasiFiniteLocalDimension.lean:53:53: error: Application type mismatch: The argument
  q.asIdeal
has type
  Ideal S
but is expected to have type
  PrimeSpectrum S
in the application
  zariskisMainProperty_of_isQuasiFiniteAtPrime R S q.asIdeal

(with the modules compiled into /tmp/forced-adaptation-tb0z8c7s/.lbuild) [3.2 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
