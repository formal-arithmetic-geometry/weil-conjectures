## What changed

Repair of returned delivery dc5b522d25: removed the unnecessary
`set_option warn.sorry false` at former line 28. The landing audit reported that
option token as `<unattributed:28:984>`. There is no hole at that location, and
removing the option eliminates that spurious hole token. Also removed the
development-only profiler and unscoped heartbeat options retained from the
interrupted debugging session. The resumed supported single-file compile passed without
warnings in 19.0 seconds. A scratch axiom check reports only `propext`,
`Classical.choice`, and `Quot.sound`. The retained proof, theorem signature, and node route
are unchanged by this repair. The option changes are recorded in
`coord/changes/scheme-frobenius-options.md`. A fresh supported single-file compile
on this resumption also passed in 15.0 seconds without warnings. The change record
identifies current consumer holders; all consumers retain the same declarations
and need no adaptation.

Proved `WeilConjectures.FiniteFieldDatum.relativeFrobenius_isFinite_isRadicial`
with its signature unchanged. The proof verifies the source library's `IsFrobenius`
predicate for the explicit model endomorphism, then applies the already proved
`IsFrobenius.isFinite_of_isPullback` and
`IsFrobenius.isUniversalHomeomorphism_of_isPullback` to the geometric-fibre square.
The required compatibility equations are precisely `relativeFrobenius_projections`.
Taking `toUniversallyInjective` finishes radiciality.

The predicate verification is actual Lean: on every open, naturality is `map_pow`;
on an affine test scheme, `GammaSpecIso_inv_naturality` and preservation of powers
identify the explicit iterate with the supplied cardinality-power ring map.
The datum's cardinality equations identify `Nat.card D.k₀` with `D.p ^ D.a`.
No additional hypotheses, definitions, intermediate statements or axioms are introduced.
The proof also covers empty and nonreduced schemes, and does not require separatedness.

Replaced the five old proof imports with the one source Frobenius morphism module.
Public imports stay unchanged. Updated the node's proof, proof dependencies and
proof origin to the implementation. Its unit record has no realized statement or
proof step on this item; the unit route is preserved.

Searches used `msearch.py` with Lean Finder, Loogle and grep, and ripgrep on both
library roots. Mathlib supplies generic stability results, not the entire theorem.
The source-library candidates already recorded on the node do supply the desired
conclusion once their predicate is verified.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.FiniteFieldDatum.relativeFrobenius_isFinite_isRadicial`
(node `lem-trf-scheme-frobenius-finite-radicial`).

Holes remaining in the item: 0. Holes added: 0. Split-offs: 0.
No other module is changed.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.RelativeFrobeniusIntegralUniversalHomeomorphism`.
- `Mathlib.FieldTheory.Finite.Basic`.
- `Sheaf.AlgebraicGeometry.RelativeFrobeniusFinite`.
- `WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`.

The two Sheaf theorem modules are not needed by this proof. In particular,
`lem-trf-relative-frobenius-finite` and
`lem-trf-relative-frobenius-universal-homeomorphism` are removed from the node's
proof dependencies: the closed source results directly give the finite-field
specialization and its scalar extension, without factoring through twists.
`lem-weil-finite-field-pow-card` is no longer a separate proof dependency: the
model and its projection identities are already constructed and proved, and the
new local calculation only uses the datum's cardinality equalities.
The other three removed imports are redundant with the retained statement and
source imports. The actual absolute-Frobenius construction and pullback notions
remain used; the auxiliary base-change convention declarations are not needed.
No files are withdrawn; this prunes requirements of this item, not other consumers.

## Where the brief, the DAG or earlier work was wrong

The original plan expanded general relative Frobenius iteration even though its
own recorded source-library candidates prove the needed finite-field case.
The candidates' extra predicate is verified directly from the existing explicit
construction; it does not require any additional theorem or hole.
No mathematical statement was corrected.
The returned unattributed-hole diagnostic points to the warning option, which
has now been removed; no anonymous or definition-level hole remains.

One resumed clean compile timed out; the diagnostic scratch compile completed
type checking in 27 seconds and the next clean compile passed in 19.0 seconds.
No tool or timeout setting was changed. The only previous pushed head was the
returned dc5b522d25; no interrupted delivery process was running when resuming.

## Second reading by V7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
