## What changed

Restored `Sheaf.AlgebraicGeometry.FiniteDiscreteCtfOrigin` from its recorded quarantine
archive. Preserved the public theorem `AlgebraicGeometry.ProEtale.finiteDiscreteCtfOrigin`,
its full signature, and all public imports. The archived source has zero holes.

Replaced the private fixed-scalar devissage helper by the reverse implication of the
existing `finiteComparisonGenerators_identification`: take an inverse image under the
exact derived coefficient equivalence, transport the internal hypothesis, obtain the
etale antecedent, enlarge its Tor interval to its ordered hull, and compose the two
comparison isomorphisms. The DAG proof and dependencies now describe this shorter proof.
This is the same finite-Tor comparison route required by the compactness unit.

## Proved and sorry left

`AlgebraicGeometry.ProEtale.finiteDiscreteCtfOrigin` has a complete assembly proof.
The quarantined module started with zero `sorry`s; this delivery closes 0 of 0 holes,
adds 0 holes, and leaves 0 holes in the module. No new theorem is split off.

The proof uses the existing named dependency
`AlgebraicGeometry.ProEtale.finiteComparisonGenerators_identification`
(node `lem-ctf-finite-comparison-generators`), which still contains its own `sorry` in
`Sheaf.Paper.FiniteComparisonLocalizing`. That existing obligation is unchanged; this is
not a claim that the transitive proof is axiom-free. The archived route already depended
on the same obligation through `finiteDiscreteCtfRealization`.

## No longer needed

Removed proof imports `Sheaf.AlgebraicGeometry.FiniteDiscreteCtfRealization`,
`import all Sheaf.Paper.ProEtaleConstructibleOrigin`, and
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison`.
Removed the proved private helper `fixedCtfOrigin`, which repeated descent after
coefficient reflection.

The item no longer directly needs nodes `lem-finite-discrete-ctf-realization`,
`lem-sf-proetale-constructible-origin`, or `lem-sf-comparison-tor-amplitude`.
No module is withdrawn, and no claim is made that these nodes are globally unnecessary:
other consumers may still use them, including through the existing generator comparison.
All three public imports and the proof import `Sheaf.Paper.ConstantModelTorAmplitude`
are retained for the unchanged interface and isomorphism transport. Added the proof import
`WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel` for its proved
`hasTorAmplitudeIn_iff_torAmplitudeIn` conversion API.

## Where the brief, the DAG or earlier work was wrong

The current rework row records a reverted cluster restoration, rather than an
unproved theorem. Its quarantine archive remains the authoritative source; absence from
`lean/` does not authorize withdrawal. The archived file compiles against the current
published build in 8.4 seconds with zero holes. No current B2 return names any other
repair. The substantive simplification here avoids accessing another module's private
helper and redundant reflection/descent; no definition or theorem statement changes.

Validation: the final restored module compiles cleanly through `lcompile.py` in 3.5
seconds. The first direct tensor conversion timed out; intermediate compiles isolated
it to interval conversion, and using the existing conversion lemma avoids expanding the
derived tensor definition. The full theorem signature and public imports were checked
byte-for-byte against the quarantine archive. The file has zero holes, no temporary
profiling options, and no lines over 100 characters.

The shorter route uses `lem-ctf-finite-comparison-generators` as the existing bounded
finite-Tor comparison tool. This directly realizes the finite comparison step of
`sk-prop-ctf-finite-compact`; it does not replace the unit's route.

Change record: `coord/changes/finite-discrete-ctf-origin-restoration.md`.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
