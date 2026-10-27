## What changed

Proved `AlgebraicGeometry.etale_normal_domain_finite_factors` with its signature unchanged.
Added private proof imports of Mathlib smooth-flatness, minimal-prime localization,
Noetherian minimal-prime finiteness, and local detection of reducedness. The existing
normality-ascent and reduced-normal decomposition theorems supply the endpoints.

Repaired the return at head `07934308444`: removed `set_option warn.sorry false`.
The landing source scanner interpreted the `sorry` component of that option name
as an unattributed hole at line 24. The option is unnecessary because the proof
has no holes. Updated the theorem docstring to describe the implemented proof.

The shorter generic-fibre argument constructs `C = FractionRing A ⊗[A] B`.
Flatness makes `B → C` injective. Minimal-prime lifting along an injective map,
followed by choosing a minimal prime below the lifted prime, puts every minimal
prime of B in the finite contraction image of the minimal primes of C.
Each product factor receives the A-algebra structure by composing its projection
with the ring equivalence and the given structure map. This upgrades that ring
equivalence to an algebra equivalence definitionally.

Updated the existing node's proof, proof_deps and proof_origin to the actual route.
Removed the obsolete localization-prime tool-use approval. No statements,
definitions, public imports, unit steps or source-library declarations changed.

Preflight treats removal of the warning option as a module command interface
change. Recorded it in `coord/changes/etale-normal-domain-warning-option.md`,
including all 22 downstream modules. No downstream adaptation is needed: the
option controls warnings and contributes no declaration, notation or instance.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.etale_normal_domain_finite_factors`
(node `lem-trf-etale-normal-domain-finite-factors`). Added 0 holes; split off 0.
No sorry remains in this delivery. The complete file compiled without warnings.
`#print axioms` confirms that the theorem depends only on `propext`,
`Classical.choice`, and `Quot.sound`; there is no transitive `sorryAx`.

## No longer needed

Removed proof import `WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso`
and its node `lem-weil-pbc-localization-prime-residue-field-iso`: contraction from
the generic fibre is handled by injective minimal-prime lifting instead.

Removed planned dependencies `lem-sc-flat-going-down`,
`lem-weil-pbc-lfp-affine-opens-finite-presentation`, and
`lem-weil-pbc-spec-map-global-sections`: tensor injectivity replaces going-down;
the affine etale dictionary already supplies algebraic finite presentation.
These are pruned only from this item's proof; no module is withdrawn and no
claim is made that other consumers no longer need these results.

## Where the brief, the DAG or earlier work was wrong

The returned unattributed hole was the option name `warn.sorry`, rather than a
proof hole. Removing the warning suppression repairs that source-scanner refusal.
No mathematical error or statement repair. The DAG and original declaration
docstring give a valid but longer proof plan. The implemented route replaces its
going-down and localization-prime steps by flat tensor injectivity and the
existing Mathlib minimal-prime lifting API (existing leaf
`lem-weil-pbc-injective-minimal-prime-lift`). This node lies below the unit level;
the unit and chapter route are unchanged. The zero-ring case is covered directly
by the decomposition theorem's empty-family conclusion. No Noetherian assumption
is added on A or B, and the theorem remains valid when B is zero.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
