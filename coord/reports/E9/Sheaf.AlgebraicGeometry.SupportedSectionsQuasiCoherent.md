## What changed

Completed `AlgebraicGeometry.Scheme.Modules.exists_supportedSections_isQuasicoherent`
in `Sheaf.AlgebraicGeometry.SupportedSectionsQuasiCoherent`, preserving its statement and
all existing public imports. Added six proved private helpers for restriction composition,
the actual supported kernel, the finite defining ideal, the affine basic-open membership
formula, and the ideal-power equivalence. Added the proof-only import
`WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs`.

The construction takes the categorical kernel of the restriction-adjunction unit
`F → j_*(F.restrict j)` for the complementary open immersion. The given affine compactness
hypothesis makes j quasi-compact; open immersions are quasi-separated. The existing proved
qcqs pushforward theorem and quasi-coherent kernel theorem give quasi-coherence. The
sectionwise kernel API proves injectivity and the prescribed image on every open.

For an affine open, `PrimeSpectrum.isCompact_isOpen_iff_ideal` gives the finite defining
ideal after transporting its compact open complement through the affine isomorphism.
A supported section m vanishes on D(a) for every a in J. The existing compact-section
power-torsion theorem gives J contained in the radical of the cyclic annihilator of m;
`Ideal.exists_pow_le_of_le_radical_of_fg` then gives a single annihilating ideal power.
Conversely, restriction makes each a in J a unit on D(a), so the annihilating power forces
vanishing there; these opens cover the complement, and sheaf uniqueness finishes.

Updated only the item's DAG proof, proof dependencies and proof origin to this route.
The additional tools are the already proved nodes `pqf-lem-pushforward-qcoh` and
`lem-weil-pbc-quasi-coherent-module-kernel`, and the existing Mathlib leaf
`lem-weil-pbc-fg-ideal-radical-power`. They are generic tools, not replacements for a unit's
statement or proof step. The unit's `realized` record has no attachment to this node.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.Modules.exists_supportedSections_isQuasicoherent`
(node `lem-trf-supported-sections-quasi-coherent`).

Added 0 holes and 0 split-off statements. No sorry remains in the delivered module.
All six private helpers are completely proved.
The complete module compiled cleanly through `lcompile.py` in 7.1 seconds (exit 0).
A source comparison confirms that the public theorem signature is unchanged.

The argument includes empty schemes and affine opens, empty or full closed supports,
the zero defining ideal, arbitrary quasi-coherent modules (no finite-generation hypothesis
on F), and exponent zero. The basic-open cover uses all elements of J, so no nonempty
finite generating family is assumed. With J=0 the complementary open is empty; sheaf
uniqueness still applies. Unit cancellation uses a^0=1 when the exponent is zero.

## No longer needed

No existing import is removed, and no module is withdrawn or claimed globally pruned.
Removed the obsolete direct tool-use approvals for
`pqf-lem-qcoh-qcqs-section-power-extension` and
`pqf-lem-qcoh-principal-open-criterion` from the node, preserving the other entries in order.
The old direct dependency on `pqf-lem-qcoh-qcqs-section-power-extension` and
`pqf-lem-qcoh-principal-open-criterion` is replaced by the proved qcqs-pushforward and
kernel tools. Both former nodes remain used transitively by the existing source
pushforward proof, so their modules are still needed and are not candidates for deletion.
The separate positive-exponent monomial calculation is replaced by the existing
finitely generated ideal radical-power Mathlib lemma. The spectrum basis and affine
compactness dependencies are retained for the compact-open ideal and torsion steps.

## Where the brief, the DAG or earlier work was wrong

No statement, definition or source error was found. The previous five-step DAG proof and
original declaration docstring describe a valid principal-open route. The shorter complete
proof uses the original kernel route from Stacks Properties Tag 07ZP, made available by
the already proved qcqs pushforward theorem. There is no shared-interface change and no
forced adaptation of another module.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
