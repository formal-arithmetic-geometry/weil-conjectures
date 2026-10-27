## What changed

This is a partial proof delivery. The original arbitrary-field declaration
`sfQcqsCompactSupport_torsion_input_ext` and its existing dispute annotation are
preserved verbatim, including its remaining `sorry`.

In the item module, proved
`sfQcqsCompactSupport_torsion_input_ext_of_finite_shifted_hom`: torsion-input
agreement implies equality when every shifted Hom into a restricted reduction of
an output is finite. The new general theorem
`derivedComplete_finiteReduction_ext` in
`Sheaf.Paper.DerivedCompleteFiniteReductionDetection` constructs the
homotopy-limit witness from the actual derived-completeness triangle and applies
the finite Mittag-Leffler Milnor bijection. The previously proved reduction-equality equivalence supplies
the componentwise hypotheses.

Added `Sheaf.Paper.IntegralReductionShiftedHomFiniteAlgClosed`, proving
`integralReduction_shiftedHom_finite_algClosed` for finite-type quasi-compact
schemes over any algebraically closed field. The existing private
`etale_hom_finite` proof already has this generality. The new module transports
that result through the finite-ring comparison and scalar adjunction. The
auxiliary finite-field datum in the Tor lemmas is constructed independently of
the geometric base; its prime is chosen larger than l. No geometric finite-field
hypothesis or separatedness assumption is introduced.

Finally proved `sfQcqsCompactSupport_torsion_input_ext_of_isAlgClosed` in the
item module, by the finite-Hom criterion, the new finiteness theorem and the
already established compact-support comparison isomorphism. This closes an
actual special case, without replacing or weakening the assigned statement.

New imports in the item are private proof imports of the two new modules.
The complete-reduction helper module privately imports the adopted Milnor module. No existing signature, definition, public attribute or public import changes.
The helper module uses the local sheafification instances and local
irreducibility settings of the existing integral mapping-limit proof. These
settings are local and do not affect importers. The helper compiles independently;
separating it avoids a universe-inference conflict when its proof is elaborated
under the much larger compact-support imports.
No shared source-library file changes.

## Proved and sorry left

Original holes closed: 0 of 1. New holes: 0. Split-off holes: 0.

New completely proved public declarations:

- `WeilConjectures.derivedComplete_finiteReduction_ext`
  (`lem-sf-derived-complete-finite-reduction-detection`).

- `WeilConjectures.sfQcqsCompactSupport_torsion_input_ext_of_finite_shifted_hom`
  (`lem-qcqs-compact-support-torsion-input-finite-hom`).
- `WeilConjectures.integralReduction_shiftedHom_finite_algClosed`
  (`lem-sf-integral-reduction-shifted-hom-finite-alg-closed`).
- `WeilConjectures.sfQcqsCompactSupport_torsion_input_ext_of_isAlgClosed`
  (`lem-qcqs-compact-support-torsion-input-alg-closed`).

The new private Roos-triangle helper is proved, with no holes. The original private helpers
and reduction-equality equivalence remain proved.

The sole remaining hole is
`WeilConjectures.sfQcqsCompactSupport_torsion_input_ext`
(`lem-qcqs-compact-support-torsion-input-detection`). Its arbitrary-field
hypotheses do not include either algebraic closedness or finite shifted Hom.
The new results do not assert otherwise.

The argument covers n = 0 (exponent one), zero objects and empty schemes. It
uses the actual scalar adjunction and actual completeness triangle, rather than
inferring faithfulness of finite evaluation on all derived morphisms.

## No longer needed

None. No existing import, module, declaration or dependency is withdrawn.
The original general proof dependencies and unit route are retained because the
arbitrary-field hole remains. The added nodes record only the proved criterion
and special case, not a replacement for that unresolved obligation.

## Where the brief, the DAG or earlier work was wrong

The existing disputed step remains unresolved: termwise finite evaluation does
not by itself prove equality of arbitrary maps in the derived category of
towers. The Milnor argument supplies injectivity under its precise finite
shifted-Hom hypothesis. The finite-field shifted-Hom statement cannot simply be
applied to an arbitrary base field.

A useful stronger existing proof was available: the private `etale_hom_finite`
lemma in `CompactSupportTermHomFinite` accepts any algebraically closed field,
even though that module's public geometric statement is narrower. Reusing this
proof gives the algebraically closed case above. This is not claimed to settle
the original arbitrary-field statement or remove its dispute.

## New nodes

`lem-sf-derived-complete-finite-reduction-detection` records the proved generic
complete-object reduction-detection theorem in its own module. The hypotheses
are exactly completeness and finiteness of the relevant shifted Hom sets. It
introduces no geometric assumptions and no proof hole.

`lem-qcqs-compact-support-torsion-input-finite-hom` records the proved Milnor
criterion in the item module. It isolates a sufficient hypothesis and supplies
all categorical glue; it introduces no new obligation.

`lem-sf-integral-reduction-shifted-hom-finite-alg-closed` records the proved
shifted-Hom finiteness theorem in the new module. Its proof dependencies are the
existing residue-Tor, triangulated-closure, finite-ring comparison, Tor
reflection, finite-type finiteness and scalar-adjunction declarations.

`lem-qcqs-compact-support-torsion-input-alg-closed` records the proved
algebraically closed special case in the item module. It combines the preceding
two results with the existing normalized compact-support isomorphism.

No change record is needed: existing statements, definitions and public imports
are unchanged. The original node records these additional formalized parts
without asserting that its general proof is complete.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
