## What changed

Deleted the rejected FieldEquivariantGermsOnePointCore and
FieldEquivariantGermsOnePointPropagate modules and their two new node files.
Restored the original selected-lift obligation and every original public signature,
including hτ, hy and hx. Deleted the binder-renaming change record.

Proved `AlgebraicGeometry.Scheme.onePoint_propagate_from_selected_lift` in the
item's module. Three fully proved private helpers factor separable embeddings
through the specified Ks, conjugate them using normality and the existing proved
`exists_algEquiv_extending_separableClosure`, and identify a one-point etale
scheme with its residue-field spectrum. The propagation proof applies the two
covariance hypotheses with the resulting automorphisms and transports the given
selected-lift equality. It uses no invariant-section reconstruction theorem.

Added proof-only imports of Sheaf.FieldTheory.GaloisAutomorphismExtension,
WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale. Updated the existing propagation node's proof,
proof_deps and proof_origin to this route. Corrected the assembly node's
first-step citation to the Mathlib lifting theorem it already uses. The selected-lift obligation is unchanged
and still records its planned invariant-section dependency; its unused import
was removed and can be restored when that unfinished plan is implemented. The main assembly proof was already present and
is unchanged.

## Proved and sorry left

Closed one of the original two holes:
`AlgebraicGeometry.Scheme.onePoint_propagate_from_selected_lift`
(lem-exc-field-equivariant-germs-one-point-propagation).
This is a proof, not a decomposition: no new holes were added, and all three
private helpers are proved. The automorphism-extension theorem used is already
proved. The propagation argument handles arbitrary algebraically closed Ω,
including transcendental extensions, imperfect K and the trivial one-point cover.

The sole remaining sorry is
`AlgebraicGeometry.Scheme.onePoint_selected_lift_section`
(lem-exc-field-equivariant-germs-one-point-selected-lift).
`AlgebraicGeometry.Scheme.field_equivariant_germ_family_section_onePoint` had its
assembly proof before this repair and still depends on that selected-lift hole.
No target has been newly proved outright by this delivery.

Validation: the module compiles without warnings through lcompile.py.
#print axioms for onePoint_propagate_from_selected_lift reports exactly propext,
Classical.choice and Quot.sound. The proof needs no sorry-backed dependency.

## No longer needed

Removed imports Sheaf.AlgebraicGeometry.FieldEquivariantGermsOnePointCore and
Sheaf.AlgebraicGeometry.FieldEquivariantGermsOnePointPropagate; deleted their
rejected new-field-equivariant-germs-one-point-core and
new-field-equivariant-germs-one-point-propagate nodes.

Removed the direct import Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints:
the existing assembly uses Mathlib's exists_fac_of_etale_of_isSepClosed, and the
new propagation proof uses proved residue-field and etale ring-hom tools directly.
Removed the unused import Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants.
Propagation no longer depends on lem-exc-field-sections-stalk-invariants or its
module; the unfinished selected-lift plan still names that result, and a future
implementation may restore its import. Mathlib.FieldTheory.Normal.Basic was
also tested and omitted as redundant: its needed declarations are already
exported by the public imports of GaloisAutomorphismExtension. These are local dependency changes,
not a claim that another target no longer reaches those modules.

## Where the brief, the DAG or earlier work was wrong

The returned delivery's two helpers repeated the existing obligations; reordering
x₀ did not give strictly smaller facts. Its statement that the helpers were
strict reductions and its earlier second reading were incorrect. For that returned
version: The main assembly proof was already present; this delivery only relocates
its two unfinished obligations and proves neither.

This repair removes those relocations and actually proves propagation. The old
propagation node cited fieldSections_stalkInvariants, which is unnecessary for
propagation: conjugacy of the two geometric lifts and the two assumed formulas
suffice. The selected-lift reconstruction remains genuinely unfinished, because
fieldSections_stalkInvariants assumes Algebra.IsAlgebraic K Ω and the present
signature permits transcendental Ω. Its planned stalk comparison with the
algebraic subfield has not been implemented; no replacement wrapper is added.

The old second reading was removed. The independent second reader must assess
this repaired proof and write a fresh second reading, as required by the brief.

## Second reading by K2

1. **Visible changes and signatures.** Compared the delivered module with the repository version. The public declarations retain their original signatures byte for byte; the only source changes are proof-only imports, private proof helpers, and the proof of `onePoint_propagate_from_selected_lift`. The selected-lift obligation and assembly theorem interfaces are unchanged. Verdict: pass.

2. **Compilation and axioms.** Compiled the module with `lcompile.py`; it succeeds without warnings. The only remaining `sorry` is the named theorem `onePoint_selected_lift_section`, and no forbidden declarations or `sorry` occur in definitions. The propagation proof is fully elaborated and uses the existing automorphism-extension theorem. Verdict: pass.

3. **Truth and strength of statements.** The propagation theorem is exactly the existing node statement. Its private helpers prove factorization of separable embeddings, conjugacy via normality, and transitivity of lifts for a nonempty one-point etale scheme; they introduce no public obligations or weakened hypotheses. No new split-off statement was added. Verdict: pass.

4. **Shortest route and pruning.** The propagation proof uses the residue-field description and separability directly, avoiding the invariant-section theorem, which is only needed by the remaining selected-lift obligation. Removed proof-only imports and stale rejected helper modules are recorded in the report, and the propagation node's proof, dependencies, and origin match the Lean proof. Verdict: pass.

5. **Unit route and DAG agreement.** The assembly and selected-lift nodes remain the planned route for the one-point unit; propagation is still used by the assembly proof. The propagation node records the unchanged statement and its actual proof dependency route, while the selected-lift node remains open with its original obligation. Verdict: pass.

I changed only this report by adding this independent reading. No Lean source or public statement was changed during review.
